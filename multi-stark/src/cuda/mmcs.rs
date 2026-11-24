use std::path::{Path, PathBuf};

use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs};
use p3_field::PrimeField64;
use p3_goldilocks::Goldilocks;
use p3_matrix::{Dimensions, Matrix, dense::RowMajorMatrix};
use p3_maybe_rayon::prelude::*;
use p3_merkle_tree::{MerkleTreeError, MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{CryptographicHasher, MerkleCap};

use super::{
    CudaLde, CudaMixedMerkleTree, mixed_lde_open_row, mixed_lde_open_row_at_height,
    mixed_lde_open_rows, mixed_lde_open_rows_at_height,
};
use crate::p3_adapter::blake3_simd;
use crate::p3_adapter::cap::{
    CapValidatingMmcs, verify_merkle_cap_len, verify_merkle_cap_len_for_log_height,
};
use crate::p3_adapter::domain_blake3::{Blake3Domain, DomainBlake3};
use crate::p3_adapter::spill::{
    MerkleDigests, STREAM_BLOCK_BYTES, SpillPackWriter, SpilledMatrix,
    build_merkle_digests_from_height_hashes,
};
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};

type DomainCompressionFunction = CompressionFunctionFromHasher<DomainBlake3, 2, 32>;
type CpuMmcs = MerkleTreeMmcs<
    Goldilocks,
    u8,
    SerializingHasher<DomainBlake3>,
    DomainCompressionFunction,
    2,
    32,
>;
type CpuData<M> = <CpuMmcs as Mmcs<Goldilocks>>::ProverData<M>;
pub(crate) type DeferredMatrix<M> = Option<(Dimensions, std::thread::JoinHandle<M>)>;
type DeferredWorker<M> = Option<std::sync::Mutex<Option<std::thread::JoinHandle<M>>>>;

#[derive(Clone, Copy)]
pub enum CudaMatrixSource<'a> {
    Resident(&'a CudaLde),
    Host(&'a RowMajorMatrix<Goldilocks>),
    Spilled(&'a SpilledMatrix),
}

#[doc(hidden)]
pub enum HybridMerkleTree {
    Device(CudaMixedMerkleTree),
    Host(MerkleDigests),
}

impl HybridMerkleTree {
    pub(crate) fn cap(&self, cap_height: usize) -> MerkleCap<Goldilocks, [u8; 32]> {
        match self {
            Self::Device(tree) => {
                assert_eq!(cap_height, 0, "device Merkle tree requires cap_height = 0");
                MerkleCap::new(vec![tree.root()])
            }
            Self::Host(digests) => digests.cap(cap_height),
        }
    }

    pub(crate) fn open_siblings(&self, index: usize, cap_height: usize) -> Vec<[u8; 32]> {
        match self {
            Self::Device(tree) => tree.open_siblings(index),
            Self::Host(digests) => digests.open_single_proof(index, cap_height),
        }
    }

    pub(crate) fn open_pruned_siblings(
        &self,
        indices: &[usize],
        cap_height: usize,
    ) -> PrunedMerklePaths<u8, 32> {
        match self {
            Self::Device(tree) => tree.open_pruned_siblings(indices),
            Self::Host(digests) => digests.open_multi_proof(indices, cap_height),
        }
    }
}

pub enum CudaMmcsData<M> {
    Cpu(CpuData<M>),
    Hybrid {
        // Drop resident LDEs before their retained host traces.
        resident: Vec<Option<CudaLde>>,
        resident_active: Vec<std::sync::atomic::AtomicBool>,
        materialize: Box<dyn Fn(&CudaLde) -> M + Send + Sync>,
        materialize_spilled: Box<dyn Fn(&SpilledMatrix) -> M + Send + Sync>,
        committed_matrices: Vec<std::sync::OnceLock<M>>,
        spilled_matrices: Vec<std::sync::OnceLock<SpilledMatrix>>,
        deferred_matrices: Vec<DeferredWorker<M>>,
        dimensions: Vec<Dimensions>,
        retained_traces: Vec<Option<M>>,
        spilled_traces: std::sync::Mutex<Vec<Option<SpilledMatrix>>>,
        tree: HybridMerkleTree,
    },
    Cuda {
        resident: std::sync::Arc<Vec<CudaLde>>,
        materialize: Option<Box<dyn Fn() -> Vec<M> + Send + Sync>>,
        // `materialize` can own the last Arc to `resident`; drop it before
        // retained host matrices so pinned trace pointers cannot outlive them.
        committed_matrices: std::sync::OnceLock<Vec<M>>,
        retained_traces: std::sync::OnceLock<Vec<M>>,
        tree: CudaMixedMerkleTree,
    },
}

fn hybrid_matrix<'a, M>(
    matrices: &'a [std::sync::OnceLock<M>],
    deferred: &[DeferredWorker<M>],
    index: usize,
) -> &'a M {
    matrices[index].get_or_init(|| {
        let started = std::time::Instant::now();
        let matrix = deferred[index]
            .as_ref()
            .expect("hybrid matrix has neither storage nor deferred computation")
            .lock()
            .expect("deferred matrix lock poisoned")
            .take()
            .expect("deferred matrix worker already consumed")
            .join()
            .expect("deferred matrix worker panicked");
        if super::memory_diagnostics_enabled() {
            eprintln!(
                "[multi-stark/cuda] waited for deferred matrix {index}: {:.3}s",
                started.elapsed().as_secs_f64()
            );
        }
        matrix
    })
}

fn hybrid_resident_candidates<M>(
    data: &CudaMmcsData<M>,
    protected_index: Option<usize>,
) -> Vec<(usize, usize, bool)> {
    let CudaMmcsData::Hybrid {
        resident,
        resident_active,
        committed_matrices,
        spilled_matrices,
        ..
    } = data
    else {
        return Vec::new();
    };
    resident
        .iter()
        .enumerate()
        .filter_map(|(index, lde)| {
            if protected_index == Some(index) {
                return None;
            }
            let lde = lde.as_ref()?;
            resident_active[index]
                .load(std::sync::atomic::Ordering::Acquire)
                .then_some((
                    index,
                    lde.height().saturating_mul(lde.width()),
                    committed_matrices[index].get().is_some()
                        || spilled_matrices[index].get().is_some(),
                ))
        })
        .collect()
}

/// Frees the device caches of generator-backed resident LDEs, one at a time
/// until `target_free_bytes` is met, and returns the free bytes then. A cache
/// is the cheapest headroom there is: the generator rebuilds it from host
/// seeds on demand, whereas an evicted LDE must be materialized and uploaded
/// again.
fn release_generator_caches<M>(
    device_id: i32,
    data: &CudaMmcsData<M>,
    protected_index: Option<usize>,
    target_free_bytes: usize,
) -> usize {
    let mut free_bytes = super::device_memory_info(device_id).0;
    let CudaMmcsData::Hybrid { resident, .. } = data else {
        return free_bytes;
    };
    for (index, lde) in resident.iter().enumerate() {
        if free_bytes >= target_free_bytes {
            break;
        }
        if protected_index == Some(index) {
            continue;
        }
        let Some(lde) = lde else { continue };
        if !lde.has_generator() {
            continue;
        }
        lde.release_generator_device();
        free_bytes = super::device_memory_info(device_id).0;
    }
    free_bytes
}

fn evict_hybrid_resident<M>(data: &CudaMmcsData<M>, index: usize, spill_dir: Option<&Path>) {
    let CudaMmcsData::Hybrid {
        resident,
        resident_active,
        materialize,
        committed_matrices,
        spilled_matrices,
        ..
    } = data
    else {
        panic!("attempted to evict a non-hybrid CUDA commitment");
    };
    let lde = resident[index]
        .as_ref()
        .expect("hybrid resident matrix is missing its LDE");
    if committed_matrices[index].get().is_none() && spilled_matrices[index].get().is_none() {
        let matrix_bytes = lde
            .height()
            .saturating_mul(lde.width())
            .saturating_mul(size_of::<Goldilocks>());
        if let Some(dir) = spill_dir
            && !super::host_spill_headroom(lde.device_id, matrix_bytes)
        {
            let mut pack = SpillPackWriter::create(dir);
            let spilled = lde.spill_to_pack(&mut pack);
            pack.flush();
            let _ = spilled_matrices[index].set(spilled);
        } else {
            committed_matrices[index].get_or_init(|| materialize(lde));
        }
    }
    // SAFETY: admission transitions run between proving stages, when no CUDA
    // operation can access this LDE or its trace.
    unsafe { lde.release_values() };
    lde.release_generator_device();
    super::witness::record_lde_spill(
        lde.device_id,
        lde.height() * lde.width() * size_of::<Goldilocks>(),
    );
    resident_active[index].store(false, std::sync::atomic::Ordering::Release);
}

impl<M> CudaMmcsData<M> {
    pub(crate) fn resident(&self, index: usize) -> Option<&CudaLde> {
        match self {
            Self::Cuda { resident, .. } => resident.get(index),
            Self::Hybrid {
                resident,
                resident_active,
                ..
            } => {
                if resident_active
                    .get(index)?
                    .load(std::sync::atomic::Ordering::Acquire)
                {
                    resident.get(index)?.as_ref()
                } else {
                    None
                }
            }
            Self::Cpu(_) => None,
        }
    }

    pub(crate) fn spilled_original_trace(&self, index: usize) -> Option<SpilledMatrix> {
        match self {
            Self::Hybrid { spilled_traces, .. } => {
                let guard = spilled_traces.lock().expect("spilled_traces lock poisoned");
                guard.get(index).and_then(Clone::clone)
            }
            Self::Cuda { .. } | Self::Cpu(_) => None,
        }
    }

    pub(crate) fn release_original_traces(&self) {
        if let Self::Hybrid { spilled_traces, .. } = self {
            let mut guard = spilled_traces.lock().expect("spilled_traces lock poisoned");
            guard.clear();
        }
    }
}

impl CudaMmcsData<RowMajorMatrix<Goldilocks>> {
    /// Whether [`Self::resident_with_trace`] returns an LDE for this matrix,
    /// without attaching anything. A hybrid LDE qualifies while its values are
    /// resident, and after a spill as long as it can regenerate its trace from
    /// a generator or a retained host trace. Admission decisions that size a
    /// budget for the graph kernel must use this predicate, so that the budget
    /// and the kernel that then runs agree.
    pub(crate) fn has_resident_with_trace(&self, index: usize) -> bool {
        match self {
            Self::Cuda {
                resident,
                retained_traces,
                ..
            } => {
                index < resident.len()
                    && retained_traces
                        .get()
                        .is_none_or(|retained| index < retained.len())
            }
            Self::Hybrid {
                resident,
                resident_active,
                retained_traces,
                ..
            } => {
                let Some(Some(lde)) = resident.get(index) else {
                    return false;
                };
                let (Some(active), Some(retained)) =
                    (resident_active.get(index), retained_traces.get(index))
                else {
                    return false;
                };
                (active.load(std::sync::atomic::Ordering::Acquire) && lde.has_device_trace())
                    || lde.has_generator()
                    || retained.is_some()
            }
            Self::Cpu(_) => false,
        }
    }

    /// Device bytes the graph lookup over matrix `index` may allocate to
    /// regenerate its trace; see [`CudaLde::regeneration_bytes`]. A spilled
    /// hybrid LDE keeps its generator and counts too.
    pub(crate) fn regeneration_bytes(&self, index: usize) -> usize {
        let lde = match self {
            Self::Cuda { resident, .. } => resident.get(index),
            Self::Hybrid { resident, .. } => resident.get(index).and_then(Option::as_ref),
            Self::Cpu(_) => None,
        };
        lde.map_or(0, CudaLde::regeneration_bytes)
    }

    /// The resident LDE together with a retained host copy of its trace, if
    /// any, for readers that take the original trace without attaching it to
    /// the LDE. Unlike [`Self::resident_with_trace`] this never mutates the
    /// LDE, so it is safe on data shared across concurrent proofs, such as a
    /// preprocessed commitment. Returns `None` unless the trace is available
    /// on the device or as that host copy.
    pub(crate) fn resident_with_host_trace(
        &self,
        index: usize,
    ) -> Option<(&CudaLde, Option<&RowMajorMatrix<Goldilocks>>)> {
        let (lde, host) = match self {
            Self::Cuda {
                resident,
                retained_traces,
                ..
            } => (
                resident.get(index)?,
                retained_traces
                    .get()
                    .and_then(|retained| retained.get(index)),
            ),
            Self::Hybrid {
                resident,
                retained_traces,
                ..
            } => (
                resident.get(index)?.as_ref()?,
                retained_traces.get(index)?.as_ref(),
            ),
            Self::Cpu(_) => return None,
        };
        (lde.has_device_trace() || host.is_some()).then_some((lde, host))
    }

    pub(crate) fn resident_with_trace(&self, index: usize) -> Option<&CudaLde> {
        match self {
            Self::Cuda {
                resident,
                retained_traces,
                ..
            } => {
                let lde = resident.get(index)?;
                if let Some(retained) = retained_traces.get() {
                    // SAFETY: the matrix is retained in this prover data and
                    // drops after every Arc owner of `resident`. This proving
                    // path serializes attachment changes with CUDA use.
                    unsafe { lde.attach_trace(retained.get(index)?) };
                }
                Some(lde)
            }
            Self::Hybrid {
                resident,
                resident_active,
                retained_traces,
                ..
            } => {
                let lde = resident.get(index)?.as_ref()?;
                let has_active_device_trace = resident_active
                    .get(index)?
                    .load(std::sync::atomic::Ordering::Acquire)
                    && lde.has_device_trace();
                if !has_active_device_trace
                    && !lde.has_generator()
                    && retained_traces.get(index)?.is_none()
                {
                    return None;
                }
                if let Some(trace) = retained_traces.get(index)?.as_ref() {
                    // SAFETY: the trace is owned by this prover data and drops
                    // after the resident LDE which holds the registered pointer.
                    unsafe { lde.attach_trace(trace) };
                }
                Some(lde)
            }
            Self::Cpu(_) => None,
        }
    }
}

#[cfg(test)]
pub(crate) fn hash_cpu_height_groups<F: p3_field::Field>(
    matrices: &[Option<RowMajorMatrix<F>>],
) -> Vec<(usize, Vec<[u8; 32]>)> {
    let mut groups = std::collections::BTreeMap::<usize, Vec<&RowMajorMatrix<F>>>::new();
    for matrix in matrices.iter().flatten() {
        groups.entry(matrix.height()).or_default().push(matrix);
    }
    groups
        .into_iter()
        .map(|(height, matrices)| {
            let hasher = SerializingHasher::new(DomainBlake3::new(Blake3Domain::Plain));
            let digests = (0..height)
                .into_par_iter()
                .map(|row| {
                    hasher.hash_iter(matrices.iter().flat_map(|matrix| matrix.row(row).unwrap()))
                })
                .collect();
            (height, digests)
        })
        .collect()
}

/// The CUDA BLAKE3 leaf kernel hashes one message of at most 32 KiB per
/// row, and a mixed tree's leaf row at a height is every matrix of that
/// height side by side. A height group whose rows are wider than that is
/// hashed on the host and enters the tree as a digest group; the device
/// still builds the rest of the tree.
pub(crate) const MAX_DEVICE_LEAF_ROW_BYTES: usize = 32 * 1024;

/// The heights whose concatenated leaf row exceeds
/// [`MAX_DEVICE_LEAF_ROW_BYTES`], and so must be hashed on the host.
pub(crate) fn host_hashed_heights(
    dimensions: impl IntoIterator<Item = Dimensions>,
) -> std::collections::BTreeSet<usize> {
    let mut row_bytes = std::collections::BTreeMap::<usize, usize>::new();
    for dimensions in dimensions {
        *row_bytes.entry(dimensions.height).or_default() +=
            dimensions.width * size_of::<Goldilocks>();
    }
    row_bytes
        .into_iter()
        .filter(|(_, bytes)| *bytes > MAX_DEVICE_LEAF_ROW_BYTES)
        .map(|(height, _)| height)
        .collect()
}

pub(crate) fn hash_host_only_height_groups<F: PrimeField64>(
    matrices: &[Option<RowMajorMatrix<F>>],
    resident: &[Option<&CudaLde>],
    deferred_dimensions: &[Option<Dimensions>],
    prehashed_heights: &std::collections::BTreeSet<usize>,
    leaf_domain: Blake3Domain,
) -> Vec<(usize, Vec<[u8; 32]>)> {
    assert_eq!(matrices.len(), resident.len());
    assert_eq!(matrices.len(), deferred_dimensions.len());
    let mut groups = std::collections::BTreeMap::<usize, Vec<usize>>::new();
    for (index, ((matrix, lde), deferred)) in matrices
        .iter()
        .zip(resident)
        .zip(deferred_dimensions)
        .enumerate()
    {
        assert!(
            usize::from(matrix.is_some())
                + usize::from(lde.is_some())
                + usize::from(deferred.is_some())
                == 1,
            "every partitioned matrix must have exactly one storage backend"
        );
        let height = matrix.as_ref().map_or_else(
            || {
                lde.as_ref()
                    .map_or_else(|| deferred.unwrap().height, |lde| lde.height())
            },
            Matrix::height,
        );
        assert!(
            deferred.is_none() || prehashed_heights.contains(&height),
            "a deferred matrix requires a pre-hashed height group"
        );
        groups.entry(height).or_default().push(index);
    }

    let hasher = SerializingHasher::new(DomainBlake3::new(leaf_domain));
    groups
        .into_iter()
        .filter_map(|(height, indices)| {
            if prehashed_heights.contains(&height)
                || indices.iter().any(|&index| resident[index].is_some())
            {
                // CUDA hashes fully resident groups directly and assembles mixed
                // groups from resident and mapped host columns in bounded chunks.
                return None;
            }
            let sources = indices
                .iter()
                .map(|&index| matrices[index].as_ref().unwrap())
                .collect::<Vec<_>>();
            let digests = (0..height)
                .into_par_iter()
                .map(|row| {
                    hasher.hash_iter(sources.iter().flat_map(|matrix| matrix.row(row).unwrap()))
                })
                .collect();
            Some((height, digests))
        })
        .collect()
}

fn hybrid_max_height(dimensions: &[Dimensions]) -> usize {
    dimensions
        .iter()
        .map(|dimensions| dimensions.height)
        .max()
        .unwrap()
}

fn hybrid_open_row<M: Matrix<Goldilocks>>(
    resident: &[Option<CudaLde>],
    resident_active: &[std::sync::atomic::AtomicBool],
    matrices: &[std::sync::OnceLock<M>],
    spilled: &[std::sync::OnceLock<SpilledMatrix>],
    deferred: &[DeferredWorker<M>],
    dimensions: &[Dimensions],
    index: usize,
) -> Vec<Vec<Goldilocks>> {
    let max_height = hybrid_max_height(dimensions);
    assert!(index < max_height, "MMCS opening index out of bounds");
    let active_ldes = resident
        .iter()
        .zip(resident_active)
        .filter_map(|(resident, active)| {
            active
                .load(std::sync::atomic::Ordering::Acquire)
                .then_some(resident.as_ref())
                .flatten()
        })
        .collect::<Vec<_>>();
    let mut gpu_rows = if !active_ldes.is_empty() {
        mixed_lde_open_row_at_height(active_ldes, max_height, index).into_iter()
    } else {
        Vec::new().into_iter()
    };
    resident
        .iter()
        .zip(resident_active)
        .enumerate()
        .map(|(matrix_index, (resident, active))| {
            if resident.is_some() && active.load(std::sync::atomic::Ordering::Acquire) {
                gpu_rows.next().unwrap()
            } else if let Some(sp) = spilled[matrix_index].get() {
                let row = index >> (max_height.trailing_zeros() - sp.height().trailing_zeros());
                sp.read_row(row)
            } else {
                let matrix = hybrid_matrix(matrices, deferred, matrix_index);
                let row = index >> (max_height.trailing_zeros() - matrix.height().trailing_zeros());
                matrix.row(row).unwrap().into_iter().collect()
            }
        })
        .collect()
}

fn hybrid_open_rows<M: Matrix<Goldilocks>>(
    resident: &[Option<CudaLde>],
    resident_active: &[std::sync::atomic::AtomicBool],
    matrices: &[std::sync::OnceLock<M>],
    spilled: &[std::sync::OnceLock<SpilledMatrix>],
    deferred: &[DeferredWorker<M>],
    dimensions: &[Dimensions],
    indices: &[usize],
) -> Vec<Vec<Vec<Goldilocks>>> {
    if indices.is_empty() {
        return Vec::new();
    }
    let max_height = hybrid_max_height(dimensions);
    assert!(indices.iter().all(|&index| index < max_height));
    let active_ldes = resident
        .iter()
        .zip(resident_active)
        .filter_map(|(resident, active)| {
            active
                .load(std::sync::atomic::Ordering::Acquire)
                .then_some(resident.as_ref())
                .flatten()
        })
        .collect::<Vec<_>>();
    let mut gpu_queries = if !active_ldes.is_empty() {
        mixed_lde_open_rows_at_height(active_ldes, max_height, indices).into_iter()
    } else {
        (0..indices.len())
            .map(|_| Vec::new())
            .collect::<Vec<_>>()
            .into_iter()
    };
    indices
        .iter()
        .map(|&index| {
            let mut gpu_rows = gpu_queries.next().unwrap().into_iter();
            resident
                .iter()
                .zip(resident_active)
                .enumerate()
                .map(|(matrix_index, (resident, active))| {
                    if resident.is_some() && active.load(std::sync::atomic::Ordering::Acquire) {
                        gpu_rows.next().unwrap()
                    } else if let Some(sp) = spilled[matrix_index].get() {
                        let row =
                            index >> (max_height.trailing_zeros() - sp.height().trailing_zeros());
                        sp.read_row(row)
                    } else {
                        let matrix = hybrid_matrix(matrices, deferred, matrix_index);
                        let row = index
                            >> (max_height.trailing_zeros() - matrix.height().trailing_zeros());
                        matrix.row(row).unwrap().into_iter().collect()
                    }
                })
                .collect()
        })
        .collect()
}

#[derive(Clone, Debug)]
pub struct CudaMmcs {
    cpu: CpuMmcs,
    cap_height: usize,
    leaf_domain: Blake3Domain,
    device_id: i32,
    spill_dir: Option<PathBuf>,
}

/// The trace a committed LDE extends: the bit-reversed LDE over `gK` starts
/// with the bit-reversed evaluations on `gH`, which interpolate the trace
/// polynomial back onto `H`. Computed on the host, so a device under memory
/// pressure is not asked for transform workspace.
fn trace_from_lde(
    lde: &RowMajorMatrix<Goldilocks>,
    log_blowup: usize,
) -> RowMajorMatrix<Goldilocks> {
    use p3_dft::TwoAdicSubgroupDft;
    use p3_field::Field;
    use p3_matrix::bitrev::BitReversibleMatrix;
    let degree = lde.height() >> log_blowup;
    let evaluations = lde
        .split_rows(degree)
        .0
        .as_cow()
        .bit_reverse_rows()
        .to_row_major_matrix();
    let dft = p3_dft::Radix2DitParallel::<Goldilocks>::default();
    let coefficients = dft.coset_idft_batch(evaluations, Goldilocks::GENERATOR);
    dft.dft_batch(coefficients).to_row_major_matrix()
}

impl CudaMmcs {
    /// Creates a legacy `v5` plain BLAKE3 CUDA MMCS (bit-identical to stock
    /// `p3_blake3::Blake3`).
    pub(crate) fn new_plain(cap_height: usize, device_id: i32) -> Self {
        let field_hash = SerializingHasher::new(DomainBlake3::new(Blake3Domain::Plain));
        let compress = DomainCompressionFunction::new(DomainBlake3::new(Blake3Domain::Plain));
        let cpu = CpuMmcs::new(field_hash, compress, cap_height);
        Self::with_device_and_domain(cpu, cap_height, Blake3Domain::Plain, device_id)
    }

    /// Creates a protocol `v6` domain-separated BLAKE3 CUDA MMCS separating
    /// Merkle leaf row hashes (`MerkleLeaf`) from 2-to-1 internal compressions
    /// (`MerkleCompress`).
    pub(crate) fn new_v6(cap_height: usize, device_id: i32) -> Self {
        let field_hash = SerializingHasher::new(DomainBlake3::new(Blake3Domain::MerkleLeaf));
        let compress =
            DomainCompressionFunction::new(DomainBlake3::new(Blake3Domain::MerkleCompress));
        let cpu = CpuMmcs::new(field_hash, compress, cap_height);
        Self::with_device_and_domain(cpu, cap_height, Blake3Domain::MerkleLeaf, device_id)
    }

    /// The stage-one trace of committed matrix `index`, for evaluating the
    /// lookups a shape-only witness omitted: the retained host trace when
    /// the commitment kept one, otherwise rebuilt from the committed LDE,
    /// read back from the device if necessary. Only that matrix is read and
    /// nothing is cached in `data`.
    pub(crate) fn committed_trace(
        &self,
        data: &CudaMmcsData<RowMajorMatrix<Goldilocks>>,
        index: usize,
        log_blowup: usize,
    ) -> RowMajorMatrix<Goldilocks> {
        match data {
            CudaMmcsData::Cpu(data) => {
                trace_from_lde(self.cpu.get_matrices(data)[index], log_blowup)
            }
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                retained_traces,
                ..
            } => {
                if let Some(spilled_trace) = data.spilled_original_trace(index) {
                    return spilled_trace.read_all();
                }
                if let Some(trace) = &retained_traces[index] {
                    return trace.clone();
                }
                if let Some(lde) = committed_matrices[index].get() {
                    return trace_from_lde(lde, log_blowup);
                }
                if let Some(lde) = resident[index].as_ref()
                    && resident_active[index].load(std::sync::atomic::Ordering::Acquire)
                {
                    return trace_from_lde(&lde.to_row_major_matrix(), log_blowup);
                }
                if let Some(spilled_lde) = spilled_matrices[index].get() {
                    let degree = spilled_lde.height() >> log_blowup;
                    let prefix = spilled_lde.read_rows(0, degree);
                    return trace_from_lde(&prefix, 0);
                }
                trace_from_lde(
                    hybrid_matrix(committed_matrices, deferred_matrices, index),
                    log_blowup,
                )
            }
            CudaMmcsData::Cuda {
                resident,
                committed_matrices,
                retained_traces,
                ..
            } => {
                if let Some(trace) = retained_traces.get().and_then(|traces| traces.get(index)) {
                    return trace.clone();
                }
                if let Some(ldes) = committed_matrices.get() {
                    return trace_from_lde(&ldes[index], log_blowup);
                }
                trace_from_lde(&resident[index].to_row_major_matrix(), log_blowup)
            }
        }
    }

    /// A commitment scheme resident on the given CUDA device. Every kernel
    /// it launches, allocation it makes and buffer it stages through belongs
    /// to that device, so several of these in one process can each own a
    /// device of their own.
    pub(crate) fn with_device_and_domain(
        cpu: CpuMmcs,
        cap_height: usize,
        leaf_domain: Blake3Domain,
        device_id: i32,
    ) -> Self {
        assert!(device_id >= 0, "CUDA device id must be non-negative");
        assert!(
            matches!(leaf_domain, Blake3Domain::Plain | Blake3Domain::MerkleLeaf),
            "unsupported CUDA Merkle leaf domain: {leaf_domain:?}"
        );
        Self {
            cpu,
            cap_height,
            leaf_domain,
            device_id,
            spill_dir: None,
        }
    }

    pub(crate) fn set_spill_dir(&mut self, spill_dir: Option<PathBuf>) {
        self.spill_dir = spill_dir;
    }

    pub(crate) fn spill_dir(&self) -> Option<&Path> {
        self.spill_dir.as_deref()
    }

    #[inline]
    pub(crate) const fn compress_domain(&self) -> Blake3Domain {
        match self.leaf_domain {
            Blake3Domain::MerkleLeaf => Blake3Domain::MerkleCompress,
            _ => Blake3Domain::Plain,
        }
    }

    #[cfg(test)]
    pub(crate) fn with_device(cpu: CpuMmcs, device_id: i32) -> Self {
        Self::with_device_and_domain(cpu, 0, Blake3Domain::Plain, device_id)
    }

    #[inline]
    pub const fn cap_height(&self) -> usize {
        self.cap_height
    }

    #[inline]
    pub(crate) const fn leaf_domain(&self) -> Blake3Domain {
        self.leaf_domain
    }

    #[inline]
    pub(crate) const fn is_domain_v6(&self) -> bool {
        matches!(self.leaf_domain, Blake3Domain::MerkleLeaf)
    }
}

pub trait CudaCommitMmcs<T: Send + Sync + Clone>: Mmcs<T> {
    fn cuda_device_id(&self) -> i32;

    fn spill_dir(&self) -> Option<&Path>;

    fn leaf_domain(&self) -> Blake3Domain;

    fn is_domain_v6(&self) -> bool {
        matches!(self.leaf_domain(), Blake3Domain::MerkleLeaf)
    }

    fn hash_cuda_hybrid_height_group(
        &self,
        resident: &[Option<&CudaLde>],
        host: &[Option<&RowMajorMatrix<T>>],
    ) -> Vec<[u8; 32]>;

    fn is_cuda_resident<M: Matrix<T>>(&self, data: &Self::ProverData<M>) -> bool;

    fn is_matrix_cuda_resident<M: Matrix<T>>(
        &self,
        data: &Self::ProverData<M>,
        index: usize,
    ) -> bool;

    /// Reports whether a matrix can be accessed without waiting for deferred
    /// host materialization.
    fn is_matrix_source_ready<M: Matrix<T>>(
        &self,
        data: &Self::ProverData<M>,
        index: usize,
    ) -> bool;

    /// Materializes and releases the largest hybrid-resident matrices until
    /// the device has at least `target_free_bytes` available. Returns the
    /// measured free bytes after eviction.
    fn ensure_device_headroom<M: Matrix<T>>(
        &self,
        data: &Self::ProverData<M>,
        target_free_bytes: usize,
        protected_index: Option<usize>,
        phase: &'static str,
    ) -> usize;

    /// Selects spill candidates across all supplied commitments instead of
    /// letting iteration order decide which commitment gives up residency.
    fn ensure_device_headroom_batch(
        &self,
        data: &[&Self::ProverData<RowMajorMatrix<T>>],
        target_free_bytes: usize,
        phase: &'static str,
    ) -> usize;

    fn matrix_dimensions(&self, data: &Self::ProverData<RowMajorMatrix<T>>) -> Vec<Dimensions>;

    fn cpu_matrices<'a>(
        &self,
        data: &'a Self::ProverData<RowMajorMatrix<T>>,
    ) -> Vec<Option<&'a RowMajorMatrix<T>>>;

    fn spilled_matrices<'a>(
        &self,
        data: &'a Self::ProverData<RowMajorMatrix<T>>,
    ) -> Vec<Option<&'a SpilledMatrix>>;

    fn commit_cuda_mixed_spilled(
        &self,
        resident: Vec<Option<CudaLde>>,
        host_matrices: Vec<Option<RowMajorMatrix<T>>>,
        spilled_matrices: Vec<Option<SpilledMatrix>>,
        prehashed: Vec<Option<Vec<[u8; 32]>>>,
        retained_traces: Vec<Option<RowMajorMatrix<T>>>,
        spilled_traces: Vec<Option<SpilledMatrix>>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);

    fn with_resident_matrix<R>(
        &self,
        data: &Self::ProverData<RowMajorMatrix<T>>,
        index: usize,
        f: impl FnOnce(&CudaLde) -> R,
    ) -> R;

    fn with_matrix_source<R>(
        &self,
        data: &Self::ProverData<RowMajorMatrix<T>>,
        index: usize,
        f: impl FnOnce(CudaMatrixSource<'_>) -> R,
    ) -> R;

    fn resident_or_upload<M: Matrix<T>>(
        &self,
        data: &Self::ProverData<M>,
    ) -> std::sync::Arc<Vec<CudaLde>>;
    fn commit_cuda_resident(
        &self,
        ldes: Vec<CudaLde>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);

    fn commit_cuda_spillable(
        &self,
        ldes: Vec<CudaLde>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);

    fn commit_cuda_hybrid(
        &self,
        resident: Vec<Option<CudaLde>>,
        host_matrices: Vec<Option<RowMajorMatrix<T>>>,
        deferred_matrices: Vec<DeferredMatrix<RowMajorMatrix<T>>>,
        retained_traces: Vec<Option<RowMajorMatrix<T>>>,
        host_digest_groups: Vec<(usize, Vec<[u8; 32]>)>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);

    fn retain_matrices(
        &self,
        data: &mut Self::ProverData<RowMajorMatrix<T>>,
        matrices: Vec<RowMajorMatrix<T>>,
    );

    fn commit_cuda_storage(
        &self,
        ldes: Vec<RowMajorMatrix<T>>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);

    fn commit_cpu_storage(
        &self,
        ldes: Vec<RowMajorMatrix<T>>,
    ) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>);
}

impl CudaCommitMmcs<Goldilocks> for CudaMmcs {
    fn cuda_device_id(&self) -> i32 {
        self.device_id
    }

    fn spill_dir(&self) -> Option<&Path> {
        self.spill_dir.as_deref()
    }

    fn leaf_domain(&self) -> Blake3Domain {
        self.leaf_domain
    }

    fn hash_cuda_hybrid_height_group(
        &self,
        resident: &[Option<&CudaLde>],
        host: &[Option<&RowMajorMatrix<Goldilocks>>],
    ) -> Vec<[u8; 32]> {
        CudaMixedMerkleTree::hash_hybrid_height_group_with_domain(
            self.device_id,
            resident,
            host,
            self.is_domain_v6(),
        )
    }

    fn is_cuda_resident<M: Matrix<Goldilocks>>(&self, data: &Self::ProverData<M>) -> bool {
        matches!(data, CudaMmcsData::Cuda { .. })
    }

    fn is_matrix_cuda_resident<M: Matrix<Goldilocks>>(
        &self,
        data: &Self::ProverData<M>,
        index: usize,
    ) -> bool {
        match data {
            CudaMmcsData::Cpu(_) => false,
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                ..
            } => {
                resident
                    .get(index)
                    .expect("hybrid matrix index out of bounds");
                resident_active[index].load(std::sync::atomic::Ordering::Acquire)
            }
            CudaMmcsData::Cuda { resident, .. } => {
                assert!(index < resident.len(), "CUDA matrix index out of bounds");
                true
            }
        }
    }

    fn is_matrix_source_ready<M: Matrix<Goldilocks>>(
        &self,
        data: &Self::ProverData<M>,
        index: usize,
    ) -> bool {
        match data {
            CudaMmcsData::Cpu(data) => {
                assert!(
                    index < self.cpu.get_matrix_heights(data).len(),
                    "CPU matrix index out of bounds"
                );
                true
            }
            CudaMmcsData::Cuda { resident, .. } => {
                assert!(index < resident.len(), "CUDA matrix index out of bounds");
                true
            }
            CudaMmcsData::Hybrid {
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                ..
            } => {
                let active = resident_active
                    .get(index)
                    .expect("hybrid matrix index out of bounds")
                    .load(std::sync::atomic::Ordering::Acquire);
                active
                    || committed_matrices[index].get().is_some()
                    || spilled_matrices[index].get().is_some()
                    || deferred_matrices[index].as_ref().is_some_and(|worker| {
                        worker
                            .lock()
                            .expect("deferred matrix lock poisoned")
                            .as_ref()
                            .is_some_and(std::thread::JoinHandle::is_finished)
                    })
            }
        }
    }

    fn ensure_device_headroom<M: Matrix<Goldilocks>>(
        &self,
        data: &Self::ProverData<M>,
        target_free_bytes: usize,
        protected_index: Option<usize>,
        phase: &'static str,
    ) -> usize {
        let (mut free_bytes, _) = super::device_memory_info(self.device_id);
        if super::memory_diagnostics_enabled() {
            eprintln!(
                "[multi-stark/cuda] {phase} admission start: target={} free={}",
                target_free_bytes, free_bytes
            );
        }
        if free_bytes >= target_free_bytes {
            return free_bytes;
        }
        free_bytes =
            release_generator_caches(self.device_id, data, protected_index, target_free_bytes);
        if free_bytes >= target_free_bytes {
            if super::memory_diagnostics_enabled() {
                eprintln!(
                    "[multi-stark/cuda] {phase} admitted after releasing generator caches: free={free_bytes}"
                );
            }
            return free_bytes;
        }
        let mut candidates = hybrid_resident_candidates(data, protected_index);
        while free_bytes < target_free_bytes && !candidates.is_empty() {
            let deficit_cells = target_free_bytes
                .saturating_sub(free_bytes)
                .div_ceil(size_of::<Goldilocks>());
            let candidate = candidates
                .iter()
                .enumerate()
                .filter(|(_, (_, cells, _))| *cells >= deficit_cells)
                .min_by_key(|(_, (_, cells, _))| *cells)
                .or_else(|| {
                    candidates
                        .iter()
                        .enumerate()
                        .max_by_key(|(_, (_, cells, _))| *cells)
                })
                .map(|(position, _)| position)
                .unwrap();
            let (index, cells, _) = candidates.swap_remove(candidate);
            evict_hybrid_resident(data, index, self.spill_dir.as_deref());
            // Eviction is a synchronous device release. Re-read the allocator
            // instead of inferring availability from logical matrix sizes:
            // CUDA allocation granularity and per-thread memory pools make a
            // byte-sum projection unreliable across Rayon worker streams.
            free_bytes = super::device_memory_info(self.device_id).0;
            if super::memory_diagnostics_enabled() {
                eprintln!(
                    "[multi-stark/cuda] evicted matrix {index}: cells={cells} free={free_bytes}"
                );
            }
        }
        free_bytes
    }

    fn ensure_device_headroom_batch(
        &self,
        data: &[&Self::ProverData<RowMajorMatrix<Goldilocks>>],
        target_free_bytes: usize,
        phase: &'static str,
    ) -> usize {
        let (mut measured_free_bytes, _) = super::device_memory_info(self.device_id);
        if super::memory_diagnostics_enabled() {
            eprintln!(
                "[multi-stark/cuda] {phase} batch admission start: target={} free={}",
                target_free_bytes, measured_free_bytes
            );
        }
        if measured_free_bytes >= target_free_bytes {
            return measured_free_bytes;
        }
        for data in data {
            measured_free_bytes =
                release_generator_caches(self.device_id, data, None, target_free_bytes);
            if measured_free_bytes >= target_free_bytes {
                if super::memory_diagnostics_enabled() {
                    eprintln!(
                        "[multi-stark/cuda] {phase} batch admitted after releasing generator caches: free={measured_free_bytes}"
                    );
                }
                return measured_free_bytes;
            }
        }
        let initial_free_bytes = measured_free_bytes;
        let mut released_bytes = 0usize;
        let mut candidates = data
            .iter()
            .enumerate()
            .flat_map(|(data_index, data)| {
                hybrid_resident_candidates(data, None).into_iter().map(
                    move |(matrix_index, cells, host_ready)| {
                        (data_index, matrix_index, cells, host_ready)
                    },
                )
            })
            .collect::<Vec<_>>();
        while initial_free_bytes
            .saturating_add(released_bytes)
            .max(measured_free_bytes)
            < target_free_bytes
            && !candidates.is_empty()
        {
            let available_bytes = initial_free_bytes
                .saturating_add(released_bytes)
                .max(measured_free_bytes);
            let deficit_cells = target_free_bytes
                .saturating_sub(available_bytes)
                .div_ceil(size_of::<Goldilocks>());
            let ready = candidates.iter().any(|candidate| candidate.3);
            let eligible = |candidate: &&(usize, usize, usize, bool)| !ready || candidate.3;
            let candidate = candidates
                .iter()
                .enumerate()
                .filter(|(_, candidate)| eligible(candidate))
                .filter(|(_, (_, _, cells, _))| *cells <= deficit_cells)
                .max_by_key(|(_, (_, _, cells, _))| *cells)
                .or_else(|| {
                    candidates
                        .iter()
                        .enumerate()
                        .filter(|(_, candidate)| eligible(candidate))
                        .min_by_key(|(_, (_, _, cells, _))| *cells)
                })
                .map(|(position, _)| position)
                .unwrap();
            let (data_index, matrix_index, cells, host_ready) = candidates.swap_remove(candidate);
            evict_hybrid_resident(data[data_index], matrix_index, self.spill_dir.as_deref());
            // `release_values` synchronously frees this exact payload. CUDA's
            // free-memory counters advance at allocator granularity, however,
            // so requiring `cudaMemGetInfo` to reflect every small release can
            // evict hundreds of matrices to cover a sub-granule reporting gap.
            // The released payload is a conservative lower bound (the LDE may
            // also release interpolation scratch), while the fresh measurement
            // catches unrelated memory becoming available.
            released_bytes =
                released_bytes.saturating_add(cells.saturating_mul(size_of::<Goldilocks>()));
            measured_free_bytes = super::device_memory_info(self.device_id).0;
            if super::memory_diagnostics_enabled() {
                eprintln!(
                    "[multi-stark/cuda] batch evicted commitment {data_index} matrix {matrix_index}: cells={cells} host_ready={host_ready} measured_free={measured_free_bytes} projected_free={}",
                    initial_free_bytes.saturating_add(released_bytes)
                );
            }
        }
        initial_free_bytes
            .saturating_add(released_bytes)
            .max(measured_free_bytes)
    }

    fn matrix_dimensions(
        &self,
        data: &Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) -> Vec<Dimensions> {
        match data {
            CudaMmcsData::Cpu(data) => self
                .cpu
                .get_matrices(data)
                .into_iter()
                .map(Matrix::dimensions)
                .collect(),
            CudaMmcsData::Hybrid { dimensions, .. } => dimensions.clone(),
            CudaMmcsData::Cuda { resident, .. } => resident
                .iter()
                .map(|lde| Dimensions {
                    width: lde.width(),
                    height: lde.height(),
                })
                .collect(),
        }
    }

    fn cpu_matrices<'a>(
        &self,
        data: &'a Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) -> Vec<Option<&'a RowMajorMatrix<Goldilocks>>> {
        match data {
            CudaMmcsData::Cpu(data) => self.cpu.get_matrices(data).into_iter().map(Some).collect(),
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                ..
            } => resident
                .iter()
                .zip(resident_active)
                .enumerate()
                .map(|(index, (resident, active))| {
                    let is_res =
                        resident.is_some() && active.load(std::sync::atomic::Ordering::Acquire);
                    if is_res || spilled_matrices[index].get().is_some() {
                        None
                    } else {
                        Some(hybrid_matrix(committed_matrices, deferred_matrices, index))
                    }
                })
                .collect(),
            CudaMmcsData::Cuda { resident, .. } => (0..resident.len()).map(|_| None).collect(),
        }
    }

    fn spilled_matrices<'a>(
        &self,
        data: &'a Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) -> Vec<Option<&'a SpilledMatrix>> {
        match data {
            CudaMmcsData::Cpu(data) => vec![None; self.cpu.get_matrix_heights(data).len()],
            CudaMmcsData::Cuda { resident, .. } => vec![None; resident.len()],
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                spilled_matrices,
                ..
            } => resident
                .iter()
                .zip(resident_active)
                .enumerate()
                .map(|(index, (res, active))| {
                    let is_res = res.is_some() && active.load(std::sync::atomic::Ordering::Acquire);
                    if is_res {
                        None
                    } else {
                        spilled_matrices[index].get()
                    }
                })
                .collect(),
        }
    }

    fn with_resident_matrix<R>(
        &self,
        data: &Self::ProverData<RowMajorMatrix<Goldilocks>>,
        index: usize,
        f: impl FnOnce(&CudaLde) -> R,
    ) -> R {
        match data {
            CudaMmcsData::Cuda { resident, .. } => f(resident
                .get(index)
                .expect("CUDA matrix index out of bounds")),
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                deferred_matrices,
                ..
            } => {
                let resident = resident
                    .get(index)
                    .expect("hybrid matrix index out of bounds");
                if resident_active[index].load(std::sync::atomic::Ordering::Acquire) {
                    let lde = resident.as_ref().expect("active hybrid matrix has no LDE");
                    f(lde)
                } else {
                    let matrix = hybrid_matrix(committed_matrices, deferred_matrices, index);
                    if super::memory_diagnostics_enabled() {
                        let (free_bytes, _) = super::device_memory_info(self.device_id);
                        eprintln!(
                            "[multi-stark/cuda] upload hybrid matrix {index}: bytes={} free={free_bytes}",
                            matrix
                                .height()
                                .saturating_mul(matrix.width())
                                .saturating_mul(size_of::<Goldilocks>())
                        );
                    }
                    let uploaded = CudaLde::from_row_major_matrix(self.device_id, matrix);
                    f(&uploaded)
                }
            }
            CudaMmcsData::Cpu(data) => {
                let matrices = self.cpu.get_matrices(data);
                let matrix = matrices.get(index).expect("CPU matrix index out of bounds");
                if super::memory_diagnostics_enabled() {
                    let (free_bytes, _) = super::device_memory_info(self.device_id);
                    eprintln!(
                        "[multi-stark/cuda] upload CPU matrix {index}: bytes={} free={free_bytes}",
                        matrix
                            .height()
                            .saturating_mul(matrix.width())
                            .saturating_mul(size_of::<Goldilocks>())
                    );
                }
                let uploaded = CudaLde::from_row_major_matrix(self.device_id, matrix);
                f(&uploaded)
            }
        }
    }

    fn with_matrix_source<R>(
        &self,
        data: &Self::ProverData<RowMajorMatrix<Goldilocks>>,
        index: usize,
        f: impl FnOnce(CudaMatrixSource<'_>) -> R,
    ) -> R {
        match data {
            CudaMmcsData::Cuda { resident, .. } => f(CudaMatrixSource::Resident(
                resident
                    .get(index)
                    .expect("CUDA matrix index out of bounds"),
            )),
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                ..
            } => {
                if resident_active
                    .get(index)
                    .expect("hybrid matrix index out of bounds")
                    .load(std::sync::atomic::Ordering::Acquire)
                {
                    f(CudaMatrixSource::Resident(
                        resident[index]
                            .as_ref()
                            .expect("active hybrid matrix has no LDE"),
                    ))
                } else if let Some(spilled) = spilled_matrices[index].get() {
                    f(CudaMatrixSource::Spilled(spilled))
                } else {
                    f(CudaMatrixSource::Host(hybrid_matrix(
                        committed_matrices,
                        deferred_matrices,
                        index,
                    )))
                }
            }
            CudaMmcsData::Cpu(data) => {
                let matrices = self.cpu.get_matrices(data);
                f(CudaMatrixSource::Host(
                    matrices.get(index).expect("CPU matrix index out of bounds"),
                ))
            }
        }
    }

    fn commit_cpu_storage(
        &self,
        ldes: Vec<RowMajorMatrix<Goldilocks>>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        let (commitment, data) = self.cpu.commit(ldes);
        (commitment, CudaMmcsData::Cpu(data))
    }

    fn retain_matrices(
        &self,
        data: &mut Self::ProverData<RowMajorMatrix<Goldilocks>>,
        retained: Vec<RowMajorMatrix<Goldilocks>>,
    ) {
        match data {
            CudaMmcsData::Cuda {
                retained_traces, ..
            } => retained_traces
                .set(retained)
                .expect("fresh CUDA trace matrix cell"),
            CudaMmcsData::Hybrid {
                retained_traces, ..
            } => {
                assert_eq!(retained_traces.len(), retained.len());
                assert!(retained_traces.iter().all(Option::is_none));
                for (slot, matrix) in retained_traces.iter_mut().zip(retained) {
                    *slot = Some(matrix);
                }
            }
            CudaMmcsData::Cpu(_) => {
                panic!("CPU commitment cannot retain CUDA trace matrices")
            }
        }
    }

    fn resident_or_upload<M: Matrix<Goldilocks>>(
        &self,
        data: &Self::ProverData<M>,
    ) -> std::sync::Arc<Vec<CudaLde>> {
        match data {
            CudaMmcsData::Cuda { resident, .. } => std::sync::Arc::clone(resident),
            CudaMmcsData::Hybrid { .. } => {
                panic!("hybrid commitments cannot be converted to all-resident storage")
            }
            CudaMmcsData::Cpu(cpu) => std::sync::Arc::new(
                self.cpu
                    .get_matrices(cpu)
                    .into_iter()
                    .map(|matrix| {
                        let values = (0..matrix.height())
                            .flat_map(|row| matrix.row(row).unwrap())
                            .collect();
                        CudaLde::from_row_major_matrix(
                            self.device_id,
                            &RowMajorMatrix::new(values, matrix.width()),
                        )
                    })
                    .collect(),
            ),
        }
    }
    fn commit_cuda_resident(
        &self,
        ldes: Vec<CudaLde>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        // A height group whose leaf row is wider than the device kernel
        // hashes cannot be part of an all-resident tree: its LDEs come back
        // to the host, its digests are hashed there, and the commitment is
        // the hybrid one every other stage already handles.
        let wide_heights = host_hashed_heights(ldes.iter().map(|lde| Dimensions {
            width: lde.width(),
            height: lde.height(),
        }));
        if !wide_heights.is_empty() {
            let mut resident: Vec<Option<CudaLde>> = Vec::with_capacity(ldes.len());
            let mut host: Vec<Option<RowMajorMatrix<Goldilocks>>> = Vec::with_capacity(ldes.len());
            for lde in ldes {
                if wide_heights.contains(&lde.height()) {
                    host.push(Some(lde.to_row_major_matrix()));
                    resident.push(None);
                } else {
                    host.push(None);
                    resident.push(Some(lde));
                }
            }
            let deferred: Vec<DeferredMatrix<RowMajorMatrix<Goldilocks>>> =
                (0..resident.len()).map(|_| None).collect();
            let deferred_dimensions = vec![None; resident.len()];
            let digests = hash_host_only_height_groups(
                &host,
                &resident.iter().map(Option::as_ref).collect::<Vec<_>>(),
                &deferred_dimensions,
                &std::collections::BTreeSet::new(),
                self.leaf_domain,
            );
            let retained = (0..resident.len()).map(|_| None).collect();
            return self.commit_cuda_hybrid(resident, host, deferred, retained, digests);
        }
        let ldes = std::sync::Arc::new(ldes);
        let tree =
            CudaMixedMerkleTree::from_ldes_with_domain(self.device_id, &ldes, self.is_domain_v6());
        let commitment = MerkleCap::new(vec![tree.root()]);
        let materialize_ldes = std::sync::Arc::clone(&ldes);
        (
            commitment,
            CudaMmcsData::Cuda {
                resident: ldes,
                materialize: Some(Box::new(move || {
                    materialize_ldes
                        .iter()
                        .map(CudaLde::to_row_major_matrix)
                        .collect()
                })),
                committed_matrices: std::sync::OnceLock::new(),
                retained_traces: std::sync::OnceLock::new(),
                tree,
            },
        )
    }

    fn commit_cuda_spillable(
        &self,
        ldes: Vec<CudaLde>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        // Mirror `commit_cuda_resident`: height groups exceeding the 4096-column
        // (32 KiB) device BLAKE3 leaf-hash limit must be hashed on the host.
        let wide_heights = host_hashed_heights(ldes.iter().map(|lde| Dimensions {
            width: lde.width(),
            height: lde.height(),
        }));
        if !wide_heights.is_empty() {
            let mut resident: Vec<Option<CudaLde>> = Vec::with_capacity(ldes.len());
            let mut host: Vec<Option<RowMajorMatrix<Goldilocks>>> = Vec::with_capacity(ldes.len());
            for lde in ldes {
                if wide_heights.contains(&lde.height()) {
                    host.push(Some(lde.to_row_major_matrix()));
                    resident.push(None);
                } else {
                    host.push(None);
                    resident.push(Some(lde));
                }
            }
            let deferred: Vec<DeferredMatrix<RowMajorMatrix<Goldilocks>>> =
                (0..resident.len()).map(|_| None).collect();
            let deferred_dimensions = vec![None; resident.len()];
            let digests = hash_host_only_height_groups(
                &host,
                &resident.iter().map(Option::as_ref).collect::<Vec<_>>(),
                &deferred_dimensions,
                &std::collections::BTreeSet::new(),
                self.leaf_domain,
            );
            let retained = (0..resident.len()).map(|_| None).collect();
            return self.commit_cuda_hybrid(resident, host, deferred, retained, digests);
        }
        let matrix_count = ldes.len();
        self.commit_cuda_hybrid(
            ldes.into_iter().map(Some).collect(),
            (0..matrix_count).map(|_| None).collect(),
            (0..matrix_count).map(|_| None).collect(),
            (0..matrix_count).map(|_| None).collect(),
            Vec::new(),
        )
    }

    fn commit_cuda_hybrid(
        &self,
        resident: Vec<Option<CudaLde>>,
        host_matrices: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        deferred_matrices: Vec<DeferredMatrix<RowMajorMatrix<Goldilocks>>>,
        retained_traces: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        host_digest_groups: Vec<(usize, Vec<[u8; 32]>)>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        assert_eq!(resident.len(), host_matrices.len());
        assert_eq!(resident.len(), deferred_matrices.len());
        assert_eq!(resident.len(), retained_traces.len());
        assert!(
            resident
                .iter()
                .zip(&host_matrices)
                .zip(&deferred_matrices)
                .all(|((gpu, cpu), deferred)| usize::from(gpu.is_some())
                    + usize::from(cpu.is_some())
                    + usize::from(deferred.is_some())
                    == 1),
            "every hybrid matrix must have exactly one storage backend"
        );
        let deferred_dimensions = deferred_matrices
            .iter()
            .map(|deferred| deferred.as_ref().map(|(dimensions, _)| *dimensions))
            .collect::<Vec<_>>();
        let dimensions = resident
            .iter()
            .zip(&host_matrices)
            .zip(&deferred_dimensions)
            .map(|((resident, host), deferred)| {
                resident.as_ref().map_or_else(
                    || {
                        host.as_ref()
                            .map_or_else(|| deferred.unwrap(), Matrix::dimensions)
                    },
                    |lde| Dimensions {
                        width: lde.width(),
                        height: lde.height(),
                    },
                )
            })
            .collect::<Vec<_>>();
        let resident_refs = resident.iter().map(Option::as_ref).collect::<Vec<_>>();
        let host_refs = host_matrices.iter().map(Option::as_ref).collect::<Vec<_>>();
        let tree = CudaMixedMerkleTree::from_hybrid_with_domain(
            self.device_id,
            &resident_refs,
            &host_refs,
            &deferred_dimensions,
            &host_digest_groups,
            self.is_domain_v6(),
        );
        let commitment = MerkleCap::new(vec![tree.root()]);
        let committed_matrices = host_matrices
            .into_iter()
            .map(|matrix| {
                let cell = std::sync::OnceLock::new();
                if let Some(matrix) = matrix {
                    cell.set(matrix).expect("fresh hybrid matrix cell");
                }
                cell
            })
            .collect();
        let deferred_matrices = deferred_matrices
            .into_iter()
            .map(|deferred| deferred.map(|(_, worker)| std::sync::Mutex::new(Some(worker))))
            .collect();
        let resident_active = resident
            .iter()
            .map(|lde| std::sync::atomic::AtomicBool::new(lde.is_some()))
            .collect();
        let count = dimensions.len();
        (
            commitment,
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                materialize: Box::new(CudaLde::to_row_major_matrix),
                materialize_spilled: Box::new(SpilledMatrix::read_all),
                committed_matrices,
                spilled_matrices: (0..count).map(|_| std::sync::OnceLock::new()).collect(),
                deferred_matrices,
                dimensions,
                retained_traces,
                spilled_traces: std::sync::Mutex::new(Vec::new()),
                tree: HybridMerkleTree::Device(tree),
            },
        )
    }

    fn commit_cuda_mixed_spilled(
        &self,
        resident: Vec<Option<CudaLde>>,
        host_matrices: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        spilled_matrices: Vec<Option<SpilledMatrix>>,
        mut prehashed: Vec<Option<Vec<[u8; 32]>>>,
        retained_traces: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        spilled_traces: Vec<Option<SpilledMatrix>>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        let count = resident.len();
        assert_eq!(host_matrices.len(), count);
        assert_eq!(spilled_matrices.len(), count);
        assert_eq!(retained_traces.len(), count);
        if prehashed.is_empty() {
            prehashed = vec![None; count];
        }
        assert_eq!(prehashed.len(), count);

        let dimensions: Vec<Dimensions> = (0..count)
            .map(|i| {
                let backends = usize::from(resident[i].is_some())
                    + usize::from(host_matrices[i].is_some())
                    + usize::from(spilled_matrices[i].is_some());
                assert_eq!(
                    backends, 1,
                    "matrix {i} must have exactly one storage backend (resident, host, or spilled)"
                );
                if let Some(lde) = &resident[i] {
                    Dimensions {
                        width: lde.width(),
                        height: lde.height(),
                    }
                } else if let Some(mat) = &host_matrices[i] {
                    mat.dimensions()
                } else {
                    spilled_matrices[i].as_ref().unwrap().dimensions()
                }
            })
            .collect();
        let any_spilled = spilled_matrices.iter().any(Option::is_some);
        let max_height = hybrid_max_height(&dimensions);
        let wide_heights = host_hashed_heights(dimensions.iter().copied());
        let (free_bytes, _) = super::device_memory_info(self.device_id);
        let tree_vram_bytes = max_height.saturating_mul(96);
        let can_use_device_tree = !any_spilled
            && wide_heights.is_empty()
            && self.cap_height == 0
            && tree_vram_bytes.saturating_add(super::minimum_free_bytes()) <= free_bytes;

        let tree = if can_use_device_tree {
            let resident_refs: Vec<Option<&CudaLde>> =
                resident.iter().map(Option::as_ref).collect();
            let host_refs: Vec<Option<&RowMajorMatrix<Goldilocks>>> =
                host_matrices.iter().map(Option::as_ref).collect();
            let deferred_dims = vec![None; count];
            let host_digest_groups = hash_host_only_height_groups(
                &host_matrices,
                &resident_refs,
                &deferred_dims,
                &std::collections::BTreeSet::new(),
                self.leaf_domain,
            );
            HybridMerkleTree::Device(CudaMixedMerkleTree::from_hybrid_with_domain(
                self.device_id,
                &resident_refs,
                &host_refs,
                &deferred_dims,
                &host_digest_groups,
                self.is_domain_v6(),
            ))
        } else {
            let heights: Vec<usize> = dimensions.iter().map(|d| d.height).collect();
            let leaf_domain = self.leaf_domain;
            let device_id = self.device_id;
            let domain_v6 = self.is_domain_v6();
            let digests = build_merkle_digests_from_height_hashes(
                &heights,
                |h, group| {
                    if let &[single_idx] = group
                        && let Some(cached) = prehashed[single_idx].take()
                    {
                        debug_assert_eq!(cached.len(), h);
                        return cached;
                    }
                    let total_row_bytes: usize = group
                        .iter()
                        .map(|&idx| dimensions[idx].width * size_of::<Goldilocks>())
                        .sum();
                    let all_resident = group.iter().all(|&idx| resident[idx].is_some());
                    if all_resident
                        && total_row_bytes <= MAX_DEVICE_LEAF_ROW_BYTES
                        && h.saturating_mul(32)
                            .saturating_add(super::minimum_free_bytes())
                            <= super::device_memory_info(device_id).0
                    {
                        let res_refs: Vec<Option<&CudaLde>> =
                            group.iter().map(|&idx| resident[idx].as_ref()).collect();
                        let host_refs: Vec<Option<&RowMajorMatrix<Goldilocks>>> =
                            vec![None; group.len()];
                        return CudaMixedMerkleTree::hash_hybrid_height_group_with_domain(
                            device_id, &res_refs, &host_refs, domain_v6,
                        );
                    }
                    let block_rows = (STREAM_BLOCK_BYTES / total_row_bytes.max(size_of::<u64>()))
                        .clamp(1, 1 << 14)
                        .min(h.max(1));
                    // SAFETY: `hash_raw_multi_rows_uninit` initializes every element of `dst`.
                    unsafe {
                        blake3_simd::alloc_and_fill_digests(h, h, |dst| {
                            for start in (0..h).step_by(block_rows) {
                                let n_rows = (h - start).min(block_rows);
                                let blocks: Vec<(Vec<u8>, usize)> = group
                                    .iter()
                                    .map(|&idx| {
                                        let row_bytes =
                                            dimensions[idx].width * size_of::<Goldilocks>();
                                        let raw = if let Some(sp) = &spilled_matrices[idx] {
                                            sp.read_raw_rows(start, n_rows)
                                        } else if let Some(mat) = &host_matrices[idx] {
                                            pack_host_matrix_rows(mat, start, n_rows)
                                        } else {
                                            let lde = resident[idx].as_ref().unwrap();
                                            let mut words = vec![0u64; n_rows * lde.width()];
                                            lde.copy_rows_to_host(start, n_rows, &mut words);
                                            pack_u64_words_canonical_le(&words)
                                        };
                                        (raw, row_bytes)
                                    })
                                    .collect();
                                blake3_simd::hash_raw_multi_rows_uninit(
                                    &blocks,
                                    &mut dst[start..start + n_rows],
                                    leaf_domain,
                                );
                            }
                        })
                    }
                },
                self.compress_domain(),
            );
            HybridMerkleTree::Host(digests)
        };

        let commitment = tree.cap(self.cap_height);
        let committed_matrices = host_matrices
            .into_iter()
            .map(|matrix| {
                let cell = std::sync::OnceLock::new();
                if let Some(matrix) = matrix {
                    cell.set(matrix).expect("fresh hybrid matrix cell");
                }
                cell
            })
            .collect();
        let spilled_cells = spilled_matrices
            .into_iter()
            .map(|sp| {
                let cell = std::sync::OnceLock::new();
                if let Some(sp) = sp {
                    cell.set(sp).ok().expect("fresh spilled matrix cell");
                }
                cell
            })
            .collect();
        let resident_active = resident
            .iter()
            .map(|lde| std::sync::atomic::AtomicBool::new(lde.is_some()))
            .collect();
        (
            commitment,
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                materialize: Box::new(CudaLde::to_row_major_matrix),
                materialize_spilled: Box::new(SpilledMatrix::read_all),
                committed_matrices,
                spilled_matrices: spilled_cells,
                deferred_matrices: (0..count).map(|_| None).collect(),
                dimensions,
                retained_traces,
                spilled_traces: std::sync::Mutex::new(spilled_traces),
                tree,
            },
        )
    }

    fn commit_cuda_storage(
        &self,
        ldes: Vec<RowMajorMatrix<Goldilocks>>,
    ) -> (
        Self::Commitment,
        Self::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        let total_bytes: usize = ldes
            .iter()
            .map(|m| {
                m.height()
                    .saturating_mul(m.width())
                    .saturating_mul(size_of::<Goldilocks>())
            })
            .sum();
        let max_height = ldes.iter().map(Matrix::height).max().unwrap_or(0);
        let tree_workspace_bytes = max_height.saturating_mul(96);
        let (free_bytes, total_device_bytes) = super::device_memory_info(self.device_id);
        let min_free = super::minimum_free_bytes();
        let wide_heights = host_hashed_heights(ldes.iter().map(Matrix::dimensions));
        if total_bytes
            .saturating_add(tree_workspace_bytes)
            .saturating_add(min_free)
            > free_bytes
            || !wide_heights.is_empty()
        {
            if let Some(dir) = &self.spill_dir {
                let mut height_counts = std::collections::HashMap::<usize, usize>::new();
                for lde in &ldes {
                    *height_counts.entry(lde.height()).or_insert(0) += 1;
                }
                let mut pack = SpillPackWriter::create(dir);
                let mut spilled = Vec::with_capacity(ldes.len());
                let mut prehashed = Vec::with_capacity(ldes.len());
                for lde in ldes {
                    if height_counts[&lde.height()] == 1 {
                        let (sp, digests) = pack.append_matrix_and_hash(&lde, self.leaf_domain);
                        spilled.push(Some(sp));
                        prehashed.push(Some(digests));
                    } else {
                        spilled.push(Some(pack.append_matrix(&lde)));
                        prehashed.push(None);
                    }
                }
                pack.flush();
                let count = spilled.len();
                return self.commit_cuda_mixed_spilled(
                    (0..count).map(|_| None).collect(),
                    (0..count).map(|_| None).collect(),
                    spilled,
                    prehashed,
                    (0..count).map(|_| None).collect(),
                    Vec::new(),
                );
            }
            return self.commit_cpu_storage(ldes);
        }
        let resident = ldes
            .iter()
            .map(|matrix| CudaLde::from_row_major_matrix(self.device_id, matrix))
            .collect();
        if self.spill_dir.is_some() && total_bytes >= total_device_bytes / 8 {
            return self.commit_cuda_spillable(resident);
        }
        let (commitment, mut data) = self.commit_cuda_resident(resident);
        if let CudaMmcsData::Cuda {
            committed_matrices, ..
        } = &mut data
        {
            let _ = committed_matrices.set(ldes);
        }
        (commitment, data)
    }
}

pub(crate) fn pack_host_matrix_rows(
    mat: &RowMajorMatrix<Goldilocks>,
    start_row: usize,
    num_rows: usize,
) -> Vec<u8> {
    let width = mat.width();
    let elems = &mat.values[start_row * width..(start_row + num_rows) * width];
    let mut out = vec![0u8; elems.len() * size_of::<u64>()];
    if elems.len() >= 4096 {
        out.par_chunks_exact_mut(8)
            .zip(elems.par_iter())
            .for_each(|(dst, elem)| {
                dst.copy_from_slice(&elem.as_canonical_u64().to_le_bytes());
            });
    } else {
        for (dst, elem) in out.chunks_exact_mut(8).zip(elems) {
            dst.copy_from_slice(&elem.as_canonical_u64().to_le_bytes());
        }
    }
    out
}

pub(crate) fn pack_u64_words_canonical_le(words: &[u64]) -> Vec<u8> {
    let mut out = vec![0u8; words.len() * size_of::<u64>()];
    if words.len() >= 4096 {
        out.par_chunks_exact_mut(8)
            .zip(words.par_iter())
            .for_each(|(dst, &w)| {
                dst.copy_from_slice(&Goldilocks::new(w).as_canonical_u64().to_le_bytes());
            });
    } else {
        for (dst, &w) in out.chunks_exact_mut(8).zip(words) {
            dst.copy_from_slice(&Goldilocks::new(w).as_canonical_u64().to_le_bytes());
        }
    }
    out
}

impl Mmcs<Goldilocks> for CudaMmcs {
    type ProverData<M> = CudaMmcsData<M>;
    type Commitment = MerkleCap<Goldilocks, [u8; 32]>;
    type Proof = Vec<[u8; 32]>;
    type MultiProof = <CpuMmcs as Mmcs<Goldilocks>>::MultiProof;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<Goldilocks>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        // Small commitments stay on the CPU, and so does one with a height
        // group wider than the device leaf kernel hashes (32 KiB per row);
        // the CPU MMCS is the reference the device tree reproduces.
        let device_hashable = host_hashed_heights(inputs.iter().map(|matrix| Dimensions {
            width: matrix.width(),
            height: matrix.height(),
        }))
        .is_empty();
        let total_cells: usize = inputs
            .iter()
            .map(|matrix| matrix.height().saturating_mul(matrix.width()))
            .sum();
        let total_bytes = total_cells.saturating_mul(size_of::<Goldilocks>());
        let max_height = inputs.iter().map(Matrix::height).max().unwrap_or(0);
        let tree_workspace_bytes = max_height.saturating_mul(96);
        let (free_bytes, _) = super::device_memory_info(self.device_id);
        if device_hashable
            && total_cells > 1 << 18
            && total_bytes
                .saturating_add(tree_workspace_bytes)
                .saturating_add(super::minimum_free_bytes())
                <= free_bytes
        {
            let resident: Vec<_> = inputs
                .iter()
                .map(|matrix| {
                    let values = (0..matrix.height())
                        .flat_map(|row| matrix.row(row).unwrap())
                        .collect();
                    CudaLde::from_row_major_matrix(
                        self.device_id,
                        &RowMajorMatrix::new(values, matrix.width()),
                    )
                })
                .collect();
            let resident = std::sync::Arc::new(resident);
            let tree = CudaMixedMerkleTree::from_ldes_with_domain(
                self.device_id,
                &resident,
                self.is_domain_v6(),
            );
            let commitment = MerkleCap::new(vec![tree.root()]);
            let committed_matrices = std::sync::OnceLock::new();
            committed_matrices
                .set(inputs)
                .ok()
                .expect("fresh CUDA matrix cell");
            return (
                commitment,
                CudaMmcsData::Cuda {
                    resident,
                    materialize: None,
                    committed_matrices,
                    retained_traces: std::sync::OnceLock::new(),
                    tree,
                },
            );
        }
        let (commitment, data) = self.cpu.commit(inputs);
        (commitment, CudaMmcsData::Cpu(data))
    }

    fn open_batch<M: Matrix<Goldilocks>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<Goldilocks, Self> {
        match prover_data {
            CudaMmcsData::Cpu(data) => {
                let opening = self.cpu.open_batch(index, data);
                BatchOpening::new(opening.opened_values, opening.opening_proof)
            }
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                dimensions,
                tree,
                ..
            } => BatchOpening::new(
                hybrid_open_row(
                    resident,
                    resident_active,
                    committed_matrices,
                    spilled_matrices,
                    deferred_matrices,
                    dimensions,
                    index,
                ),
                tree.open_siblings(index, self.cap_height),
            ),
            CudaMmcsData::Cuda { resident, tree, .. } => {
                let opened_values = mixed_lde_open_row(resident, index);
                BatchOpening::new(opened_values, tree.open_siblings(index))
            }
        }
    }

    fn get_matrices<'a, M: Matrix<Goldilocks>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        match prover_data {
            CudaMmcsData::Cpu(data) => self.cpu.get_matrices(data),
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                materialize,
                materialize_spilled,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                ..
            } => resident
                .iter()
                .enumerate()
                .map(|(index, resident)| {
                    if resident.is_some()
                        && resident_active[index].load(std::sync::atomic::Ordering::Acquire)
                    {
                        committed_matrices[index]
                            .get_or_init(|| materialize(resident.as_ref().unwrap()))
                    } else if let Some(sp) = spilled_matrices[index].get() {
                        committed_matrices[index].get_or_init(|| materialize_spilled(sp))
                    } else {
                        hybrid_matrix(committed_matrices, deferred_matrices, index)
                    }
                })
                .collect(),
            CudaMmcsData::Cuda {
                committed_matrices,
                materialize,
                ..
            } => committed_matrices
                .get_or_init(|| {
                    materialize
                        .as_ref()
                        .expect("CUDA matrices have no materializer")()
                })
                .iter()
                .collect(),
        }
    }

    fn get_matrix_heights<M: Matrix<Goldilocks>>(
        &self,
        prover_data: &Self::ProverData<M>,
    ) -> Vec<usize> {
        match prover_data {
            CudaMmcsData::Cpu(data) => self.cpu.get_matrix_heights(data),
            CudaMmcsData::Hybrid { dimensions, .. } => dimensions
                .iter()
                .map(|dimensions| dimensions.height)
                .collect(),
            CudaMmcsData::Cuda { resident, .. } => resident.iter().map(CudaLde::height).collect(),
        }
    }

    fn get_max_height<M: Matrix<Goldilocks>>(&self, prover_data: &Self::ProverData<M>) -> usize {
        match prover_data {
            CudaMmcsData::Cpu(data) => self.cpu.get_max_height(data),
            CudaMmcsData::Hybrid { dimensions, .. } => hybrid_max_height(dimensions),
            CudaMmcsData::Cuda { resident, .. } => {
                resident.iter().map(CudaLde::height).max().unwrap()
            }
        }
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        index: usize,
        batch_opening: BatchOpeningRef<'_, Goldilocks, Self>,
    ) -> Result<(), Self::Error> {
        verify_merkle_cap_len(self.cap_height(), commit, dimensions)?;
        self.cpu.verify_batch(
            commit,
            dimensions,
            index,
            BatchOpeningRef::new(batch_opening.opened_values, batch_opening.opening_proof),
        )
    }

    fn open_multi_batch<M: Matrix<Goldilocks>>(
        &self,
        indices: &[usize],
        prover_data: &Self::ProverData<M>,
    ) -> (Vec<Vec<Vec<Goldilocks>>>, Self::MultiProof) {
        match prover_data {
            CudaMmcsData::Cpu(data) => self.cpu.open_multi_batch(indices, data),
            CudaMmcsData::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                deferred_matrices,
                dimensions,
                tree,
                ..
            } => {
                let opened_values = hybrid_open_rows(
                    resident,
                    resident_active,
                    committed_matrices,
                    spilled_matrices,
                    deferred_matrices,
                    dimensions,
                    indices,
                );
                let opening_proof = tree.open_pruned_siblings(indices, self.cap_height);
                (opened_values, opening_proof)
            }
            CudaMmcsData::Cuda { resident, tree, .. } => {
                let opened_values = if indices.is_empty() {
                    Vec::new()
                } else {
                    mixed_lde_open_rows(resident, indices)
                };
                let opening_proof = tree.open_pruned_siblings(indices);
                (opened_values, opening_proof)
            }
        }
    }

    fn verify_multi_batch<R: AsRef<[Goldilocks]> + PartialEq>(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        indices: &[usize],
        opened_values: &[Vec<R>],
        proof: &Self::MultiProof,
    ) -> Result<(), Self::Error> {
        verify_merkle_cap_len(self.cap_height(), commit, dimensions)?;
        self.cpu
            .verify_multi_batch(commit, dimensions, indices, opened_values, proof)
    }
}

impl CapValidatingMmcs<Goldilocks> for CudaMmcs {
    fn validate_commitment_cap_for_log_height(
        &self,
        commit: &Self::Commitment,
        log_max_height: usize,
    ) -> Result<(), Self::Error> {
        verify_merkle_cap_len_for_log_height(self.cap_height(), commit, log_max_height)
    }
    fn empty_multi_proof() -> Self::MultiProof {
        PrunedMerklePaths {
            sibling_hashes: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_commit::Mmcs;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    fn matrix(height: usize, width: usize, offset: usize) -> RowMajorMatrix<Goldilocks> {
        RowMajorMatrix::new(
            (0..height * width)
                .map(|index| Goldilocks::from_usize(offset + index))
                .collect(),
            width,
        )
    }

    #[test]
    fn wide_height_groups_are_hashed_on_the_host() {
        let d = |width, height| Dimensions { width, height };
        // 4096 columns of 8 bytes is exactly the 32 KiB the leaf kernel takes.
        assert!(host_hashed_heights([d(4096, 8)]).is_empty());
        assert_eq!(
            host_hashed_heights([d(4097, 8)])
                .into_iter()
                .collect::<Vec<_>>(),
            vec![8]
        );
        // Matrices at one height share a leaf row, so their widths add up;
        // other heights are judged on their own.
        assert_eq!(
            host_hashed_heights([d(3000, 16), d(1500, 16), d(9282, 4), d(10, 4), d(14, 4096)])
                .into_iter()
                .collect::<Vec<_>>(),
            vec![4, 16]
        );
    }

    /// The dimensions of the Aiur BLAKE3 hashing test's stage-one traces at
    /// size 64: the height-4 group is 9,731 columns wide, 78 KB per leaf row.
    #[test]
    fn resident_commit_with_a_wide_height_group_matches_the_cpu() {
        let dims = [
            (4096, 14),
            (2048, 14),
            (4096, 17),
            (4, 37),
            (4, 35),
            (4, 371),
            (4, 9282),
            (256, 110),
            (4, 6),
            (1024, 3),
            (262144, 10),
        ];
        let matrices: Vec<_> = dims
            .iter()
            .enumerate()
            .map(|(i, &(height, width))| matrix(height, width, 7 * i + 1))
            .collect();
        let cpu = CpuMmcs::new(
            SerializingHasher::new(DomainBlake3::new(Blake3Domain::Plain)),
            DomainCompressionFunction::new(DomainBlake3::new(Blake3Domain::Plain)),
            0,
        );
        let (expected_commitment, expected_data) = cpu.commit(matrices.clone());
        let indices = [0, 3, 1000, 262143];
        let expected_openings: Vec<_> = indices
            .iter()
            .map(|&i| cpu.open_batch(i, &expected_data))
            .collect();
        let mmcs = CudaMmcs::with_device(cpu, 0);
        let ldes = matrices
            .iter()
            .map(|m| CudaLde::from_row_major_matrix(mmcs.device_id, m))
            .collect();
        let (commitment, data) = mmcs.commit_cuda_resident(ldes);
        assert_eq!(commitment, expected_commitment);
        for (&index, expected) in indices.iter().zip(&expected_openings) {
            let opening = mmcs.open_batch(index, &data);
            assert_eq!(opening.opened_values, expected.opened_values);
        }
    }

    #[test]
    fn hybrid_openings_survive_device_spill() {
        let matrices = vec![matrix(16, 2, 3), matrix(8, 3, 71), matrix(16, 1, 109)];
        let cpu = CpuMmcs::new(
            SerializingHasher::new(DomainBlake3::new(Blake3Domain::Plain)),
            DomainCompressionFunction::new(DomainBlake3::new(Blake3Domain::Plain)),
            0,
        );
        let (expected_commitment, expected_data) = cpu.commit(matrices.clone());
        let expected_opening = cpu.open_batch(5, &expected_data);

        let mmcs = CudaMmcs::with_device(cpu, 0);
        let resident = vec![
            Some(CudaLde::from_row_major_matrix(mmcs.device_id, &matrices[0])),
            None,
            None,
        ];
        let host_matrices = vec![None, Some(matrices[1].clone()), Some(matrices[2].clone())];
        let host_digest_groups = hash_host_only_height_groups(
            &host_matrices,
            &resident.iter().map(Option::as_ref).collect::<Vec<_>>(),
            &[None, None, None],
            &std::collections::BTreeSet::new(),
            Blake3Domain::Plain,
        );
        let retained_traces = vec![None, None, None];
        let deferred_matrices = vec![None, None, None];
        let (commitment, data) = mmcs.commit_cuda_hybrid(
            resident,
            host_matrices,
            deferred_matrices,
            retained_traces,
            host_digest_groups,
        );
        assert_eq!(commitment, expected_commitment);

        let resident_opening = mmcs.open_batch(5, &data);
        assert_eq!(
            resident_opening.opened_values,
            expected_opening.opened_values
        );
        assert_eq!(
            resident_opening.opening_proof,
            expected_opening.opening_proof
        );

        mmcs.ensure_device_headroom(&data, usize::MAX, None, "test");
        assert!(!(0..matrices.len()).any(|index| mmcs.is_matrix_cuda_resident(&data, index)));
        let spilled_opening = mmcs.open_batch(5, &data);
        assert_eq!(
            spilled_opening.opened_values,
            expected_opening.opened_values
        );
        assert_eq!(
            spilled_opening.opening_proof,
            expected_opening.opening_proof
        );
    }
}
