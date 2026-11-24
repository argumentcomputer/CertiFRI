//! CUDA hiding MMCS (`v6-zk`) using on-the-fly BLAKE3-CTR leaf salting with
//! zero salt-matrix VRAM or RAM storage.
//!
//! Matches the wire format, leaf-salt derivation (`derive_leaf_salt`),
//! `ZkMerkleLeaf` / `ZkMerkleCompress` domain separation, and `C2` exact
//! `MerkleCap` root-count validation of the CPU hiding MMCS byte-for-byte.

use core::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use itertools::Itertools;
use p3_commit::{BatchOpening, BatchOpeningRef, ExtensionMmcs, Mmcs};
use p3_field::{ExtensionField, PrimeField64};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
use p3_maybe_rayon::prelude::*;
use p3_merkle_tree::{MerkleTreeError, PrunedMerklePaths};
use p3_symmetric::MerkleCap;
use p3_util::log2_ceil_usize;

use super::mmcs::{CudaMatrixSource, HybridMerkleTree};
use super::{
    CudaLde, CudaMixedMerkleTree, mixed_lde_open_row, mixed_lde_open_row_at_height,
    mixed_lde_open_rows, mixed_lde_open_rows_at_height,
};
use crate::p3_adapter::blake3_simd;
use crate::p3_adapter::cap::{CapValidatingMmcs, verify_merkle_cap_len_for_log_height};
use crate::p3_adapter::domain_blake3::Blake3Domain;
use crate::p3_adapter::spill::{
    STREAM_BLOCK_BYTES, SpillPackWriter, SpilledMatrix, build_merkle_digests_from_height_hashes,
};
use crate::p3_adapter::zk::{
    HidingBatchProof, HidingMultiProof, ZK_LEAF_SALT_BYTES, derive_leaf_salt,
    open_hiding_batch_salts, open_hiding_multi_salts, random_seed, verify_hiding_batch,
    verify_hiding_multi_batch,
};

/// Maximum concatenated leaf row payload (in bytes, excluding the 16-byte leaf
/// salt) that the device BLAKE3 leaf kernel hashes directly in a 32 KiB chunk
/// tree (`4094` Goldilocks columns + `2` `u64` salt words = `32 KiB`).
pub(crate) const MAX_DEVICE_LEAF_ROW_BYTES_ZK: usize = 32 * 1024 - ZK_LEAF_SALT_BYTES;

/// Returns heights whose concatenated leaf payload exceeds
/// [`MAX_DEVICE_LEAF_ROW_BYTES_ZK`] and therefore must be salted and hashed on
/// the host before entering the CUDA Merkle tree as pre-hashed digest groups.
pub(crate) fn host_hashed_heights_zk(
    dimensions: impl IntoIterator<Item = Dimensions>,
) -> BTreeSet<usize> {
    let mut row_bytes = BTreeMap::<usize, usize>::new();
    for dims in dimensions {
        *row_bytes.entry(dims.height).or_default() += dims.width * size_of::<Goldilocks>();
    }
    row_bytes
        .into_iter()
        .filter(|(_, bytes)| *bytes > MAX_DEVICE_LEAF_ROW_BYTES_ZK)
        .map(|(height, _)| height)
        .collect()
}

#[inline]
fn padded_len_binary(len: usize) -> usize {
    if len <= 1 { 1 } else { len.next_power_of_two() }
}

#[inline]
fn compress_pair(compress_domain: Blake3Domain, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut block = [0u8; 64];
    block[..32].copy_from_slice(left);
    block[32..].copy_from_slice(right);
    compress_domain.hash_bytes(&block)
}

fn hash_group_salted<M: Matrix<Goldilocks>>(
    matrices: &[&M],
    height: usize,
    salt_seed: &[u8; 32],
    leaf_domain: Blake3Domain,
) -> Vec<[u8; 32]> {
    (0..height)
        .into_par_iter()
        .map(|row| {
            let mut hasher = leaf_domain.hasher();
            for matrix in matrices {
                for elem in matrix.row(row).unwrap() {
                    hasher.update(&elem.as_canonical_u64().to_le_bytes());
                }
            }
            let salt = derive_leaf_salt(salt_seed, height, row);
            hasher.update(&salt);
            hasher.finalize().into()
        })
        .collect()
}

/// CPU salted binary BLAKE3 Merkle tree used for small commitments, wide height
/// groups, and CPU fallback FRI rounds. Stores only the 32-byte `salt_seed`.
struct CpuHidingTree<M> {
    leaves: Vec<M>,
    digest_layers: Vec<Vec<[u8; 32]>>,
    salt_seed: [u8; 32],
}

impl<M: Matrix<Goldilocks>> CpuHidingTree<M> {
    fn build(
        leaves: Vec<M>,
        leaf_domain: Blake3Domain,
        compress_domain: Blake3Domain,
        salt_seed: [u8; 32],
    ) -> Self {
        assert!(!leaves.is_empty(), "No matrices given?");
        let max_height = leaves
            .iter()
            .map(Matrix::height)
            .max()
            .expect("No matrices given?");
        assert!(max_height > 0, "matrix height must be positive");
        let log_max_height = log2_ceil_usize(max_height);
        for matrix in &leaves {
            let h = matrix.height();
            assert!(h > 0, "matrix height must be positive");
            let bits_reduced = log_max_height - log2_ceil_usize(h);
            let expected = ((max_height - 1) >> bits_reduced) + 1;
            assert_eq!(
                h, expected,
                "incompatible matrix height {h} for max_height {max_height}"
            );
        }

        let mut order: Vec<usize> = (0..leaves.len()).collect();
        order.sort_by_key(|&idx| Reverse(leaves[idx].height()));

        let tallest_end = order
            .iter()
            .take_while(|&&idx| leaves[idx].height() == max_height)
            .count();
        let tallest_refs: Vec<&M> = order[..tallest_end].iter().map(|&i| &leaves[i]).collect();
        let mut first_layer = hash_group_salted(&tallest_refs, max_height, &salt_seed, leaf_domain);
        first_layer.resize(padded_len_binary(max_height), [0u8; 32]);

        let mut digest_layers = vec![first_layer];
        let mut cursor = tallest_end;

        loop {
            let prev_layer = digest_layers.last().unwrap().as_slice();
            if prev_layer.len() <= 1 {
                break;
            }
            let raw_next = prev_layer.len() / 2;
            let next_layer_len = raw_next.next_power_of_two();

            let inject_start = cursor;
            while cursor < order.len()
                && leaves[order[cursor]].height().next_power_of_two() == next_layer_len
            {
                cursor += 1;
            }
            let inject_group = &order[inject_start..cursor];

            let mut next_digests: Vec<[u8; 32]> = if inject_group.is_empty() {
                (0..raw_next)
                    .into_par_iter()
                    .map(|i| {
                        compress_pair(compress_domain, &prev_layer[2 * i], &prev_layer[2 * i + 1])
                    })
                    .collect()
            } else {
                let inject_refs: Vec<&M> = inject_group.iter().map(|&i| &leaves[i]).collect();
                let inject_height = inject_refs[0].height();
                let injected =
                    hash_group_salted(&inject_refs, inject_height, &salt_seed, leaf_domain);
                let zero = [0u8; 32];
                (0..raw_next)
                    .into_par_iter()
                    .map(|i| {
                        let parent = compress_pair(
                            compress_domain,
                            &prev_layer[2 * i],
                            &prev_layer[2 * i + 1],
                        );
                        let leaf = if i < inject_height {
                            &injected[i]
                        } else {
                            &zero
                        };
                        compress_pair(compress_domain, &parent, leaf)
                    })
                    .collect()
            };
            next_digests.resize(padded_len_binary(raw_next), [0u8; 32]);
            digest_layers.push(next_digests);
        }

        Self {
            leaves,
            digest_layers,
            salt_seed,
        }
    }

    fn cap(&self, cap_height: usize) -> MerkleCap<Goldilocks, [u8; 32]> {
        let num_levels = self.digest_layers.len().saturating_sub(1);
        let effective_cap = cap_height.min(num_levels);
        let cap_layer = &self.digest_layers[num_levels - effective_cap];
        MerkleCap::new(cap_layer[..(1usize << effective_cap)].to_vec())
    }

    fn max_height(&self) -> usize {
        self.leaves
            .iter()
            .map(Matrix::height)
            .max()
            .expect("No committed matrices?")
    }

    fn matrix_heights(&self) -> Vec<usize> {
        self.leaves.iter().map(Matrix::height).collect()
    }

    #[allow(dead_code)]
    fn dimensions(&self) -> Vec<Dimensions> {
        self.leaves.iter().map(Matrix::dimensions).collect()
    }

    fn open_single_proof(&self, index: usize, cap_height: usize) -> Vec<[u8; 32]> {
        let num_levels = self.digest_layers.len().saturating_sub(1);
        let effective_cap = cap_height.min(num_levels);
        let proof_levels = num_levels - effective_cap;
        let mut siblings = Vec::with_capacity(proof_levels);
        let mut pos = index;
        for layer in &self.digest_layers[..proof_levels] {
            siblings.push(layer[pos ^ 1]);
            pos >>= 1;
        }
        siblings
    }

    fn open_multi_proof(&self, indices: &[usize], cap_height: usize) -> PrunedMerklePaths<u8, 32> {
        if indices.is_empty() {
            return PrunedMerklePaths {
                sibling_hashes: Vec::new(),
            };
        }
        let num_levels = self.digest_layers.len().saturating_sub(1);
        let effective_cap = cap_height.min(num_levels);
        let proof_levels = num_levels - effective_cap;
        let mut frontier: Vec<usize> = indices.to_vec();
        frontier.sort_unstable();
        frontier.dedup();
        let mut parents = Vec::with_capacity(frontier.len());
        let mut sibling_hashes = Vec::new();
        for layer in &self.digest_layers[..proof_levels] {
            parents.clear();
            let mut at = 0;
            while at < frontier.len() {
                let first = frontier[at];
                let parent = first >> 1;
                let group_start = at;
                at += 1;
                while at < frontier.len() && (frontier[at] >> 1) == parent {
                    at += 1;
                }
                if at - group_start == 1 {
                    sibling_hashes.push(layer[first ^ 1]);
                }
                parents.push(parent);
            }
            core::mem::swap(&mut frontier, &mut parents);
        }
        PrunedMerklePaths { sibling_hashes }
    }

    fn open_batch(
        &self,
        index: usize,
        cap_height: usize,
    ) -> (Vec<Vec<Goldilocks>>, HidingBatchProof) {
        let heights = self.matrix_heights();
        let max_height = self.max_height();
        assert!(
            index < max_height,
            "index {index} out of bounds for height {max_height}"
        );
        let log_max_height = log2_ceil_usize(max_height);
        let opened_values = self
            .leaves
            .iter()
            .map(|matrix| {
                let bits_reduced = log_max_height - log2_ceil_usize(matrix.height());
                matrix
                    .row(index >> bits_reduced)
                    .unwrap()
                    .into_iter()
                    .collect()
            })
            .collect();
        let siblings = self.open_single_proof(index, cap_height);
        let salts = open_hiding_batch_salts(&self.salt_seed, &heights, index, cap_height);
        (opened_values, HidingBatchProof { salts, siblings })
    }

    fn open_multi_batch(
        &self,
        indices: &[usize],
        cap_height: usize,
    ) -> (Vec<Vec<Vec<Goldilocks>>>, HidingMultiProof) {
        let heights = self.matrix_heights();
        let max_height = self.max_height();
        let log_max_height = log2_ceil_usize(max_height);
        let opened_values = indices
            .iter()
            .map(|&index| {
                assert!(
                    index < max_height,
                    "index {index} out of bounds for height {max_height}"
                );
                self.leaves
                    .iter()
                    .map(|matrix| {
                        let bits_reduced = log_max_height - log2_ceil_usize(matrix.height());
                        matrix
                            .row(index >> bits_reduced)
                            .unwrap()
                            .into_iter()
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let pruned = self.open_multi_proof(indices, cap_height);
        let salts = open_hiding_multi_salts(&self.salt_seed, &heights, indices, cap_height);
        (opened_values, HidingMultiProof { salts, pruned })
    }
}

/// Prover data for [`HidingCudaMmcs`], storing only a 32-byte `salt_seed`
/// alongside the committed matrices and Merkle tree (zero salt-matrix memory
/// or VRAM overhead).
pub struct HidingCudaMmcsData<M>(HidingCudaMmcsDataInner<M>);

enum HidingCudaMmcsDataInner<M> {
    Cpu(CpuHidingTree<M>),
    Hybrid {
        resident: Vec<Option<CudaLde>>,
        resident_active: Vec<AtomicBool>,
        materialize: Box<dyn Fn(&CudaLde) -> M + Send + Sync>,
        materialize_spilled: Box<dyn Fn(&SpilledMatrix) -> M + Send + Sync>,
        committed_matrices: Vec<OnceLock<M>>,
        spilled_matrices: Vec<OnceLock<SpilledMatrix>>,
        dimensions: Vec<Dimensions>,
        retained_traces: Mutex<Vec<Option<M>>>,
        spilled_traces: Mutex<Vec<Option<SpilledMatrix>>>,
        tree: HybridMerkleTree,
        salt_seed: [u8; 32],
    },
    Cuda {
        resident: Arc<Vec<CudaLde>>,
        materialize: Option<Box<dyn Fn() -> Vec<M> + Send + Sync>>,
        committed_matrices: OnceLock<Vec<M>>,
        retained_traces: Mutex<Vec<Option<M>>>,
        tree: CudaMixedMerkleTree,
        salt_seed: [u8; 32],
    },
}

impl<M> HidingCudaMmcsData<M> {
    pub(crate) fn spilled_original_trace(&self, index: usize) -> Option<SpilledMatrix> {
        match &self.0 {
            HidingCudaMmcsDataInner::Hybrid { spilled_traces, .. } => spilled_traces
                .lock()
                .expect("hiding spilled_traces lock poisoned")
                .get(index)
                .and_then(Clone::clone),
            HidingCudaMmcsDataInner::Cpu(_) | HidingCudaMmcsDataInner::Cuda { .. } => None,
        }
    }

    pub(crate) fn set_retained_traces(&self, traces: Vec<Option<M>>) {
        match &self.0 {
            HidingCudaMmcsDataInner::Hybrid {
                retained_traces, ..
            }
            | HidingCudaMmcsDataInner::Cuda {
                retained_traces, ..
            } => {
                *retained_traces
                    .lock()
                    .expect("hiding retained_traces lock poisoned") = traces;
            }
            HidingCudaMmcsDataInner::Cpu(_) => {}
        }
    }

    pub(crate) fn release_original_traces(&self) {
        match &self.0 {
            HidingCudaMmcsDataInner::Hybrid {
                retained_traces,
                spilled_traces,
                ..
            } => {
                retained_traces
                    .lock()
                    .expect("hiding retained_traces lock poisoned")
                    .clear();
                spilled_traces
                    .lock()
                    .expect("hiding spilled_traces lock poisoned")
                    .clear();
            }
            HidingCudaMmcsDataInner::Cuda {
                retained_traces, ..
            } => {
                retained_traces
                    .lock()
                    .expect("hiding retained_traces lock poisoned")
                    .clear();
            }
            HidingCudaMmcsDataInner::Cpu(_) => {}
        }
    }
}

impl<M: Clone> HidingCudaMmcsData<M> {
    pub(crate) fn clone_in_memory_original_trace(&self, index: usize) -> Option<M> {
        match &self.0 {
            HidingCudaMmcsDataInner::Hybrid {
                retained_traces, ..
            }
            | HidingCudaMmcsDataInner::Cuda {
                retained_traces, ..
            } => retained_traces
                .lock()
                .expect("hiding retained_traces lock poisoned")
                .get(index)
                .and_then(Clone::clone),
            HidingCudaMmcsDataInner::Cpu(_) => None,
        }
    }
}

/// CUDA-accelerated salted BLAKE3 MMCS for Protocol `v6-zk`.
#[derive(Clone, Debug)]
pub struct HidingCudaMmcs {
    cap_height: usize,
    leaf_domain: Blake3Domain,
    compress_domain: Blake3Domain,
    device_id: i32,
    spill_dir: Option<PathBuf>,
}

impl HidingCudaMmcs {
    /// Creates a Protocol `v6-zk` CUDA hiding MMCS separating salted Merkle
    /// leaf hashing (`ZkMerkleLeaf`) from internal compressions
    /// (`ZkMerkleCompress`).
    pub(crate) fn new_v6_zk(cap_height: usize, device_id: i32) -> Self {
        assert!(device_id >= 0, "CUDA device id must be non-negative");
        assert_eq!(
            cap_height, 0,
            "the CUDA backend currently supports only cap_height = 0"
        );
        Self {
            cap_height,
            leaf_domain: Blake3Domain::ZkMerkleLeaf,
            compress_domain: Blake3Domain::ZkMerkleCompress,
            device_id,
            spill_dir: None,
        }
    }

    pub fn set_spill_dir(&mut self, spill_dir: Option<PathBuf>) {
        self.spill_dir = spill_dir;
    }

    pub fn spill_dir(&self) -> Option<&Path> {
        self.spill_dir.as_deref()
    }

    #[inline]
    pub const fn cap_height(&self) -> usize {
        self.cap_height
    }

    #[inline]
    pub(crate) const fn device_id(&self) -> i32 {
        self.device_id
    }

    #[inline]
    pub(crate) const fn leaf_domain(&self) -> Blake3Domain {
        self.leaf_domain
    }

    #[inline]
    pub(crate) fn is_cuda_resident<M>(&self, data: &HidingCudaMmcsData<M>) -> bool {
        matches!(data.0, HidingCudaMmcsDataInner::Cuda { .. })
    }

    #[inline]
    pub(crate) fn resident_arc<M>(
        &self,
        data: &HidingCudaMmcsData<M>,
    ) -> Option<Arc<Vec<CudaLde>>> {
        match &data.0 {
            HidingCudaMmcsDataInner::Cuda { resident, .. } => Some(Arc::clone(resident)),
            HidingCudaMmcsDataInner::Cpu(_) | HidingCudaMmcsDataInner::Hybrid { .. } => None,
        }
    }

    pub(crate) fn matrix_dimensions<M: Matrix<Goldilocks>>(
        &self,
        data: &HidingCudaMmcsData<M>,
    ) -> Vec<Dimensions> {
        match &data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.dimensions(),
            HidingCudaMmcsDataInner::Hybrid { dimensions, .. } => dimensions.clone(),
            HidingCudaMmcsDataInner::Cuda { resident, .. } => resident
                .iter()
                .map(|lde| Dimensions {
                    width: lde.width(),
                    height: lde.height(),
                })
                .collect(),
        }
    }

    pub(crate) fn spilled_matrices<'a, M>(
        &self,
        data: &'a HidingCudaMmcsData<M>,
    ) -> Vec<Option<&'a SpilledMatrix>> {
        match &data.0 {
            HidingCudaMmcsDataInner::Hybrid {
                spilled_matrices, ..
            } => spilled_matrices.iter().map(OnceLock::get).collect(),
            HidingCudaMmcsDataInner::Cpu(tree) => vec![None; tree.leaves.len()],
            HidingCudaMmcsDataInner::Cuda { resident, .. } => vec![None; resident.len()],
        }
    }

    pub(crate) fn is_matrix_cuda_resident<M>(
        &self,
        data: &HidingCudaMmcsData<M>,
        index: usize,
    ) -> bool {
        match &data.0 {
            HidingCudaMmcsDataInner::Cuda { resident, .. } => index < resident.len(),
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                ..
            } => {
                resident.get(index).is_some_and(Option::is_some)
                    && resident_active
                        .get(index)
                        .is_some_and(|a| a.load(Ordering::Acquire))
            }
            HidingCudaMmcsDataInner::Cpu(_) => false,
        }
    }

    pub(crate) fn with_resident_matrix<M, R>(
        &self,
        data: &HidingCudaMmcsData<M>,
        index: usize,
        f: impl FnOnce(&CudaLde) -> R,
    ) -> R {
        match &data.0 {
            HidingCudaMmcsDataInner::Cuda { resident, .. } => f(&resident[index]),
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                ..
            } => {
                assert!(
                    resident_active[index].load(Ordering::Acquire),
                    "hiding hybrid matrix {index} was evicted from CUDA"
                );
                f(resident[index]
                    .as_ref()
                    .expect("hiding hybrid matrix is not CUDA-resident"))
            }
            HidingCudaMmcsDataInner::Cpu(_) => {
                panic!("attempted to access CPU hiding commitment as CUDA-resident")
            }
        }
    }

    pub(crate) fn cpu_matrices<'a, M: Matrix<Goldilocks>>(
        &self,
        data: &'a HidingCudaMmcsData<M>,
    ) -> Vec<Option<&'a M>> {
        match &data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.leaves.iter().map(Some).collect(),
            HidingCudaMmcsDataInner::Cuda { resident, .. } => vec![None; resident.len()],
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                ..
            } => (0..resident.len())
                .map(|index| {
                    let is_active =
                        resident[index].is_some() && resident_active[index].load(Ordering::Acquire);
                    if is_active || spilled_matrices[index].get().is_some() {
                        None
                    } else {
                        committed_matrices[index].get()
                    }
                })
                .collect(),
        }
    }

    pub(crate) fn with_matrix_source<R>(
        &self,
        data: &HidingCudaMmcsData<RowMajorMatrix<Goldilocks>>,
        index: usize,
        f: impl FnOnce(CudaMatrixSource<'_>) -> R,
    ) -> R {
        match &data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => f(CudaMatrixSource::Host(&tree.leaves[index])),
            HidingCudaMmcsDataInner::Cuda { resident, .. } => {
                f(CudaMatrixSource::Resident(&resident[index]))
            }
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                ..
            } => {
                if let Some(lde) = resident[index].as_ref()
                    && resident_active[index].load(Ordering::Acquire)
                {
                    f(CudaMatrixSource::Resident(lde))
                } else if let Some(spilled) = spilled_matrices[index].get() {
                    f(CudaMatrixSource::Spilled(spilled))
                } else {
                    f(CudaMatrixSource::Host(
                        committed_matrices[index]
                            .get()
                            .expect("hiding hybrid host matrix missing"),
                    ))
                }
            }
        }
    }

    pub(crate) fn ensure_device_headroom_batch<M>(
        &self,
        datas: &[&HidingCudaMmcsData<M>],
        target_free_bytes: usize,
        phase: &str,
    ) -> usize {
        let mut free_bytes = super::device_memory_info(self.device_id).0;
        if free_bytes >= target_free_bytes {
            return free_bytes;
        }
        let mut candidates: Vec<(usize, usize, usize, bool)> = Vec::new();
        for (data_idx, data) in datas.iter().enumerate() {
            if let HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                ..
            } = &data.0
            {
                for (mat_idx, lde) in resident.iter().enumerate() {
                    let Some(lde) = lde.as_ref() else {
                        continue;
                    };
                    if resident_active[mat_idx].load(Ordering::Acquire) {
                        candidates.push((
                            data_idx,
                            mat_idx,
                            lde.height().saturating_mul(lde.width()),
                            committed_matrices[mat_idx].get().is_some()
                                || spilled_matrices[mat_idx].get().is_some(),
                        ));
                    }
                }
            }
        }
        candidates
            .sort_unstable_by_key(|&(_, _, cells, has_copy)| (Reverse(has_copy), Reverse(cells)));
        for (data_idx, mat_idx, _, _) in candidates {
            if free_bytes >= target_free_bytes {
                break;
            }
            if let HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                materialize,
                committed_matrices,
                spilled_matrices,
                ..
            } = &datas[data_idx].0
            {
                let lde = resident[mat_idx]
                    .as_ref()
                    .expect("hiding hybrid resident LDE missing");
                if committed_matrices[mat_idx].get().is_none()
                    && spilled_matrices[mat_idx].get().is_none()
                {
                    let matrix_bytes = lde
                        .height()
                        .saturating_mul(lde.width())
                        .saturating_mul(size_of::<Goldilocks>());
                    if let Some(dir) = self.spill_dir.as_deref()
                        && !super::host_spill_headroom(lde.device_id, matrix_bytes)
                    {
                        let mut pack = SpillPackWriter::create(dir);
                        let sp = lde.spill_to_pack(&mut pack);
                        pack.flush();
                        let _ = spilled_matrices[mat_idx].set(sp);
                    } else {
                        committed_matrices[mat_idx].get_or_init(|| materialize(lde));
                    }
                }
                // SAFETY: eviction runs between proving phases when no CUDA
                // operation accesses this LDE.
                unsafe { lde.release_values() };
                lde.release_generator_device();
                resident_active[mat_idx].store(false, Ordering::Release);
            }
            free_bytes = super::device_memory_info(self.device_id).0;
            if super::memory_diagnostics_enabled() {
                eprintln!(
                    "[multi-stark/cuda] v6-zk {phase}: evicted data[{data_idx}][{mat_idx}], free={free_bytes}/{target_free_bytes}"
                );
            }
        }
        free_bytes
    }

    /// Commits host matrices on CPU using an explicit `salt_seed`.
    pub(crate) fn commit_cpu_with_seed<M: Matrix<Goldilocks>>(
        &self,
        inputs: Vec<M>,
        salt_seed: [u8; 32],
    ) -> (
        <Self as Mmcs<Goldilocks>>::Commitment,
        HidingCudaMmcsData<M>,
    ) {
        let tree = CpuHidingTree::build(inputs, self.leaf_domain, self.compress_domain, salt_seed);
        let commitment = tree.cap(self.cap_height);
        (
            commitment,
            HidingCudaMmcsData(HidingCudaMmcsDataInner::Cpu(tree)),
        )
    }

    /// Commits a mixed set of CUDA-resident, host-resident, and NVMe-spilled
    /// matrices for Protocol `v6-zk` with an explicit `salt_seed`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_cuda_mixed_spilled_with_seed(
        &self,
        resident: Vec<Option<CudaLde>>,
        host_matrices: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        spilled: Vec<Option<SpilledMatrix>>,
        mut prehashed: Vec<Option<Vec<[u8; 32]>>>,
        retained_traces: Vec<Option<RowMajorMatrix<Goldilocks>>>,
        spilled_traces: Vec<Option<SpilledMatrix>>,
        salt_seed: [u8; 32],
    ) -> (
        <Self as Mmcs<Goldilocks>>::Commitment,
        HidingCudaMmcsData<RowMajorMatrix<Goldilocks>>,
    ) {
        let count = resident.len();
        assert!(count > 0, "No matrices given?");
        assert_eq!(host_matrices.len(), count);
        assert_eq!(spilled.len(), count);
        assert_eq!(prehashed.len(), count);

        let mut dimensions = Vec::with_capacity(count);
        let mut any_spilled = false;
        let mut any_host = false;
        for i in 0..count {
            let dims = if let Some(lde) = resident[i].as_ref() {
                Dimensions {
                    width: lde.width(),
                    height: lde.height(),
                }
            } else if let Some(sp) = spilled[i].as_ref() {
                any_spilled = true;
                sp.dimensions()
            } else if let Some(mat) = host_matrices[i].as_ref() {
                any_host = true;
                mat.dimensions()
            } else {
                panic!("v6-zk mixed commit matrix {i} has no backing storage");
            };
            dimensions.push(dims);
        }

        let wide_heights = host_hashed_heights_zk(dimensions.iter().copied());
        let max_height = dimensions.iter().map(|d| d.height).max().unwrap_or(0);
        let tree_workspace_bytes = max_height.saturating_mul(96);
        let (free_bytes, _) = super::device_memory_info(self.device_id);
        let min_free = super::minimum_free_bytes();

        // Pure device fast path when nothing is spilled, all groups fit device
        // hashing, and the GPU Merkle tree fits in free VRAM.
        if !any_spilled
            && !any_host
            && wide_heights.is_empty()
            && tree_workspace_bytes.saturating_add(min_free) <= free_bytes
        {
            let ldes: Vec<CudaLde> = resident
                .into_iter()
                .map(|opt| opt.expect("resident LDE"))
                .collect();
            if self.spill_dir.is_none() && spilled_traces.is_empty() {
                let ldes = Arc::new(ldes);
                let tree = CudaMixedMerkleTree::from_ldes_v6zk(self.device_id, &ldes, &salt_seed);
                let commitment = MerkleCap::new(vec![tree.root()]);
                let materialize_ldes = Arc::clone(&ldes);
                return (
                    commitment,
                    HidingCudaMmcsData(HidingCudaMmcsDataInner::Cuda {
                        resident: ldes,
                        materialize: Some(Box::new(move || {
                            materialize_ldes
                                .iter()
                                .map(CudaLde::to_row_major_matrix)
                                .collect()
                        })),
                        committed_matrices: OnceLock::new(),
                        retained_traces: Mutex::new(retained_traces),
                        tree,
                        salt_seed,
                    }),
                );
            }
            let tree = CudaMixedMerkleTree::from_ldes_v6zk(self.device_id, &ldes, &salt_seed);
            let commitment = MerkleCap::new(vec![tree.root()]);
            let resident_opts: Vec<Option<CudaLde>> = ldes.into_iter().map(Some).collect();
            let resident_active = (0..count).map(|_| AtomicBool::new(true)).collect();
            let committed_matrices = (0..count).map(|_| OnceLock::new()).collect();
            let spilled_cells = (0..count).map(|_| OnceLock::new()).collect();
            return (
                commitment,
                HidingCudaMmcsData(HidingCudaMmcsDataInner::Hybrid {
                    resident: resident_opts,
                    resident_active,
                    materialize: Box::new(CudaLde::to_row_major_matrix),
                    materialize_spilled: Box::new(SpilledMatrix::read_all),
                    committed_matrices,
                    spilled_matrices: spilled_cells,
                    dimensions,
                    retained_traces: Mutex::new(retained_traces),
                    spilled_traces: Mutex::new(spilled_traces),
                    tree: HybridMerkleTree::Device(tree),
                    salt_seed,
                }),
            );
        }

        // Build host `MerkleDigests` (0 bytes VRAM pinned across rounds), using
        // GPU-prehashed leaf digests for unique heights and streaming chunked
        // SIMD BLAKE3 for spilled / wide / multi-matrix groups.
        let heights: Vec<usize> = dimensions.iter().map(|d| d.height).collect();
        let leaf_domain = self.leaf_domain;
        let device_id = self.device_id;
        let digests = build_merkle_digests_from_height_hashes(
            &heights,
            |group_height, group_indices| {
                if let &[single_idx] = group_indices
                    && let Some(leaf_hashes) = prehashed[single_idx].take()
                {
                    assert_eq!(leaf_hashes.len(), group_height);
                    return leaf_hashes;
                }
                let group_has_spilled = group_indices.iter().any(|&i| spilled[i].is_some());
                let group_has_resident = group_indices.iter().any(|&i| resident[i].is_some());
                let group_is_wide = wide_heights.contains(&group_height);
                if !group_has_spilled
                    && group_has_resident
                    && !group_is_wide
                    && group_height
                        .saturating_mul(32)
                        .saturating_add(64 << 20)
                        .saturating_add(min_free)
                        <= super::device_memory_info(device_id).0
                {
                    let res_refs: Vec<Option<&CudaLde>> = group_indices
                        .iter()
                        .map(|&i| resident[i].as_ref())
                        .collect();
                    let host_refs: Vec<Option<&RowMajorMatrix<Goldilocks>>> = group_indices
                        .iter()
                        .map(|&i| {
                            resident[i]
                                .is_none()
                                .then(|| host_matrices[i].as_ref().expect("host matrix"))
                        })
                        .collect();
                    return CudaMixedMerkleTree::hash_hybrid_height_group_v6zk(
                        device_id, &res_refs, &host_refs, &salt_seed,
                    );
                }

                // Stream rows across resident/host/spilled members of this height group.
                let total_row_bytes: usize = group_indices
                    .iter()
                    .map(|&i| dimensions[i].width * size_of::<Goldilocks>())
                    .sum();
                let block_rows = (STREAM_BLOCK_BYTES / total_row_bytes.max(size_of::<u64>()))
                    .clamp(1, group_height);
                // SAFETY: every row `0..group_height` is initialized by
                // `hash_raw_multi_rows_salted_uninit` across chunks.
                unsafe {
                    blake3_simd::alloc_and_fill_digests(group_height, group_height, |dst| {
                        let mut row_start = 0usize;
                        while row_start < group_height {
                            let n_rows = (group_height - row_start).min(block_rows);
                            let blocks: Vec<(Vec<u8>, usize)> = group_indices
                                .iter()
                                .map(|&i| {
                                    let row_bytes = dimensions[i].width * size_of::<Goldilocks>();
                                    if let Some(sp) = spilled[i].as_ref() {
                                        (sp.read_raw_rows(row_start, n_rows), row_bytes)
                                    } else if let Some(mat) = host_matrices[i].as_ref() {
                                        let width = mat.width();
                                        let mut raw = vec![0u8; n_rows * row_bytes];
                                        let slice = &mat.values
                                            [row_start * width..(row_start + n_rows) * width];
                                        for (chunk, elem) in
                                            raw.as_chunks_mut::<8>().0.iter_mut().zip(slice.iter())
                                        {
                                            *chunk = elem.as_canonical_u64().to_le_bytes();
                                        }
                                        (raw, row_bytes)
                                    } else if let Some(lde) = resident[i].as_ref() {
                                        let mut words = vec![0u64; n_rows * lde.width()];
                                        lde.copy_rows_to_host(row_start, n_rows, &mut words);
                                        let mut raw = vec![0u8; n_rows * row_bytes];
                                        for (chunk, &w) in
                                            raw.as_chunks_mut::<8>().0.iter_mut().zip(words.iter())
                                        {
                                            *chunk = w.to_le_bytes();
                                        }
                                        (raw, row_bytes)
                                    } else {
                                        unreachable!("checked above")
                                    }
                                })
                                .collect();
                            blake3_simd::hash_raw_multi_rows_salted_uninit(
                                &blocks,
                                group_height,
                                row_start,
                                &salt_seed,
                                &mut dst[row_start..row_start + n_rows],
                                leaf_domain,
                            );
                            row_start += n_rows;
                        }
                    })
                }
            },
            self.compress_domain,
        );

        let tree = HybridMerkleTree::Host(digests);
        let commitment = tree.cap(self.cap_height);
        let resident_active: Vec<AtomicBool> = resident
            .iter()
            .map(|opt| AtomicBool::new(opt.is_some()))
            .collect();
        let committed_matrices: Vec<OnceLock<RowMajorMatrix<Goldilocks>>> = host_matrices
            .into_iter()
            .map(|mat| {
                let cell = OnceLock::new();
                if let Some(mat) = mat {
                    cell.set(mat).expect("fresh hiding host cell");
                }
                cell
            })
            .collect();
        let spilled_cells: Vec<OnceLock<SpilledMatrix>> = spilled
            .into_iter()
            .map(|sp| {
                let cell = OnceLock::new();
                if let Some(sp) = sp {
                    cell.set(sp).ok().expect("fresh hiding spill cell");
                }
                cell
            })
            .collect();
        (
            commitment,
            HidingCudaMmcsData(HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                materialize: Box::new(CudaLde::to_row_major_matrix),
                materialize_spilled: Box::new(SpilledMatrix::read_all),
                committed_matrices,
                spilled_matrices: spilled_cells,
                dimensions,
                retained_traces: Mutex::new(retained_traces),
                spilled_traces: Mutex::new(spilled_traces),
                tree,
                salt_seed,
            }),
        )
    }

    /// Commits device-resident CUDA LDEs with an explicit `salt_seed`, routing
    /// any height group exceeding [`MAX_DEVICE_LEAF_ROW_BYTES_ZK`] through
    /// host salted leaf hashing and hybrid CUDA Merkle tree construction.
    pub(crate) fn commit_cuda_resident_with_seed(
        &self,
        ldes: Vec<CudaLde>,
        salt_seed: [u8; 32],
    ) -> (
        <Self as Mmcs<Goldilocks>>::Commitment,
        HidingCudaMmcsData<RowMajorMatrix<Goldilocks>>,
    ) {
        let wide_heights = host_hashed_heights_zk(ldes.iter().map(|lde| Dimensions {
            width: lde.width(),
            height: lde.height(),
        }));
        if !wide_heights.is_empty() {
            let count = ldes.len();
            let mut resident: Vec<Option<CudaLde>> = Vec::with_capacity(count);
            let mut host: Vec<Option<RowMajorMatrix<Goldilocks>>> = Vec::with_capacity(count);
            let mut dimensions = Vec::with_capacity(count);
            for lde in ldes {
                let dims = Dimensions {
                    width: lde.width(),
                    height: lde.height(),
                };
                dimensions.push(dims);
                if wide_heights.contains(&dims.height) {
                    host.push(Some(lde.to_row_major_matrix()));
                    resident.push(None);
                } else {
                    host.push(None);
                    resident.push(Some(lde));
                }
            }
            let host_digest_groups =
                hash_wide_host_groups_salted(&host, &wide_heights, &salt_seed, self.leaf_domain);
            let resident_refs: Vec<Option<&CudaLde>> =
                resident.iter().map(Option::as_ref).collect();
            let host_refs: Vec<Option<&RowMajorMatrix<Goldilocks>>> =
                host.iter().map(Option::as_ref).collect();
            let deferred_dims = vec![None; resident.len()];
            let tree = CudaMixedMerkleTree::from_hybrid_v6zk(
                self.device_id,
                &resident_refs,
                &host_refs,
                &deferred_dims,
                &host_digest_groups,
                &salt_seed,
            );
            let commitment = MerkleCap::new(vec![tree.root()]);
            let resident_active = resident
                .iter()
                .map(|opt| AtomicBool::new(opt.is_some()))
                .collect();
            let committed_matrices = host
                .into_iter()
                .map(|mat| {
                    let cell = OnceLock::new();
                    if let Some(mat) = mat {
                        cell.set(mat).expect("fresh hybrid matrix cell");
                    }
                    cell
                })
                .collect();
            let spilled_matrices = (0..count).map(|_| OnceLock::new()).collect();
            return (
                commitment,
                HidingCudaMmcsData(HidingCudaMmcsDataInner::Hybrid {
                    resident,
                    resident_active,
                    materialize: Box::new(CudaLde::to_row_major_matrix),
                    materialize_spilled: Box::new(SpilledMatrix::read_all),
                    committed_matrices,
                    spilled_matrices,
                    dimensions,
                    retained_traces: Mutex::new(Vec::new()),
                    spilled_traces: Mutex::new(Vec::new()),
                    tree: HybridMerkleTree::Device(tree),
                    salt_seed,
                }),
            );
        }

        let ldes = Arc::new(ldes);
        let tree = CudaMixedMerkleTree::from_ldes_v6zk(self.device_id, &ldes, &salt_seed);
        let commitment = MerkleCap::new(vec![tree.root()]);
        let materialize_ldes = Arc::clone(&ldes);
        (
            commitment,
            HidingCudaMmcsData(HidingCudaMmcsDataInner::Cuda {
                resident: ldes,
                materialize: Some(Box::new(move || {
                    materialize_ldes
                        .iter()
                        .map(CudaLde::to_row_major_matrix)
                        .collect()
                })),
                committed_matrices: OnceLock::new(),
                retained_traces: Mutex::new(Vec::new()),
                tree,
                salt_seed,
            }),
        )
    }

    /// Uploads host LDEs to CUDA when they fit device row limits and VRAM
    /// headroom, committing them with an explicit `salt_seed` while retaining
    /// the original host storage for fast re-reads.
    pub(crate) fn commit_cuda_storage_with_seed(
        &self,
        ldes: Vec<RowMajorMatrix<Goldilocks>>,
        salt_seed: [u8; 32],
    ) -> (
        <Self as Mmcs<Goldilocks>>::Commitment,
        HidingCudaMmcsData<RowMajorMatrix<Goldilocks>>,
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
        let exceeds_vram = total_bytes
            .saturating_add(tree_workspace_bytes)
            .saturating_add(min_free)
            > free_bytes
            || !host_hashed_heights_zk(ldes.iter().map(Matrix::dimensions)).is_empty();
        if let Some(dir) = self.spill_dir.as_deref()
            && (exceeds_vram || total_bytes > total_device_bytes / 6)
        {
            let mut pack = SpillPackWriter::create(dir);
            let spilled: Vec<Option<SpilledMatrix>> = ldes
                .into_iter()
                .map(|m| Some(pack.append_matrix(&m)))
                .collect();
            pack.flush();
            let count = spilled.len();
            return self.commit_cuda_mixed_spilled_with_seed(
                (0..count).map(|_| None).collect(),
                (0..count).map(|_| None).collect(),
                spilled,
                (0..count).map(|_| None).collect(),
                Vec::new(),
                Vec::new(),
                salt_seed,
            );
        }
        if exceeds_vram {
            return self.commit_cpu_with_seed(ldes, salt_seed);
        }
        let resident: Vec<CudaLde> = ldes
            .iter()
            .map(|matrix| CudaLde::from_row_major_matrix(self.device_id, matrix))
            .collect();
        let (commitment, mut data) = self.commit_cuda_resident_with_seed(resident, salt_seed);
        if let HidingCudaMmcsDataInner::Cuda {
            committed_matrices, ..
        } = &mut data.0
        {
            let _ = committed_matrices.set(ldes);
        }
        (commitment, data)
    }
}

fn hash_wide_host_groups_salted(
    host_matrices: &[Option<RowMajorMatrix<Goldilocks>>],
    wide_heights: &BTreeSet<usize>,
    salt_seed: &[u8; 32],
    leaf_domain: Blake3Domain,
) -> Vec<(usize, Vec<[u8; 32]>)> {
    let mut groups: BTreeMap<usize, Vec<&RowMajorMatrix<Goldilocks>>> = BTreeMap::new();
    for matrix in host_matrices.iter().flatten() {
        if wide_heights.contains(&matrix.height()) {
            groups.entry(matrix.height()).or_default().push(matrix);
        }
    }
    groups
        .into_iter()
        .map(|(height, mats)| {
            let digests = hash_group_salted(&mats, height, salt_seed, leaf_domain);
            (height, digests)
        })
        .collect()
}

fn hybrid_open_row<M: Matrix<Goldilocks>>(
    resident: &[Option<CudaLde>],
    resident_active: &[AtomicBool],
    committed_matrices: &[OnceLock<M>],
    spilled_matrices: &[OnceLock<SpilledMatrix>],
    dimensions: &[Dimensions],
    index: usize,
) -> Vec<Vec<Goldilocks>> {
    let max_height = dimensions.iter().map(|d| d.height).max().unwrap();
    assert!(index < max_height, "MMCS opening index out of bounds");
    let log_max_height = log2_ceil_usize(max_height);
    let active_ldes: Vec<&CudaLde> = resident
        .iter()
        .enumerate()
        .filter_map(|(i, lde)| {
            resident_active[i]
                .load(Ordering::Acquire)
                .then_some(lde.as_ref())?
        })
        .collect();
    let mut gpu_rows = if active_ldes.is_empty() {
        Vec::new().into_iter()
    } else {
        mixed_lde_open_row_at_height(active_ldes, max_height, index).into_iter()
    };
    resident
        .iter()
        .enumerate()
        .map(|(matrix_index, lde)| {
            if lde.is_some() && resident_active[matrix_index].load(Ordering::Acquire) {
                gpu_rows.next().unwrap()
            } else if let Some(spilled) = spilled_matrices[matrix_index].get() {
                let row = index >> (log_max_height - log2_ceil_usize(spilled.height()));
                spilled.read_row(row)
            } else {
                let matrix = committed_matrices[matrix_index]
                    .get()
                    .expect("hybrid host matrix missing");
                let row = index >> (log_max_height - log2_ceil_usize(matrix.height()));
                matrix.row(row).unwrap().into_iter().collect()
            }
        })
        .collect()
}

fn hybrid_open_rows<M: Matrix<Goldilocks>>(
    resident: &[Option<CudaLde>],
    resident_active: &[AtomicBool],
    committed_matrices: &[OnceLock<M>],
    spilled_matrices: &[OnceLock<SpilledMatrix>],
    dimensions: &[Dimensions],
    indices: &[usize],
) -> Vec<Vec<Vec<Goldilocks>>> {
    if indices.is_empty() {
        return Vec::new();
    }
    let max_height = dimensions.iter().map(|d| d.height).max().unwrap();
    assert!(indices.iter().all(|&index| index < max_height));
    let log_max_height = log2_ceil_usize(max_height);
    let active_ldes: Vec<&CudaLde> = resident
        .iter()
        .enumerate()
        .filter_map(|(i, lde)| {
            resident_active[i]
                .load(Ordering::Acquire)
                .then_some(lde.as_ref())?
        })
        .collect();
    let mut gpu_queries = if active_ldes.is_empty() {
        (0..indices.len())
            .map(|_| Vec::new())
            .collect::<Vec<_>>()
            .into_iter()
    } else {
        mixed_lde_open_rows_at_height(active_ldes, max_height, indices).into_iter()
    };
    indices
        .iter()
        .map(|&index| {
            let mut gpu_rows = gpu_queries.next().unwrap().into_iter();
            resident
                .iter()
                .enumerate()
                .map(|(matrix_index, lde)| {
                    if lde.is_some() && resident_active[matrix_index].load(Ordering::Acquire) {
                        gpu_rows.next().unwrap()
                    } else if let Some(spilled) = spilled_matrices[matrix_index].get() {
                        let row = index >> (log_max_height - log2_ceil_usize(spilled.height()));
                        spilled.read_row(row)
                    } else {
                        let matrix = committed_matrices[matrix_index]
                            .get()
                            .expect("hybrid host matrix missing");
                        let row = index >> (log_max_height - log2_ceil_usize(matrix.height()));
                        matrix.row(row).unwrap().into_iter().collect()
                    }
                })
                .collect()
        })
        .collect()
}

impl Mmcs<Goldilocks> for HidingCudaMmcs {
    type ProverData<M> = HidingCudaMmcsData<M>;
    type Commitment = MerkleCap<Goldilocks, [u8; 32]>;
    type Proof = HidingBatchProof;
    type MultiProof = HidingMultiProof;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<Goldilocks>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let salt_seed = random_seed();
        let all_pow2 = inputs.iter().all(|m| m.height().is_power_of_two());
        let device_hashable =
            all_pow2 && host_hashed_heights_zk(inputs.iter().map(Matrix::dimensions)).is_empty();
        let total_cells: usize = inputs
            .iter()
            .map(|matrix| matrix.height().saturating_mul(matrix.width()))
            .sum();
        let total_bytes = total_cells.saturating_mul(size_of::<Goldilocks>());
        if device_hashable && total_cells > (1 << 18) {
            let max_height = inputs.iter().map(Matrix::height).max().unwrap_or(0);
            let tree_workspace_bytes = max_height.saturating_mul(96);
            let (free_bytes, _) = super::device_memory_info(self.device_id);
            let min_free = super::minimum_free_bytes();
            if total_bytes
                .saturating_add(tree_workspace_bytes)
                .saturating_add(min_free)
                <= free_bytes
            {
                let resident: Vec<CudaLde> = inputs
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
                let resident = Arc::new(resident);
                let tree =
                    CudaMixedMerkleTree::from_ldes_v6zk(self.device_id, &resident, &salt_seed);
                let commitment = MerkleCap::new(vec![tree.root()]);
                let committed_matrices = OnceLock::new();
                committed_matrices
                    .set(inputs)
                    .ok()
                    .expect("fresh CUDA matrix cell");
                return (
                    commitment,
                    HidingCudaMmcsData(HidingCudaMmcsDataInner::Cuda {
                        resident,
                        materialize: None,
                        committed_matrices,
                        retained_traces: Mutex::new(Vec::new()),
                        tree,
                        salt_seed,
                    }),
                );
            }
        }
        self.commit_cpu_with_seed(inputs, salt_seed)
    }

    fn open_batch<M: Matrix<Goldilocks>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<Goldilocks, Self> {
        match &prover_data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => {
                let (opened_values, proof) = tree.open_batch(index, self.cap_height);
                BatchOpening::new(opened_values, proof)
            }
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                dimensions,
                tree,
                salt_seed,
                ..
            } => {
                let heights: Vec<usize> = dimensions.iter().map(|d| d.height).collect();
                let opened_values = hybrid_open_row(
                    resident,
                    resident_active,
                    committed_matrices,
                    spilled_matrices,
                    dimensions,
                    index,
                );
                let siblings = tree.open_siblings(index, self.cap_height);
                let salts = open_hiding_batch_salts(salt_seed, &heights, index, self.cap_height);
                BatchOpening::new(opened_values, HidingBatchProof { salts, siblings })
            }
            HidingCudaMmcsDataInner::Cuda {
                resident,
                tree,
                salt_seed,
                ..
            } => {
                let heights: Vec<usize> = resident.iter().map(CudaLde::height).collect();
                let opened_values = mixed_lde_open_row(resident, index);
                let siblings = tree.open_siblings(index);
                let salts = open_hiding_batch_salts(salt_seed, &heights, index, self.cap_height);
                BatchOpening::new(opened_values, HidingBatchProof { salts, siblings })
            }
        }
    }

    fn get_matrices<'a, M: Matrix<Goldilocks>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        match &prover_data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.leaves.iter().collect(),
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                materialize,
                materialize_spilled,
                committed_matrices,
                spilled_matrices,
                ..
            } => resident
                .iter()
                .enumerate()
                .map(|(index, lde)| {
                    if let Some(lde) = lde.as_ref()
                        && resident_active[index].load(Ordering::Acquire)
                    {
                        committed_matrices[index].get_or_init(|| materialize(lde))
                    } else if let Some(spilled) = spilled_matrices[index].get() {
                        committed_matrices[index].get_or_init(|| materialize_spilled(spilled))
                    } else {
                        committed_matrices[index]
                            .get()
                            .expect("hybrid host matrix missing")
                    }
                })
                .collect(),
            HidingCudaMmcsDataInner::Cuda {
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
        match &prover_data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.matrix_heights(),
            HidingCudaMmcsDataInner::Hybrid { dimensions, .. } => {
                dimensions.iter().map(|d| d.height).collect()
            }
            HidingCudaMmcsDataInner::Cuda { resident, .. } => {
                resident.iter().map(CudaLde::height).collect()
            }
        }
    }

    fn get_max_height<M: Matrix<Goldilocks>>(&self, prover_data: &Self::ProverData<M>) -> usize {
        match &prover_data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.max_height(),
            HidingCudaMmcsDataInner::Hybrid { dimensions, .. } => {
                dimensions.iter().map(|d| d.height).max().unwrap()
            }
            HidingCudaMmcsDataInner::Cuda { resident, .. } => {
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
        verify_hiding_batch(
            self.cap_height,
            self.leaf_domain,
            self.compress_domain,
            commit,
            dimensions,
            index,
            batch_opening.opened_values,
            batch_opening.opening_proof,
        )
    }

    fn open_multi_batch<M: Matrix<Goldilocks>>(
        &self,
        indices: &[usize],
        prover_data: &Self::ProverData<M>,
    ) -> (Vec<Vec<Vec<Goldilocks>>>, Self::MultiProof) {
        match &prover_data.0 {
            HidingCudaMmcsDataInner::Cpu(tree) => tree.open_multi_batch(indices, self.cap_height),
            HidingCudaMmcsDataInner::Hybrid {
                resident,
                resident_active,
                committed_matrices,
                spilled_matrices,
                dimensions,
                tree,
                salt_seed,
                ..
            } => {
                let heights: Vec<usize> = dimensions.iter().map(|d| d.height).collect();
                let opened_values = hybrid_open_rows(
                    resident,
                    resident_active,
                    committed_matrices,
                    spilled_matrices,
                    dimensions,
                    indices,
                );
                let pruned = tree.open_pruned_siblings(indices, self.cap_height);
                let salts = open_hiding_multi_salts(salt_seed, &heights, indices, self.cap_height);
                (opened_values, HidingMultiProof { salts, pruned })
            }
            HidingCudaMmcsDataInner::Cuda {
                resident,
                tree,
                salt_seed,
                ..
            } => {
                let heights: Vec<usize> = resident.iter().map(CudaLde::height).collect();
                let opened_values = if indices.is_empty() {
                    Vec::new()
                } else {
                    mixed_lde_open_rows(resident, indices)
                };
                let pruned = tree.open_pruned_siblings(indices);
                let salts = open_hiding_multi_salts(salt_seed, &heights, indices, self.cap_height);
                (opened_values, HidingMultiProof { salts, pruned })
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
        verify_hiding_multi_batch(
            self.cap_height,
            self.leaf_domain,
            self.compress_domain,
            commit,
            dimensions,
            indices,
            opened_values,
            proof,
        )
    }
}

impl CapValidatingMmcs<Goldilocks> for HidingCudaMmcs {
    fn validate_commitment_cap_for_log_height(
        &self,
        commit: &Self::Commitment,
        log_max_height: usize,
    ) -> Result<(), Self::Error> {
        verify_merkle_cap_len_for_log_height(self.cap_height(), commit, log_max_height)
    }

    fn empty_multi_proof() -> Self::MultiProof {
        HidingMultiProof {
            salts: Vec::new(),
            pruned: PrunedMerklePaths {
                sibling_hashes: Vec::new(),
            },
        }
    }
}

/// Device-resident salted FRI commit-phase round holding the codeword, Merkle
/// tree, arity, and 32-byte `salt_seed` (zero salt-matrix VRAM overhead).
#[doc(hidden)]
pub struct HidingCudaFriRound {
    pub(crate) codeword: CudaLde,
    pub(crate) tree: CudaMixedMerkleTree,
    pub(crate) arity: usize,
    pub(crate) salt_seed: [u8; 32],
}

/// Trait implemented by CUDA hiding FRI commit-phase MMCS types.
#[doc(hidden)]
pub trait HidingCudaFriMmcs<Val, Challenge: Send + Sync + Clone>: Mmcs<Challenge> {
    fn commit_cuda_fri_hiding(
        &self,
        codeword: CudaLde,
        log_arity: usize,
    ) -> (Self::Commitment, HidingCudaFriRound);

    fn open_cuda_fri_hiding_batch(
        &self,
        round: &HidingCudaFriRound,
        rows: &[usize],
    ) -> (Vec<Vec<Challenge>>, Self::MultiProof);
}

impl<Challenge> HidingCudaFriMmcs<Goldilocks, Challenge>
    for ExtensionMmcs<Goldilocks, Challenge, HidingCudaMmcs>
where
    Challenge: ExtensionField<Goldilocks>,
{
    fn commit_cuda_fri_hiding(
        &self,
        codeword: CudaLde,
        log_arity: usize,
    ) -> (Self::Commitment, HidingCudaFriRound) {
        let arity = 1usize << log_arity;
        let salt_seed = random_seed();
        let tree = CudaMixedMerkleTree::from_fri_codeword_v6zk(&codeword, arity, &salt_seed);
        let commitment = MerkleCap::new(vec![tree.root()]);
        (
            commitment,
            HidingCudaFriRound {
                codeword,
                tree,
                arity,
                salt_seed,
            },
        )
    }

    fn open_cuda_fri_hiding_batch(
        &self,
        round: &HidingCudaFriRound,
        rows: &[usize],
    ) -> (Vec<Vec<Challenge>>, Self::MultiProof) {
        let codeword_rows = rows
            .iter()
            .flat_map(|&row| (0..round.arity).map(move |column| row * round.arity + column))
            .collect_vec();
        let opened = round.codeword.rows(&codeword_rows);
        let opened_rows = opened
            .chunks_exact(round.arity)
            .map(|query_rows| {
                query_rows
                    .iter()
                    .map(|row| {
                        Challenge::from_basis_coefficients_slice(row).expect("extension row")
                    })
                    .collect()
            })
            .collect();
        let tree_height = round.codeword.height() / round.arity;
        let pruned = round.tree.open_pruned_siblings(rows);
        // CUDA backend enforces `cap_height == 0` on construction.
        let salts = open_hiding_multi_salts(&round.salt_seed, &[tree_height], rows, 0);
        (opened_rows, HidingMultiProof { salts, pruned })
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::types::{ExtVal2, ExtVal3};

    fn test_matrix(height: usize, width: usize, offset: usize) -> RowMajorMatrix<Goldilocks> {
        RowMajorMatrix::new(
            (0..height * width)
                .map(|i| Goldilocks::from_usize(offset + i))
                .collect(),
            width,
        )
    }

    #[test]
    fn wide_height_groups_zk_leave_room_for_leaf_salt() {
        let d = |width, height| Dimensions { width, height };
        // 4094 Goldilocks columns + 16-byte leaf salt = exactly 32 KiB.
        assert!(host_hashed_heights_zk([d(4094, 8)]).is_empty());
        assert_eq!(
            host_hashed_heights_zk([d(4095, 8)])
                .into_iter()
                .collect::<Vec<_>>(),
            vec![8]
        );
        assert_eq!(
            host_hashed_heights_zk([d(3000, 16), d(1095, 16), d(10, 4)])
                .into_iter()
                .collect::<Vec<_>>(),
            vec![16]
        );
    }

    #[test]
    #[should_panic(expected = "cap_height = 0")]
    fn cuda_v6zk_rejects_nonzero_merkle_caps() {
        let _ = HidingCudaMmcs::new_v6_zk(1, 0);
    }

    #[test]
    fn cuda_v6zk_from_ldes_matches_cpu_salted_tree() {
        let mmcs = HidingCudaMmcs::new_v6_zk(0, 0);
        let salt_seed = [0x5Au8; 32];
        let matrices = vec![
            test_matrix(32, 5, 1),
            test_matrix(16, 3, 100),
            test_matrix(32, 2, 300),
            test_matrix(8, 7, 500),
        ];
        let dims: Vec<Dimensions> = matrices.iter().map(Matrix::dimensions).collect();

        let (cpu_commit, cpu_data) = mmcs.commit_cpu_with_seed(matrices.clone(), salt_seed);
        let ldes: Vec<CudaLde> = matrices
            .iter()
            .map(|m| CudaLde::from_row_major_matrix(mmcs.device_id(), m))
            .collect();
        let (gpu_commit, gpu_data) = mmcs.commit_cuda_resident_with_seed(ldes, salt_seed);

        assert_eq!(
            gpu_commit, cpu_commit,
            "GPU v6-zk Merkle root must match CPU salted tree bit-for-bit"
        );

        for idx in [0usize, 1, 7, 19, 31] {
            let cpu_open = mmcs.open_batch(idx, &cpu_data);
            let gpu_open = mmcs.open_batch(idx, &gpu_data);
            assert_eq!(gpu_open.opened_values, cpu_open.opened_values);
            assert_eq!(gpu_open.opening_proof, cpu_open.opening_proof);
            mmcs.verify_batch(
                &gpu_commit,
                &dims,
                idx,
                BatchOpeningRef::new(&gpu_open.opened_values, &gpu_open.opening_proof),
            )
            .expect("single-batch verification must pass");
        }

        let query_indices = [0usize, 3, 3, 15, 29];
        let (cpu_rows, cpu_proof) = mmcs.open_multi_batch(&query_indices, &cpu_data);
        let (gpu_rows, gpu_proof) = mmcs.open_multi_batch(&query_indices, &gpu_data);
        assert_eq!(gpu_rows, cpu_rows);
        assert_eq!(gpu_proof, cpu_proof);
        mmcs.verify_multi_batch(&gpu_commit, &dims, &query_indices, &gpu_rows, &gpu_proof)
            .expect("multi-batch verification must pass");
    }

    #[test]
    fn cuda_v6zk_wide_and_hybrid_group_match_cpu_salted_tree() {
        let mmcs = HidingCudaMmcs::new_v6_zk(0, 0);
        let salt_seed = [0xA3u8; 32];
        let matrices = vec![
            test_matrix(16, 12, 7),
            test_matrix(8, 4100, 99),
            test_matrix(16, 5, 200),
        ];
        let dims: Vec<Dimensions> = matrices.iter().map(Matrix::dimensions).collect();

        // Exercise `hash_hybrid_height_group_v6zk` on a resident+host pair at height 16.
        let lde0 = CudaLde::from_row_major_matrix(mmcs.device_id(), &matrices[0]);
        let hybrid_digests = CudaMixedMerkleTree::hash_hybrid_height_group_v6zk(
            mmcs.device_id(),
            &[Some(&lde0), None],
            &[None, Some(&matrices[2])],
            &salt_seed,
        );
        let expected_digests = hash_group_salted(
            &[&matrices[0], &matrices[2]],
            16,
            &salt_seed,
            Blake3Domain::ZkMerkleLeaf,
        );
        assert_eq!(hybrid_digests, expected_digests);

        // Exercise wide height-group (> 4094 cols) automatic hybrid commit.
        let (cpu_commit, cpu_data) = mmcs.commit_cpu_with_seed(matrices.clone(), salt_seed);
        let ldes: Vec<CudaLde> = matrices
            .iter()
            .map(|m| CudaLde::from_row_major_matrix(mmcs.device_id(), m))
            .collect();
        let (gpu_commit, gpu_data) = mmcs.commit_cuda_resident_with_seed(ldes, salt_seed);
        assert_eq!(gpu_commit, cpu_commit);

        let indices = [0usize, 5, 11, 15];
        let (cpu_rows, cpu_proof) = mmcs.open_multi_batch(&indices, &cpu_data);
        let (gpu_rows, gpu_proof) = mmcs.open_multi_batch(&indices, &gpu_data);
        assert_eq!(gpu_rows, cpu_rows);
        assert_eq!(gpu_proof, cpu_proof);
        mmcs.verify_multi_batch(&gpu_commit, &dims, &indices, &gpu_rows, &gpu_proof)
            .expect("wide-group hybrid verification must pass");
    }

    #[test]
    fn cuda_v6zk_fri_merkle_verifies_ext2_and_ext3() {
        let base_mmcs = HidingCudaMmcs::new_v6_zk(0, 0);

        let ext3_mmcs: ExtensionMmcs<Goldilocks, ExtVal3, HidingCudaMmcs> =
            ExtensionMmcs::new(base_mmcs.clone());
        let cw3 = test_matrix(64, 3, 17);
        let cw3_gpu = CudaLde::from_row_major_matrix(base_mmcs.device_id(), &cw3);
        let (commit3, round3) = ext3_mmcs.commit_cuda_fri_hiding(cw3_gpu, 1);
        let rows = [0usize, 5, 13, 31];
        let (opened3, mut proof3) = ext3_mmcs.open_cuda_fri_hiding_batch(&round3, &rows);
        let opened3_wrapped: Vec<Vec<Vec<ExtVal3>>> =
            opened3.into_iter().map(|row| vec![row]).collect();
        let dims3 = [Dimensions {
            width: 2,
            height: 32,
        }];
        ext3_mmcs
            .verify_multi_batch(&commit3, &dims3, &rows, &opened3_wrapped, &proof3)
            .expect("CUDA v6-zk ExtVal3 FRI Merkle opening must verify");
        proof3.salts[0][0][0] ^= 1;
        assert!(
            ext3_mmcs
                .verify_multi_batch(&commit3, &dims3, &rows, &opened3_wrapped, &proof3)
                .is_err(),
            "tampered FRI leaf salt must fail verification"
        );

        let ext2_mmcs: ExtensionMmcs<Goldilocks, ExtVal2, HidingCudaMmcs> =
            ExtensionMmcs::new(base_mmcs);
        let cw2 = test_matrix(64, 2, 41);
        let cw2_gpu = CudaLde::from_row_major_matrix(0, &cw2);
        let (commit2, round2) = ext2_mmcs.commit_cuda_fri_hiding(cw2_gpu, 1);
        let (opened2, proof2) = ext2_mmcs.open_cuda_fri_hiding_batch(&round2, &rows);
        let opened2_wrapped: Vec<Vec<Vec<ExtVal2>>> =
            opened2.into_iter().map(|row| vec![row]).collect();
        ext2_mmcs
            .verify_multi_batch(&commit2, &dims3, &rows, &opened2_wrapped, &proof2)
            .expect("CUDA v6-zk ExtVal2 FRI Merkle opening must verify");
    }
}
