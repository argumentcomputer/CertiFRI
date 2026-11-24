use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use p3_commit::{ExtensionMmcs, Pcs};
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, TwoAdicField};
use p3_fri::FriParameters as InnerFriParameters;
use p3_goldilocks::Goldilocks;
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

use super::*;
use crate::config::ProofConfig;
use crate::cuda::hiding_mmcs::HidingCudaMmcs;
use crate::cuda::hiding_pcs::HidingCudaTwoAdicFriPcs;
use crate::cuda::mmcs::{CudaCommitMmcs, CudaMatrixSource, CudaMmcs};
use crate::cuda::pcs::{CudaTwoAdicFriPcs, bit_reversed_coset, ext_to_goldilocks};
use crate::expr::{CircuitSpec, Expr, ExtExpr};
use crate::graph::compile;
use crate::lookup::{Lookup, logup_constraint_count, stage2_width};
use crate::p3_adapter::domain_blake3::Blake3Domain;
use crate::p3_adapter::fri_batching::FriBatching;
use crate::p3_adapter::pcs::{lde_from_shifted_coefficients, shifted_quotient_slices};
use crate::p3_adapter::spill::{
    SpillPackWriter, SpillableMmcs, SpillableTwoAdicFriPcs, SpilledMatrix, active_spill_files,
};
use crate::p3_adapter::spill_zk::{HidingSpillableMmcs, HidingSpillableTwoAdicFriPcs};
use crate::system::{Circuit, CircuitInputs, System};
use crate::types::{
    CommitmentParameters, ExtVal2, ExtVal3, FriParameters, GoldilocksBlake3Config,
    GoldilocksBlake3V6Config, GoldilocksBlake3V6ZkConfig,
};

fn fresh_spill_dir(tag: &str) -> PathBuf {
    static NEXT_ID: AtomicU64 = AtomicU64::new(0);
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "multi-stark-cuda-spill-{tag}-{}-{id}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp CUDA spill dir");
    dir
}

fn random_matrix(seed: u64, height: usize, width: usize) -> RowMajorMatrix<Goldilocks> {
    let mut rng = SmallRng::seed_from_u64(seed);
    RowMajorMatrix::new(
        (0..height * width)
            .map(|_| Goldilocks::from_u64(rng.random::<u64>() % Goldilocks::ORDER_U64))
            .collect(),
        width,
    )
}

fn spill_as_multi_panel(
    lde: &CudaLde,
    pack: &mut SpillPackWriter,
    panel_widths: &[usize],
) -> SpilledMatrix {
    let host = lde.to_row_major_matrix();
    let total_w: usize = panel_widths.iter().sum();
    assert_eq!(total_w, lde.width());
    let mut panels = Vec::with_capacity(panel_widths.len());
    let mut col = 0usize;
    for &pw in panel_widths {
        let sub = extract_column_panel(&host, col, pw);
        let sub_gpu = CudaLde::from_row_major_matrix(lde.device_id, &sub);
        panels.push(sub_gpu.spill_panel_to_pack(pack));
        col += pw;
    }
    SpilledMatrix::from_panels(lde.height(), panels)
}

#[test]
fn cuda_coset_lde_spilled_and_shifted_coeffs_match_cpu() {
    let device = configured_device();
    let dft = CudaDft::without_auxiliary_devices(device);
    let cpu = Radix2DitParallel::<Goldilocks>::default();
    let dir = fresh_spill_dir("coset-and-shifted");

    let trace = random_matrix(0x1111, 512, 9);
    let log_blowup = 2usize;
    let shift = Goldilocks::GENERATOR;

    let expected_lde = cpu
        .coset_lde_batch(trace.clone(), log_blowup, shift)
        .bit_reverse_rows()
        .to_row_major_matrix();

    let salt_seed = [0x42u8; 32];
    let mut pack = SpillPackWriter::create(&dir);
    for (domain, salt) in [
        (Blake3Domain::Plain, None),
        (Blake3Domain::MerkleLeaf, None),
        (Blake3Domain::ZkMerkleLeaf, Some(&salt_seed)),
    ] {
        let (spilled, digests) =
            dft.coset_lde_spilled(&trace, log_blowup, shift, &mut pack, Some((domain, salt)));
        pack.flush();
        assert_eq!(spilled.read_all(), expected_lde);
        let digests = digests.expect("unique-height GPU leaf hash should succeed");
        assert_eq!(digests.len(), expected_lde.height());
        let mut expected_digests = vec![[0u8; 32]; expected_lde.height()];
        if let Some(seed) = salt {
            // Verify against CPU salted leaf hashing.
            for (row_idx, slot) in expected_digests.iter_mut().enumerate() {
                let mut hasher = domain.hasher();
                for elem in expected_lde.row(row_idx).unwrap() {
                    hasher.update(&elem.as_canonical_u64().to_le_bytes());
                }
                hasher.update(&crate::p3_adapter::zk::derive_leaf_salt(
                    seed,
                    expected_lde.height(),
                    row_idx,
                ));
                *slot = hasher.finalize().into();
            }
        } else {
            crate::p3_adapter::blake3_simd::hash_matrix_rows(
                &[&expected_lde],
                0,
                &mut expected_digests,
                domain,
            );
        }
        assert_eq!(digests, expected_digests);
    }

    // Verify `shifted_coeffs_to_lde_resident` and `shifted_coeffs_to_lde_spilled`
    // match `lde_from_shifted_coefficients` bit-for-bit.
    let shifted = random_matrix(0x2222, 512, 12);
    let expected_shifted = lde_from_shifted_coefficients(&cpu, shifted.clone(), log_blowup);
    let resident_shifted = dft.shifted_coeffs_to_lde_resident(&shifted, log_blowup);
    assert_eq!(resident_shifted.to_row_major_matrix(), expected_shifted);
    let (spilled_shifted, digests) = dft.shifted_coeffs_to_lde_spilled(
        &shifted,
        log_blowup,
        &mut pack,
        Some((Blake3Domain::ZkMerkleLeaf, Some(&salt_seed))),
    );
    pack.flush();
    assert_eq!(spilled_shifted.read_all(), expected_shifted);
    assert!(digests.is_some());

    drop(spilled_shifted);
    drop(pack);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn cuda_fri_chunked_spilled_interp_and_reduce_match_resident_ext2_and_ext3() {
    fn check_ext<EF: ExtensionField<Goldilocks>>(ext_degree: usize, ext_w: Goldilocks) {
        let device = configured_device();
        let dir = fresh_spill_dir(&format!("fri-chunked-ext{ext_degree}"));
        let lde_height = 2048usize;
        let poly_height = 512usize;
        let width = 11usize;
        let host_mat = random_matrix(0x3333 + ext_degree as u64, lde_height, width);
        let resident = CudaLde::from_row_major_matrix(device, &host_mat);

        let mut pack = SpillPackWriter::create(&dir);
        let spilled_single = resident.spill_to_pack(&mut pack);
        let spilled_multi = spill_as_multi_panel(&resident, &mut pack, &[3, 5, 3]);
        pack.flush();

        let coset = bit_reversed_coset::<Goldilocks>(log2_strict_usize(lde_height));
        let z0_coords = [
            Goldilocks::from_u64(13),
            Goldilocks::from_u64(29),
            Goldilocks::from_u64(47),
        ];
        let z1_coords = [
            Goldilocks::from_u64(71),
            Goldilocks::from_u64(103),
            Goldilocks::from_u64(149),
        ];
        let z0 = EF::from_basis_coefficients_slice(&z0_coords[..ext_degree]).unwrap();
        let z1 = EF::from_basis_coefficients_slice(&z1_coords[..ext_degree]).unwrap();

        let mut inverse_points = Vec::new();
        for &pt in &[z0, z1] {
            let (buf, d) = ext_to_goldilocks::<Goldilocks, EF>(pt, ext_degree);
            inverse_points.extend_from_slice(&buf[..d]);
        }
        let inverse_counts = [lde_height, lde_height];
        let mut ws = CudaFriWorkspace::new(
            device,
            &inverse_points,
            &inverse_counts,
            &coset,
            ext_w,
            ext_degree,
        );

        let lh = log2_strict_usize(poly_height);
        let shift_pow = Goldilocks::GENERATOR.exp_power_of_2(lh);
        let scale_of = |pt: EF| {
            let s = (pt.exp_power_of_2(lh) - shift_pow)
                * (Goldilocks::from_usize(poly_height) * shift_pow).inverse();
            let (buf, d) = ext_to_goldilocks::<Goldilocks, EF>(s, ext_degree);
            buf[..d].to_vec()
        };

        // Test both 1-point and 2-point (fused) interpolation & reduction!
        for pts in [&[z0][..], &[z0, z1][..]] {
            let mut tasks = CudaInterpolationTasks::new(ext_degree);
            let mut inv_offsets = Vec::new();
            let mut scales_flat = Vec::new();
            for (i, &pt) in pts.iter().enumerate() {
                let off = i * lde_height;
                let sc = scale_of(pt);
                tasks.push(&resident, poly_height, off, i * width, &sc);
                inv_offsets.push(off);
                scales_flat.extend_from_slice(&sc);
            }
            let expected_interp = ws.interpolate(&tasks, pts.len() * width, ext_w);
            for sp in [&spilled_single, &spilled_multi] {
                let got_interp =
                    ws.interpolate_spilled(sp, poly_height, &inv_offsets, &scales_flat, ext_w);
                assert_eq!(
                    got_interp, expected_interp,
                    "spilled interp ext{ext_degree}"
                );
            }

            let alpha = EF::from_basis_coefficients_slice(&z0_coords[..ext_degree]).unwrap();
            let col_weights: Vec<EF> = alpha.powers().take(width).collect();
            let mut col_weights_flat = Vec::with_capacity(width * ext_degree);
            for &w in &col_weights {
                let (buf, d) = ext_to_goldilocks::<Goldilocks, EF>(w, ext_degree);
                col_weights_flat.extend_from_slice(&buf[..d]);
            }

            let mut expected_red =
                CudaReducedOpening::new_with_degree(device, lde_height, ext_degree);
            let mut red_tasks = CudaReductionTasks::new(ext_degree);
            let mut ys_flat = Vec::new();
            let mut offs_flat = Vec::new();
            for (i, _) in pts.iter().enumerate() {
                let y = alpha.exp_u64((i + 3) as u64);
                let off = alpha.exp_u64((i + 7) as u64);
                let (yb, d) = ext_to_goldilocks::<Goldilocks, EF>(y, ext_degree);
                let (ob, _) = ext_to_goldilocks::<Goldilocks, EF>(off, ext_degree);
                red_tasks.push(
                    &mut expected_red,
                    &resident,
                    i * lde_height,
                    &yb[..d],
                    &ob[..d],
                );
                ys_flat.extend_from_slice(&yb[..d]);
                offs_flat.extend_from_slice(&ob[..d]);
            }
            ws.reduce(&red_tasks, &col_weights_flat, ext_w);
            let expected_red_host = expected_red.into_lde().to_row_major_matrix();

            for sp in [&spilled_single, &spilled_multi] {
                let mut got_red =
                    CudaReducedOpening::new_with_degree(device, lde_height, ext_degree);
                ws.reduce_spilled(
                    &mut got_red,
                    sp,
                    &inv_offsets,
                    &ys_flat,
                    &offs_flat,
                    &col_weights_flat,
                    ext_w,
                );
                assert_eq!(
                    got_red.into_lde().to_row_major_matrix(),
                    expected_red_host,
                    "spilled reduce ext{ext_degree}"
                );
            }
        }

        drop(spilled_single);
        drop(spilled_multi);
        drop(pack);
        let _ = fs::remove_dir_all(&dir);
    }

    check_ext::<ExtVal2>(2, Goldilocks::from_u64(7));
    check_ext::<ExtVal3>(3, Goldilocks::ZERO);
}

#[test]
fn cuda_quotient_eval_blocks_and_panel_slice_match_cpu_ext2_and_ext3() {
    fn run_for_ext<SC, EF>(ext_degree: usize, ext_w: Goldilocks)
    where
        SC: ProofConfig<Challenge = EF>,
        SC::Pcs: crate::traits::Pcs<F = Goldilocks, Challenge = EF>,
        EF: TwoAdicField + ExtensionField<Goldilocks> + crate::traits::ExtensionOf<Goldilocks>,
    {
        let device = configured_device();
        let dft = CudaDft::without_auxiliary_devices(device);
        let cpu = Radix2DitParallel::<Goldilocks>::default();
        let dir = fresh_spill_dir(&format!("quotient-blocks-ext{ext_degree}"));

        let n = 64usize;
        let log_blowup = 2usize;
        let quotient_degree = 4usize;
        let quotient_size = n * quotient_degree;
        let lde_height = n << log_blowup;
        let lookup_count = 3usize;
        let group_size = 2usize;
        let s2_width = stage2_width(lookup_count, group_size, ext_degree);
        let n_publics = 4 * ext_degree;
        let ext = crate::system::extension_params::<SC>();

        let spec = CircuitSpec {
            main_width: 4,
            preprocessed_width: 3,
            stage2_width: s2_width,
            num_publics: n_publics,
            constraints: vec![
                Expr::IsFirstRow * Expr::main(0) + Expr::IsLastRow * Expr::main_next(1),
                Expr::IsTransition * (Expr::preprocessed_next(0) - Expr::main_next(0)),
                Expr::main(0) * Expr::main(1) * Expr::main(2) - Expr::main(3)
                    + Expr::preprocessed(2),
            ],
            ext_constraints: vec![
                ExtExpr::stage2(0, u32::try_from(ext_degree).unwrap(), RowOffset::Next)
                    - ExtExpr::stage2(0, u32::try_from(ext_degree).unwrap(), RowOffset::Current),
            ],
            lookups: (0..lookup_count)
                .map(|i| {
                    Lookup::push(
                        Expr::preprocessed(0) - Expr::constant(Goldilocks::from_usize(i)),
                        vec![
                            Expr::main_next(0),
                            Expr::preprocessed_next(1),
                            Expr::main(2),
                        ],
                    )
                })
                .collect(),
        };
        let graph = compile(&spec, &ext).unwrap();
        let constraint_count =
            graph.zeros.len() + logup_constraint_count(lookup_count, group_size, ext_degree);
        let circuit = Circuit {
            graph,
            main_width: 4,
            preprocessed: None,
            preprocessed_width: 3,
            preprocessed_height: n,
            num_lookups: lookup_count,
            stage_2_width: s2_width,
            num_publics: n_publics,
            lookup_group_size: group_size,
            constraint_count,
            max_constraint_degree: 5,
        };

        let prep_lde = random_matrix(0x4100 + ext_degree as u64, lde_height, 3);
        let main_lde = random_matrix(0x4200 + ext_degree as u64, lde_height, 4);
        let s2_lde = random_matrix(0x4300 + ext_degree as u64, lde_height, s2_width);
        let prep_gpu = CudaLde::from_row_major_matrix(device, &prep_lde);
        let main_gpu = CudaLde::from_row_major_matrix(device, &main_lde);
        let s2_gpu = CudaLde::from_row_major_matrix(device, &s2_lde);

        let mut pack = SpillPackWriter::create(&dir);
        let prep_sp = spill_as_multi_panel(&prep_gpu, &mut pack, &[1, 2]);
        let main_sp = spill_as_multi_panel(&main_gpu, &mut pack, &[2, 2]);
        let s2_sp = s2_gpu.spill_to_pack(&mut pack);
        pack.flush();

        let publics: Vec<Goldilocks> = (0..n_publics)
            .map(|i| Goldilocks::from_u64(17 + i as u64 * 13))
            .collect();
        let trace = TwoAdicMultiplicativeCoset::new(Goldilocks::ONE, log2_strict_usize(n)).unwrap();
        let quotient = TwoAdicMultiplicativeCoset::new(
            Goldilocks::GENERATOR,
            log2_strict_usize(quotient_size),
        )
        .unwrap();
        let selectors = CudaCosetSelectors {
            coset_shift: quotient.shift(),
            coset_generator: quotient.subgroup_generator(),
            trace_last: trace.subgroup_generator().inverse(),
            vanishing_start: quotient.shift().exp_u64(n as u64),
            vanishing_step: Goldilocks::two_adic_generator(log2_strict_usize(quotient_degree)),
        };
        let alpha_coords = [
            Goldilocks::from_u64(37),
            Goldilocks::from_u64(53),
            Goldilocks::from_u64(89),
        ];
        let alpha = EF::from_basis_coefficients_slice(&alpha_coords[..ext_degree]).unwrap();
        let mut powers = Vec::with_capacity(constraint_count);
        let mut p = <EF as PrimeCharacteristicRing>::ONE;
        for _ in 0..constraint_count {
            powers.push(p);
            p *= alpha;
        }
        powers.reverse();
        let mut alpha_flat = Vec::with_capacity(ext_degree * constraint_count);
        for c in 0..ext_degree {
            alpha_flat.extend(
                powers.iter().map(|v| {
                    <EF as BasedVectorSpace<Goldilocks>>::as_basis_coefficients_slice(v)[c]
                }),
            );
        }
        let norm = (Goldilocks::from_usize(n) * trace.subgroup_generator()).inverse();
        let delta: Vec<Goldilocks> = (0..ext_degree)
            .map(|c| (publics[3 * ext_degree + c] - publics[2 * ext_degree + c]) * norm)
            .collect();

        // Reference via existing resident kernels.
        let expected_vals = quotient_values_resident(
            &circuit.graph,
            Some(&prep_gpu),
            &main_gpu,
            &s2_gpu,
            &publics,
            selectors,
            &alpha_flat,
            &delta,
            ext_w,
            ext_degree,
            quotient_size,
            quotient_degree,
            group_size,
        );
        let expected_sliced = shifted_quotient_slices(
            &cpu,
            expected_vals.clone(),
            quotient.shift(),
            quotient_degree,
        );
        let expected_lde = lde_from_shifted_coefficients(&cpu, expected_sliced, log_blowup);

        // Test raw values (`forward_transform = false`) + transformed & panel-sliced
        // (`forward_transform = true`) across all Resident/Host/Spilled mixes!
        for mode in 0..3 {
            let (prep_src, main_src, s2_src) = match mode {
                0 => (
                    CudaMatrixSource::Spilled(&prep_sp),
                    CudaMatrixSource::Spilled(&main_sp),
                    CudaMatrixSource::Spilled(&s2_sp),
                ),
                1 => (
                    CudaMatrixSource::Resident(&prep_gpu),
                    CudaMatrixSource::Spilled(&main_sp),
                    CudaMatrixSource::Host(&s2_lde),
                ),
                _ => (
                    CudaMatrixSource::Host(&prep_lde),
                    CudaMatrixSource::Resident(&main_gpu),
                    CudaMatrixSource::Spilled(&s2_sp),
                ),
            };
            let (_, raw_vals) = quotient_eval_blocks(
                &dft,
                &circuit.graph,
                Some(prep_src),
                main_src,
                s2_src,
                &publics,
                selectors,
                &alpha_flat,
                &delta,
                ext_w,
                ext_degree,
                quotient_size,
                quotient_degree,
                group_size,
                4 << 20,
                false,
            );
            assert_eq!(
                raw_vals.unwrap(),
                expected_vals,
                "quotient_eval_blocks raw mismatch ext{ext_degree} mode={mode}"
            );

            let (transformed, _) = quotient_eval_blocks(
                &dft,
                &circuit.graph,
                Some(prep_src),
                main_src,
                s2_src,
                &publics,
                selectors,
                &alpha_flat,
                &delta,
                ext_w,
                ext_degree,
                quotient_size,
                quotient_degree,
                group_size,
                4 << 20,
                true,
            );
            let transformed = transformed.unwrap();

            // Full 1-shot slice panel.
            let full_panel = quotient_slice_panel_lde(
                &dft,
                &transformed,
                quotient_degree,
                n,
                0,
                quotient_degree,
                log_blowup,
            );
            assert_eq!(
                full_panel.to_row_major_matrix(),
                expected_lde,
                "full quotient_slice_panel_lde mismatch ext{ext_degree} mode={mode}"
            );

            // Multi-panel streaming (chunk_count = 1 -> 4 panels spilled to NVMe).
            let mut q_panels = Vec::new();
            for chunk in 0..quotient_degree {
                let p_lde = quotient_slice_panel_lde(
                    &dft,
                    &transformed,
                    quotient_degree,
                    n,
                    chunk,
                    1,
                    log_blowup,
                );
                q_panels.push(p_lde.spill_panel_to_pack(&mut pack));
            }
            pack.flush();
            let q_spilled = SpilledMatrix::from_panels(lde_height, q_panels);
            assert_eq!(
                q_spilled.read_all(),
                expected_lde,
                "multi-panel quotient_slice_panel_lde mismatch ext{ext_degree} mode={mode}"
            );
        }

        drop(prep_sp);
        drop(main_sp);
        drop(s2_sp);
        drop(pack);
        let _ = fs::remove_dir_all(&dir);
    }

    run_for_ext::<GoldilocksBlake3Config, ExtVal2>(2, Goldilocks::from_u64(7));
    run_for_ext::<GoldilocksBlake3V6Config, ExtVal3>(3, Goldilocks::ZERO);
}

#[test]
fn cuda_spilled_pcs_open_matches_cpu_spilled_v6_and_verifies_v6zk() {
    let device = configured_device();
    let dft = CudaDft::without_auxiliary_devices(device);
    let cpu_dft = Radix2DitParallel::<Goldilocks>::default();
    let dir = fresh_spill_dir("pcs-spilled-open");

    // Height 512 with lb=2 -> LDE height 2048 (> 1024 GPU streamed FRI threshold!).
    let n0 = 512usize;
    let n1 = 256usize;
    let log_blowup = 2usize;
    let t0 = random_matrix(0x5100, n0, 8);
    let t1 = random_matrix(0x5200, n1, 5);
    let d0 = TwoAdicMultiplicativeCoset::new(Goldilocks::ONE, log2_strict_usize(n0)).unwrap();
    let d1 = TwoAdicMultiplicativeCoset::new(Goldilocks::ONE, log2_strict_usize(n1)).unwrap();

    // 1. Protocol v6 (`ExtVal3`, Tensor, max_log_arity=3): compare CPU spilled
    //    PCS vs CUDA explicitly-spilled PCS byte-for-byte!
    let cfg_v6 = GoldilocksBlake3V6Config::with_device(
        CommitmentParameters {
            log_blowup,
            cap_height: 0,
        },
        FriParameters {
            log_final_poly_len: 1,
            max_log_arity: 3,
            num_queries: 8,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
        },
        FriBatching::Tensor,
        Some(device),
    );
    let mut cuda_mmcs = CudaMmcs::new_v6(0, device);
    cuda_mmcs.set_spill_dir(Some(dir.clone()));
    let cuda_fri = InnerFriParameters {
        log_blowup,
        log_final_poly_len: 1,
        max_log_arity: 3,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ExtensionMmcs::<Goldilocks, ExtVal3, CudaMmcs>::new(cuda_mmcs.clone()),
    };
    let mut cuda_pcs = CudaTwoAdicFriPcs::new(dft.clone(), cuda_mmcs.clone(), cuda_fri)
        .with_batching(FriBatching::Tensor);
    cuda_pcs.set_spill_dir(Some(dir.clone()));

    let mut pack = SpillPackWriter::create(&dir);
    let (sp0, dg0) = dft.coset_lde_spilled(
        &t0,
        log_blowup,
        Goldilocks::GENERATOR,
        &mut pack,
        Some((Blake3Domain::MerkleLeaf, None)),
    );
    let (sp1, dg1) = dft.coset_lde_spilled(
        &t1,
        log_blowup,
        Goldilocks::GENERATOR,
        &mut pack,
        Some((Blake3Domain::MerkleLeaf, None)),
    );
    pack.flush();
    let (gpu_sp_commit, gpu_sp_data) = cuda_mmcs.commit_cuda_mixed_spilled(
        vec![None, None],
        vec![None, None],
        vec![Some(sp0), Some(sp1)],
        vec![dg0, dg1],
        vec![None, None],
        Vec::new(),
    );

    let cpu_mmcs = SpillableMmcs::new_v6(0);
    let cpu_fri = InnerFriParameters {
        log_blowup,
        log_final_poly_len: 1,
        max_log_arity: 3,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ExtensionMmcs::<Goldilocks, ExtVal3, SpillableMmcs>::new(cpu_mmcs.clone()),
    };
    let mut cpu_pcs = SpillableTwoAdicFriPcs::new(cpu_dft.clone(), cpu_mmcs, cpu_fri)
        .with_batching(FriBatching::Tensor);
    cpu_pcs.set_spill_dir(Some(dir.clone()));
    let (cpu_sp_commit, cpu_sp_data) = <SpillableTwoAdicFriPcs<_, _> as Pcs<
        ExtVal3,
        crate::types::DomainChallenger<ExtVal3>,
    >>::commit(
        &cpu_pcs, vec![(d0, t0.clone()), (d1, t1.clone())]
    );
    assert_eq!(
        gpu_sp_commit, cpu_sp_commit,
        "v6 spilled commitment root must match CPU"
    );

    let zeta = ExtVal3::from_basis_coefficients_slice(&[
        Goldilocks::from_u64(19),
        Goldilocks::from_u64(31),
        Goldilocks::from_u64(43),
    ])
    .unwrap();
    let zeta_next0 = zeta * d0.subgroup_generator();
    let zeta_next1 = zeta * d1.subgroup_generator();
    let points = vec![vec![zeta, zeta_next0], vec![zeta, zeta_next1]];

    let mut ch_gpu = cfg_v6.initialise_challenger();
    let (opened_gpu, proof_gpu) = <CudaTwoAdicFriPcs<_, _, _, _> as Pcs<ExtVal3, _>>::open(
        &cuda_pcs,
        vec![(&gpu_sp_data, points.clone())],
        &mut ch_gpu,
    );
    let mut ch_cpu = cfg_v6.initialise_challenger();
    let (opened_cpu, proof_cpu) = <SpillableTwoAdicFriPcs<_, _> as Pcs<ExtVal3, _>>::open(
        &cpu_pcs,
        vec![(&cpu_sp_data, points)],
        &mut ch_cpu,
    );
    assert_eq!(
        opened_gpu, opened_cpu,
        "v6 spilled opened values must match CPU"
    );
    assert_eq!(
        proof_gpu.commit_phase_commits, proof_cpu.commit_phase_commits,
        "v6 spilled FRI commit roots must match CPU"
    );
    assert_eq!(proof_gpu.final_poly, proof_cpu.final_poly);

    // Cross-verify the GPU spilled proof with the CPU verifier via bincode wire format!
    let wire_cfg = bincode::config::standard()
        .with_little_endian()
        .with_fixed_int_encoding();
    let proof_gpu_bytes = bincode::serde::encode_to_vec(&proof_gpu, wire_cfg).unwrap();
    let proof_cpu_bytes = bincode::serde::encode_to_vec(&proof_cpu, wire_cfg).unwrap();
    assert_eq!(
        proof_gpu_bytes, proof_cpu_bytes,
        "v6 CUDA spilled FRI proof must be byte-for-byte identical to CPU spilled FRI proof"
    );
    type CpuV6SpillPcs = SpillableTwoAdicFriPcs<
        Radix2DitParallel<Goldilocks>,
        ExtensionMmcs<Goldilocks, ExtVal3, SpillableMmcs>,
    >;
    type CpuV6SpillProof =
        <CpuV6SpillPcs as Pcs<ExtVal3, crate::types::DomainChallenger<ExtVal3>>>::Proof;
    let (proof_for_cpu, _): (CpuV6SpillProof, usize) =
        bincode::serde::decode_from_slice(&proof_gpu_bytes, wire_cfg).unwrap();
    let mut ch_ver = cfg_v6.initialise_challenger();
    <SpillableTwoAdicFriPcs<_, _> as Pcs<ExtVal3, _>>::verify(
        &cpu_pcs,
        vec![(
            gpu_sp_commit,
            vec![
                (
                    d0,
                    vec![
                        (zeta, opened_gpu[0][0][0].clone()),
                        (zeta_next0, opened_gpu[0][0][1].clone()),
                    ],
                ),
                (
                    d1,
                    vec![
                        (zeta, opened_gpu[0][1][0].clone()),
                        (zeta_next1, opened_gpu[0][1][1].clone()),
                    ],
                ),
            ],
        )],
        &proof_for_cpu,
        &mut ch_ver,
    )
    .expect("CPU verifier must accept CUDA spilled v6 FRI proof");

    // 2. Protocol v6-zk (`ExtVal3`, Tensor, max_log_arity=3): spill via
    //    `HidingCudaMmcs::commit_cuda_mixed_spilled_with_seed`, open via CUDA
    //    streamed FRI, and cross-verify with CPU `HidingSpillableTwoAdicFriPcs`!
    let cfg_zk = GoldilocksBlake3V6ZkConfig::with_device(
        CommitmentParameters {
            log_blowup,
            cap_height: 0,
        },
        FriParameters {
            log_final_poly_len: 1,
            max_log_arity: 3,
            num_queries: 8,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
        },
        FriBatching::Tensor,
        Some(device),
    );
    let mut zk_cuda_mmcs = HidingCudaMmcs::new_v6_zk(0, device);
    zk_cuda_mmcs.set_spill_dir(Some(dir.clone()));
    let zk_cuda_fri = InnerFriParameters {
        log_blowup,
        log_final_poly_len: 1,
        max_log_arity: 3,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ExtensionMmcs::<Goldilocks, ExtVal3, HidingCudaMmcs>::new(zk_cuda_mmcs.clone()),
    };
    let mut zk_cuda_pcs =
        HidingCudaTwoAdicFriPcs::new(dft.clone(), zk_cuda_mmcs.clone(), zk_cuda_fri)
            .with_batching(FriBatching::Tensor);
    zk_cuda_pcs.set_spill_dir(Some(dir.clone()));

    let salt_seed = [0x99u8; 32];
    let b0 = crate::p3_adapter::zk::interleave_random_rows(&t0);
    let b1 = crate::p3_adapter::zk::interleave_random_rows(&t1);
    let (zsp0, zdg0) = dft.coset_lde_spilled(
        &b0,
        log_blowup,
        Goldilocks::GENERATOR,
        &mut pack,
        Some((Blake3Domain::ZkMerkleLeaf, Some(&salt_seed))),
    );
    let (zsp1, zdg1) = dft.coset_lde_spilled(
        &b1,
        log_blowup,
        Goldilocks::GENERATOR,
        &mut pack,
        Some((Blake3Domain::ZkMerkleLeaf, Some(&salt_seed))),
    );
    pack.flush();
    let (zk_gpu_commit, zk_gpu_data) = zk_cuda_mmcs.commit_cuda_mixed_spilled_with_seed(
        vec![None, None],
        vec![None, None],
        vec![Some(zsp0), Some(zsp1)],
        vec![zdg0, zdg1],
        Vec::new(),
        Vec::new(),
        salt_seed,
    );

    let mut ch_zk_gpu = cfg_zk.initialise_challenger();
    let (zk_opened, zk_proof) = <HidingCudaTwoAdicFriPcs<_, _, _, _> as Pcs<ExtVal3, _>>::open(
        &zk_cuda_pcs,
        vec![(
            &zk_gpu_data,
            vec![vec![zeta, zeta_next0], vec![zeta, zeta_next1]],
        )],
        &mut ch_zk_gpu,
    );

    let zk_cpu_mmcs = HidingSpillableMmcs::new_v6_zk(0);
    let zk_cpu_fri = InnerFriParameters {
        log_blowup,
        log_final_poly_len: 1,
        max_log_arity: 3,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: ExtensionMmcs::<Goldilocks, ExtVal3, HidingSpillableMmcs>::new(zk_cpu_mmcs.clone()),
    };
    let zk_cpu_pcs = HidingSpillableTwoAdicFriPcs::new(cpu_dft, zk_cpu_mmcs, zk_cpu_fri)
        .with_batching(FriBatching::Tensor);
    let zk_proof_bytes = bincode::serde::encode_to_vec(&zk_proof, wire_cfg).unwrap();
    type CpuV6ZkSpillPcs = HidingSpillableTwoAdicFriPcs<
        Radix2DitParallel<Goldilocks>,
        ExtensionMmcs<Goldilocks, ExtVal3, HidingSpillableMmcs>,
    >;
    type CpuV6ZkSpillProof =
        <CpuV6ZkSpillPcs as Pcs<ExtVal3, crate::types::DomainChallenger<ExtVal3>>>::Proof;
    let (zk_proof_for_cpu, _): (CpuV6ZkSpillProof, usize) =
        bincode::serde::decode_from_slice(&zk_proof_bytes, wire_cfg).unwrap();
    let mut ch_zk_ver = cfg_zk.initialise_challenger();
    <HidingSpillableTwoAdicFriPcs<_, _> as Pcs<ExtVal3, _>>::verify(
        &zk_cpu_pcs,
        vec![(
            zk_gpu_commit,
            vec![
                (
                    d0,
                    vec![
                        (zeta, zk_opened[0][0][0].clone()),
                        (zeta_next0, zk_opened[0][0][1].clone()),
                    ],
                ),
                (
                    d1,
                    vec![
                        (zeta, zk_opened[0][1][0].clone()),
                        (zeta_next1, zk_opened[0][1][1].clone()),
                    ],
                ),
            ],
        )],
        &zk_proof_for_cpu,
        &mut ch_zk_ver,
    )
    .expect("CPU verifier must accept CUDA spilled v6-zk FRI proof");

    drop(gpu_sp_data);
    drop(cpu_sp_data);
    drop(zk_gpu_data);
    drop(pack);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
#[ignore = "requires exclusive access to a CUDA device: reserves VRAM to force disk spilling"]
fn cuda_full_system_spilled_matches_resident_v5_v6_and_verifies_v6zk() {
    let device = configured_device();
    let dir = fresh_spill_dir("full-system-spilled");
    // Size traces so each LDE is >= 2.5 MiB (`65536 * 5 * 8`), exceeding
    // `round_resident_budget = 2 MiB` under the tight GPU reservation while
    // keeping GPU `coset_lde_spilled` and `quotient_eval_blocks` well within
    // the 8 MiB working budget.
    let n = 16384usize;

    let build_inputs = || {
        let mut prep_vals = Vec::with_capacity(n * 4);
        let mut main_vals = Vec::with_capacity(n * 5);
        for row in 0..n {
            let a = Goldilocks::from_usize(row + 1);
            let b = Goldilocks::from_usize(2 * row + 3);
            let c = a * b;
            let d = a + b;
            let e = c + d;
            prep_vals.push(Goldilocks::from_usize(row + 7));
            prep_vals.push(a);
            prep_vals.push(b);
            prep_vals.push(d);
            main_vals.push(a);
            main_vals.push(b);
            main_vals.push(c);
            main_vals.push(d);
            main_vals.push(e);
        }
        let prep = RowMajorMatrix::new(prep_vals, 4);
        let main = RowMajorMatrix::new(main_vals, 5);
        let inputs = vec![CircuitInputs {
            main_width: 5,
            preprocessed: Some(prep),
            constraints: vec![
                Expr::main(0) * Expr::main(1) - Expr::main(2),
                Expr::main(0) + Expr::main(1) - Expr::main(3),
                Expr::main(2) + Expr::main(3) - Expr::main(4),
                Expr::main(0) - Expr::preprocessed(1),
            ],
            lookups: vec![
                Lookup::push(
                    Expr::constant(Goldilocks::ONE),
                    vec![Expr::main(0), Expr::preprocessed(0)],
                ),
                Lookup::pull(
                    Expr::constant(Goldilocks::ONE),
                    vec![Expr::main(0), Expr::preprocessed(0)],
                ),
            ],
            lookup_group_size: 2,
            ..Default::default()
        }];
        (inputs, vec![main])
    };

    let comm = CommitmentParameters {
        log_blowup: 2,
        cap_height: 0,
    };
    let fri = FriParameters {
        log_final_poly_len: 1,
        max_log_arity: 2,
        num_queries: 8,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
    };

    // Unreserved CUDA reference proofs for v5 and v6.
    let (inputs_v5, traces_v5) = build_inputs();
    let cfg_v5_res =
        GoldilocksBlake3Config::with_device(comm, fri, Some(device)).without_disk_spill();
    let (sys_v5_res, key_v5_res) = System::new_without_preprocessed(cfg_v5_res, inputs_v5);
    let proof_v5_res = sys_v5_res.prove_multiple_claims_streaming(&key_v5_res, &[], traces_v5);
    sys_v5_res
        .verify_multiple_claims(&[], &proof_v5_res)
        .expect("v5 resident reference proof must verify");
    let expected_v5 = proof_v5_res.to_bytes().unwrap();

    let (inputs_v6, traces_v6) = build_inputs();
    let cfg_v6_res =
        GoldilocksBlake3V6Config::with_device(comm, fri, FriBatching::Tensor, Some(device))
            .without_disk_spill();
    let (sys_v6_res, key_v6_res) = System::new_without_preprocessed(cfg_v6_res, inputs_v6);
    let proof_v6_res = sys_v6_res.prove_multiple_claims_streaming(&key_v6_res, &[], traces_v6);
    sys_v6_res
        .verify_multiple_claims(&[], &proof_v6_res)
        .expect("v6 resident reference proof must verify");
    let expected_v6 = proof_v6_res.to_bytes().unwrap();

    // Reserve VRAM so `round_resident_budget = (136 MiB - 128 MiB) / 4 = 2 MiB`
    // while keeping 8 MiB headroom above reserve for GPU `coset_lde_spilled`
    // and `quotient_eval_blocks`, AND reserve `1 TiB` to verify full CPU
    // streaming fallback. Test BOTH!
    let (free_now, _) = device_memory_info(device);
    let tight_reserve = free_now.saturating_sub(136usize << 20);
    for (label, reserve_bytes) in [("gpu-spill", tight_reserve), ("full-reserve", 1usize << 40)] {
        let _reservation = DeviceMemoryReservation::new(device, reserve_bytes);

        let (inputs_v5_sp, traces_v5_sp) = build_inputs();
        let cfg_v5_sp =
            GoldilocksBlake3Config::with_device(comm, fri, Some(device)).with_disk_spill(&dir);
        let (sys_v5_sp, key_v5_sp) = System::new_without_preprocessed(cfg_v5_sp, inputs_v5_sp);
        assert!(
            active_spill_files() > 0,
            "v5 ({label}) should spill preprocessed LDE to NVMe under tight VRAM budget"
        );
        let proof_v5_sp = sys_v5_sp.prove_multiple_claims_streaming(&key_v5_sp, &[], traces_v5_sp);
        sys_v5_sp
            .verify_multiple_claims(&[], &proof_v5_sp)
            .unwrap_or_else(|e| panic!("v5 CUDA disk-spilled ({label}) verify failed: {e:?}"));
        assert_eq!(
            proof_v5_sp.to_bytes().unwrap(),
            expected_v5,
            "v5 CUDA disk-spilled ({label}) proof must be byte-identical to CUDA resident proof"
        );
        drop(key_v5_sp);

        let (inputs_v6_sp, traces_v6_sp) = build_inputs();
        let cfg_v6_sp =
            GoldilocksBlake3V6Config::with_device(comm, fri, FriBatching::Tensor, Some(device))
                .with_disk_spill(&dir);
        let (sys_v6_sp, key_v6_sp) = System::new_without_preprocessed(cfg_v6_sp, inputs_v6_sp);
        assert!(
            active_spill_files() > 0,
            "v6 ({label}) should spill preprocessed LDE to NVMe under tight VRAM budget"
        );
        let proof_v6_sp = sys_v6_sp.prove_multiple_claims_streaming(&key_v6_sp, &[], traces_v6_sp);
        sys_v6_sp
            .verify_multiple_claims(&[], &proof_v6_sp)
            .unwrap_or_else(|e| panic!("v6 CUDA disk-spilled ({label}) verify failed: {e:?}"));
        assert_eq!(
            proof_v6_sp.to_bytes().unwrap(),
            expected_v6,
            "v6 CUDA disk-spilled ({label}) proof must be byte-identical to CUDA resident proof"
        );
        drop(key_v6_sp);

        let (inputs_zk, traces_zk) = build_inputs();
        let comm_zk = CommitmentParameters {
            log_blowup: 3,
            cap_height: 0,
        };
        let cfg_zk_sp = GoldilocksBlake3V6ZkConfig::with_device(
            comm_zk,
            fri,
            FriBatching::Tensor,
            Some(device),
        )
        .with_disk_spill(&dir);
        let (sys_zk_sp, key_zk_sp) = System::new_without_preprocessed(cfg_zk_sp, inputs_zk);
        assert!(
            active_spill_files() > 0,
            "v6-zk ({label}) should spill preprocessed LDE to NVMe under tight VRAM budget"
        );
        let proof_zk_sp = sys_zk_sp.prove_multiple_claims_streaming(&key_zk_sp, &[], traces_zk);
        sys_zk_sp
            .verify_multiple_claims(&[], &proof_zk_sp)
            .unwrap_or_else(|e| {
                panic!("v6-zk CUDA disk-spilled ({label}) proof must verify: {e:?}")
            });
        drop(key_zk_sp);
    }

    assert_eq!(
        active_spill_files(),
        0,
        "zero spill files may leak after drop"
    );
    assert_eq!(fs::read_dir(&dir).unwrap().count(), 0);
    let _ = fs::remove_dir_all(&dir);
}
