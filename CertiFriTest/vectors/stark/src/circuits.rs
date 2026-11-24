//! The two systems the vectors are proofs of, and their traces.
//!
//! No lookup expression uses a row selector: multi-stark evaluates selectors
//! as 0 or 1 when it builds the lookup witness, but as Plonky3's unnormalized
//! selector polynomials in the constraints, so the two would disagree.

use multi_stark::expr::{Expr, ExtExpr, RowOffset};
use multi_stark::lookup::Lookup;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::system::CircuitInputs;

use crate::config::{EXTENSION_DEGREE, Val};

type E = Expr<Val>;

fn val(x: u64) -> Val {
    Val::from_u64(x)
}

fn constant(x: u64) -> E {
    E::constant(val(x))
}

fn main(index: u32) -> E {
    E::main(index)
}

fn main_next(index: u32) -> E {
    E::main_next(index)
}

fn fixed(index: u32) -> E {
    E::preprocessed(index)
}

fn fixed_next(index: u32) -> E {
    E::preprocessed_next(index)
}

/// `x * (x - 1)`.
fn boolean(x: E) -> E {
    x.clone() * (x - constant(1))
}

fn matrix(rows: &[Vec<u64>], width: usize) -> RowMajorMatrix<Val> {
    assert!(rows.iter().all(|row| row.len() == width));
    RowMajorMatrix::new(rows.iter().flatten().map(|&x| val(x)).collect(), width)
}

/// The trace of a circuit that is inactive in a proof.
pub fn empty(width: usize) -> RowMajorMatrix<Val> {
    RowMajorMatrix::new(vec![], width)
}

/// Two circuits without fixed columns, of constraint degree 2.
///
/// * `sequence` (circuit 0) lists the Fibonacci numbers and pushes the rows it
///   selects.
/// * `reader` (circuit 1) pulls rows of `sequence`, and for some of them a
///   claim `[n, F_n]`.
pub mod fibonacci {
    use super::*;

    pub const SEQUENCE_WIDTH: usize = 4;
    pub const READER_WIDTH: usize = 5;

    pub fn circuits() -> Vec<CircuitInputs<Val>> {
        // Columns `i, a, b, s`: row `i` holds `a = F_i`, `b = F_(i+1)`, and
        // is pushed as `[i, a, b]` when `s = 1`. The last row is always
        // pushed.
        let (i, a, b, s) = (0, 1, 2, 3);
        let sequence = CircuitInputs {
            main_width: SEQUENCE_WIDTH,
            constraints: vec![
                E::IsFirstRow * main(i),
                E::IsFirstRow * main(a),
                E::IsFirstRow * (main(b) - constant(1)),
                E::IsTransition * (main_next(i) - main(i) - constant(1)),
                E::IsTransition * (main_next(a) - main(b)),
                E::IsTransition * (main_next(b) - main(a) - main(b)),
                boolean(main(s)),
                E::IsLastRow * (main(s) - constant(1)),
            ],
            lookups: vec![Lookup::push(main(s), vec![main(i), main(a), main(b)])],
            ..Default::default()
        };

        // Columns `n, f, g, m, c`: when `m = 1` the row pulls `[n, f, g]`,
        // and when also `c = 1` it pulls the claim `[n, f]`.
        let (n, f, g, m, c) = (0, 1, 2, 3, 4);
        let reader = CircuitInputs {
            main_width: READER_WIDTH,
            constraints: vec![
                boolean(main(m)),
                boolean(main(c)),
                main(c) * (main(m) - constant(1)),
            ],
            lookups: vec![
                Lookup::pull(main(m), vec![main(n), main(f), main(g)]),
                Lookup::pull(main(c), vec![main(n), main(f)]),
            ],
            ..Default::default()
        };
        vec![sequence, reader]
    }

    /// `(F_i, F_(i+1))`.
    fn pair(i: usize) -> (u64, u64) {
        (0..i).fold((0, 1), |(a, b), _| (b, a + b))
    }

    /// The trace of `sequence` with `2^log_height` rows, pushing the given
    /// rows.
    pub fn sequence(log_height: usize, pushed: &[usize]) -> RowMajorMatrix<Val> {
        let rows: Vec<Vec<u64>> = (0..1 << log_height)
            .map(|i| {
                let (a, b) = pair(i);
                vec![i as u64, a, b, pushed.contains(&i) as u64]
            })
            .collect();
        matrix(&rows, SEQUENCE_WIDTH)
    }

    /// The trace of `reader`: `Some((n, claimed))` pulls row `n` of
    /// `sequence`, and the claim `[n, F_n]` if `claimed`; `None` is a row
    /// that pulls nothing.
    pub fn reader(rows: &[Option<(usize, bool)>]) -> RowMajorMatrix<Val> {
        let rows: Vec<Vec<u64>> = rows
            .iter()
            .map(|row| match *row {
                Some((n, claimed)) => {
                    let (f, g) = pair(n);
                    vec![n as u64, f, g, 1, claimed as u64]
                }
                None => vec![0; READER_WIDTH],
            })
            .collect();
        matrix(&rows, READER_WIDTH)
    }

    /// The claim `[n, F_n]`.
    pub fn claim(n: usize) -> Vec<Val> {
        vec![val(n as u64), val(pair(n).0)]
    }

    /// The message `[n, F_n, F_(n+1)]` that `sequence` pushes for row `n`.
    pub fn row_message(n: usize) -> Vec<Val> {
        let (f, g) = pair(n);
        vec![val(n as u64), val(f), val(g)]
    }
}

/// Four circuits, two of them with fixed columns, of constraint degrees 3, 2,
/// 2 and 5.
///
/// * `sums` (circuit 0) holds pairs `a, b` with their cubes, looks both cubes
///   up in `table`, and pulls a claim `[100, a^3 + b^3]`. Its three lookups
///   are grouped by two.
/// * `table` (circuit 1) has the fixed columns `x, x^3` for `x = 0..8`.
/// * `spare` (circuit 2) is never given a trace.
/// * `rounds` (circuit 3) has a fixed column of round constants and no
///   lookups.
pub mod cubes {
    use super::*;

    pub const SUMS_WIDTH: usize = 5;
    pub const TABLE_WIDTH: usize = 1;
    pub const SPARE_WIDTH: usize = 2;
    pub const ROUNDS_WIDTH: usize = 2;

    /// The first argument of a claim.
    pub const CLAIM_TAG: u64 = 100;
    const SPARE_TAG: u64 = 200;
    const TABLE_LOG_HEIGHT: usize = 3;
    const ROUND_CONSTANTS: [u64; 4] = [3, 5, 7, 11];
    const ROUNDS_START: u64 = 2;

    pub fn circuits() -> Vec<CircuitInputs<Val>> {
        let d = EXTENSION_DEGREE as u32;
        let stage2 = |slot: u32| ExtExpr::stage2(slot, d, RowOffset::Current);

        // Columns `a, b, a3, b3, s`. Stage 2 has two accumulator slots: slot
        // 0 enters the group of the first two lookups, slot 1 the group of
        // the third. The prover starts slot 0 at zero, which the two
        // extension constraints state: the second multiplies two extension
        // values that are not embedded base values.
        let (a, b, a3, b3, s) = (0, 1, 2, 3, 4);
        let starts_at_zero = ExtExpr::from(E::IsFirstRow) * stage2(0);
        let sums = CircuitInputs {
            main_width: SUMS_WIDTH,
            constraints: vec![boolean(main(s))],
            ext_constraints: vec![starts_at_zero.clone(), starts_at_zero * stage2(1)],
            lookups: vec![
                Lookup::push(main(s), vec![main(a), main(a3)]),
                Lookup::push(main(s), vec![main(b), main(b3)]),
                Lookup::pull(main(s), vec![constant(CLAIM_TAG), main(a3) + main(b3)]),
            ],
            lookup_group_size: 2,
            ..Default::default()
        };

        // Fixed columns `x, x^3`; the main column is the number of times the
        // row is looked up. The constraint reads the next fixed row.
        let table_rows: Vec<Vec<u64>> = (0..1u64 << TABLE_LOG_HEIGHT)
            .map(|x| vec![x, x * x * x])
            .collect();
        let table = CircuitInputs {
            main_width: TABLE_WIDTH,
            preprocessed: Some(matrix(&table_rows, 2)),
            constraints: vec![E::IsTransition * (fixed_next(0) - fixed(0) - constant(1))],
            lookups: vec![Lookup::pull(main(0), vec![fixed(0), fixed(1)])],
            ..Default::default()
        };

        // Columns `u, v`, on a channel of its own.
        let spare = CircuitInputs {
            main_width: SPARE_WIDTH,
            constraints: vec![boolean(main(0))],
            lookups: vec![Lookup::pull(main(0), vec![constant(SPARE_TAG), main(1)])],
            ..Default::default()
        };

        // Fixed column `k`; columns `x, y` with `x' = x^5 + k` and `y` the
        // running sum of `k`, read from the next fixed row. Without lookups
        // the accumulator passes through unchanged, which the two extension
        // constraints state on the public values and on the stage-2 column.
        let (x, y) = (0, 1);
        let x5 = main(x) * main(x) * main(x) * main(x) * main(x);
        let total: u64 = ROUND_CONSTANTS.iter().sum();
        let rounds = CircuitInputs {
            main_width: ROUNDS_WIDTH,
            preprocessed: Some(matrix(&ROUND_CONSTANTS.map(|k| vec![k]), 1)),
            constraints: vec![
                E::IsFirstRow * (main(x) - constant(ROUNDS_START)),
                E::IsTransition * (main_next(x) - x5 - fixed(0)),
                E::IsFirstRow * (main(y) - fixed(0)),
                E::IsTransition * (main_next(y) - main(y) - fixed_next(0)),
                E::IsLastRow * (main(y) - constant(total)),
            ],
            ext_constraints: vec![
                ExtExpr::public(3, d) - ExtExpr::public(2, d),
                (ExtExpr::stage2(0, d, RowOffset::Next) - stage2(0)) * ExtExpr::public(1, d),
            ],
            ..Default::default()
        };
        vec![sums, table, spare, rounds]
    }

    /// The trace of `sums` for the given pairs, padded with rows that look
    /// nothing up.
    pub fn sums(pairs: &[(u64, u64)], log_height: usize) -> RowMajorMatrix<Val> {
        let height = 1 << log_height;
        assert!(pairs.len() <= height);
        let mut rows: Vec<Vec<u64>> = pairs
            .iter()
            .map(|&(a, b)| vec![a, b, a * a * a, b * b * b, 1])
            .collect();
        rows.resize(height, vec![0; SUMS_WIDTH]);
        matrix(&rows, SUMS_WIDTH)
    }

    /// The trace of `table` that serves the given pairs.
    pub fn table(pairs: &[(u64, u64)]) -> RowMajorMatrix<Val> {
        let mut counts = [0u64; 1 << TABLE_LOG_HEIGHT];
        for &(a, b) in pairs {
            counts[a as usize] += 1;
            counts[b as usize] += 1;
        }
        matrix(
            &counts.iter().map(|&m| vec![m]).collect::<Vec<_>>(),
            TABLE_WIDTH,
        )
    }

    /// The trace of `rounds`.
    pub fn rounds() -> RowMajorMatrix<Val> {
        let mut x = val(ROUNDS_START);
        let mut y = Val::ZERO;
        let mut values = vec![];
        for k in ROUND_CONSTANTS {
            y += val(k);
            values.extend([x, y]);
            x = x * x * x * x * x + val(k);
        }
        RowMajorMatrix::new(values, ROUNDS_WIDTH)
    }

    /// The claim `[100, a^3 + b^3]`.
    pub fn claim((a, b): (u64, u64)) -> Vec<Val> {
        vec![val(CLAIM_TAG), val(a * a * a + b * b * b)]
    }
}
