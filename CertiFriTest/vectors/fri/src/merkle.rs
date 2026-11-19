//! Merkle openings of `MerkleTreeMmcs` with a two-to-one compression,
//! power-of-two heights and a single root: the classical one-path-per-index
//! check, and the unpacking of Plonky3's pruned multi-opening proof into one
//! full path per query.

use std::collections::BTreeMap;

use crate::config::{Digest, Val};
use crate::model::{compress, hash_vals};

/// Dimensions of one committed matrix, in base-field columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dim {
    pub width: usize,
    pub log_height: usize,
}

fn max_log_height(dims: &[Dim]) -> usize {
    dims.iter()
        .map(|d| d.log_height)
        .max()
        .expect("no matrices")
}

/// The rows of the matrices of log-height `h`, concatenated in batch order.
fn group_rows(dims: &[Dim], rows: &[Vec<Val>], h: usize) -> Option<Vec<Val>> {
    let mut group = vec![];
    let mut any = false;
    for (dim, row) in dims.iter().zip(rows) {
        if dim.log_height == h {
            any = true;
            group.extend_from_slice(row);
        }
    }
    any.then_some(group)
}

/// The digest a node of the layer of log-height `h` has once the matrices of
/// that height, if there are any, are injected into it.
fn inject(dims: &[Dim], rows: &[Vec<Val>], h: usize, digest: Digest) -> Digest {
    match group_rows(dims, rows, h) {
        Some(group) => compress(&digest, &hash_vals(&group)),
        None => digest,
    }
}

/// Recompute the root from the rows opened at one index and one full path.
///
/// `rows[m]` is the row of matrix `m` at `index >> (top - dims[m].log_height)`,
/// where `top` is the largest log-height. `path[l]` is the sibling of the node
/// on the way up at level `l`, the leaf level being level 0; there are `top`
/// of them.
///
/// * The leaf is the hash of the rows of the tallest matrices, concatenated in
///   batch order.
/// * Going up one level compresses the node with its sibling, the node on the
///   left when bit `l` of `index` is 0.
/// * Whenever the layer just reached is as wide as some matrices are tall, the
///   node is compressed once more, on the left, with the hash of the rows of
///   those matrices on the right.
pub fn root_from_path(
    dims: &[Dim],
    index: usize,
    rows: &[Vec<Val>],
    path: &[Digest],
) -> Result<Digest, String> {
    if dims.is_empty() {
        return Err("no matrices".into());
    }
    if rows.len() != dims.len() {
        return Err("one row per matrix expected".into());
    }
    if dims.iter().zip(rows).any(|(d, r)| r.len() != d.width) {
        return Err("a row has the wrong width".into());
    }
    let top = max_log_height(dims);
    if path.len() != top {
        return Err(format!("path has {} siblings, expected {top}", path.len()));
    }
    if index >> top != 0 {
        return Err("index out of range".into());
    }
    let mut digest = hash_vals(&group_rows(dims, rows, top).unwrap());
    for (level, sibling) in path.iter().enumerate() {
        digest = if (index >> level) & 1 == 0 {
            compress(&digest, sibling)
        } else {
            compress(sibling, &digest)
        };
        digest = inject(dims, rows, top - level - 1, digest);
    }
    Ok(digest)
}

/// Unpack a pruned multi-opening proof (`PrunedMerklePaths::sibling_hashes`)
/// into one full path per query, and return the root the proof leads to.
///
/// The pruned proof lists, level by level from the leaves, for each parent of
/// a node on some query's way up in ascending order, the child that is not on
/// any query's way up (if there is one). A sibling that is on another query's
/// way up is not in the proof; it is recomputed here, exactly as the verifier
/// recomputes it.
pub fn restore_paths(
    dims: &[Dim],
    indices: &[usize],
    rows: &[Vec<Vec<Val>>],
    pruned: &[Digest],
) -> (Vec<Vec<Digest>>, Digest) {
    assert_eq!(indices.len(), rows.len());
    assert!(!indices.is_empty());
    let top = max_log_height(dims);

    // nodes[level][i]: digest of node `i` of the layer `level` levels above
    // the leaves, as it enters the compression (after injection).
    let mut nodes: Vec<BTreeMap<usize, Digest>> = vec![];
    // The nodes on some query's way up, with one query that passes through.
    let mut frontier: BTreeMap<usize, (Digest, usize)> = BTreeMap::new();
    for (query, &index) in indices.iter().enumerate() {
        assert!(index >> top == 0);
        let leaf = hash_vals(&group_rows(dims, &rows[query], top).unwrap());
        if let Some((digest, _)) = frontier.get(&index) {
            assert_eq!(*digest, leaf, "two queries of one index disagree");
        } else {
            frontier.insert(index, (leaf, query));
        }
    }

    let mut supplied = pruned.iter();
    for level in 0..top {
        let mut layer: BTreeMap<usize, Digest> =
            frontier.iter().map(|(&i, &(d, _))| (i, d)).collect();
        let mut parents: BTreeMap<usize, (Digest, usize)> = BTreeMap::new();
        // Ascending parent index; within a parent, left child before right.
        for (&index, &(_, query)) in &frontier {
            let parent = index >> 1;
            if parents.contains_key(&parent) {
                continue;
            }
            for child in [2 * parent, 2 * parent + 1] {
                if !frontier.contains_key(&child) {
                    let digest = supplied.next().expect("pruned proof too short");
                    layer.insert(child, *digest);
                }
            }
            let digest = compress(&layer[&(2 * parent)], &layer[&(2 * parent + 1)]);
            let digest = inject(dims, &rows[query], top - level - 1, digest);
            parents.insert(parent, (digest, query));
        }
        nodes.push(layer);
        frontier = parents;
    }
    assert!(supplied.next().is_none(), "pruned proof too long");
    assert_eq!(frontier.len(), 1);
    let root = frontier[&0].0;

    let paths = indices
        .iter()
        .map(|&index| {
            (0..top)
                .map(|level| nodes[level][&((index >> level) ^ 1)])
                .collect()
        })
        .collect();
    (paths, root)
}
