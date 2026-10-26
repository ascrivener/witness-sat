//! A formula's clauses in a Merkle tree, and proofs that some of them are in it.
//!
//! The tree is witness's (`witness_types::merkle`): leaves are `blake2b(0x00 ++ blake2b(clause))`
//! for each clause's encoding, inner nodes `blake2b(0x01 ++ left ++ right)`, and an odd node at
//! the end of a level is carried up as it is. So the root of a formula is the root an attestation
//! of its clauses, in order, would have.
//!
//! A chunk proves the formula's clauses it uses with one *multiproof*: the hashes, level by level
//! from the leaves and left to right within a level, of every node it needs but can't compute,
//! namely the siblings of nodes it can that aren't themselves computable.

use alloc::vec::Vec;

pub type Hash = [u8; 32];

pub fn blake2b256(data: &[u8]) -> Hash {
	let h = blake2b_simd::Params::new().hash_length(32).hash(data);
	let mut out = [0; 32];
	out.copy_from_slice(h.as_bytes());
	out
}

/// The leaf of the clause whose encoding is `clause`.
pub fn leaf(clause: &[u8]) -> Hash {
	let mut data = [0u8; 33];
	data[1..].copy_from_slice(&blake2b256(clause));
	blake2b256(&data)
}

pub fn node(left: &Hash, right: &Hash) -> Hash {
	let mut data = [0u8; 65];
	data[0] = 1;
	data[1..33].copy_from_slice(left);
	data[33..].copy_from_slice(right);
	blake2b256(&data)
}

/// Walk up from `level`, leaves `(index, hash)` in increasing index order of a tree of `width`
/// leaves, to the root. A sibling not in the level comes from `sibling`, given its depth (0 for
/// leaves) and index: reading a proof, or writing one.
fn climb(mut level: Vec<(u32, Hash)>, mut width: u32, mut sibling: impl FnMut(usize, u32) -> Option<Hash>) -> Option<Hash> {
	let mut depth = 0;
	while width > 1 {
		let mut next = Vec::with_capacity(level.len());
		let mut k = 0;
		while k < level.len() {
			let (i, h) = level[k];
			let parent = if i % 2 == 1 {
				node(&sibling(depth, i - 1)?, &h)
			} else if i + 1 >= width {
				h
			} else if level.get(k + 1).is_some_and(|&(j, _)| j == i + 1) {
				k += 1;
				node(&h, &level[k].1)
			} else {
				node(&h, &sibling(depth, i + 1)?)
			};
			next.push((i / 2, parent));
			k += 1;
		}
		level = next;
		width = width.div_ceil(2);
		depth += 1;
	}
	level.first().map(|&(_, h)| h)
}

/// Whether `proof` shows the leaves `(index, hash)`, in strictly increasing index order, are in the
/// tree of `width` leaves with root `root`. No leaves need no proof.
pub fn verify(root: &Hash, width: u32, leaves: Vec<(u32, Hash)>, proof: &[Hash]) -> bool {
	if leaves.is_empty() {
		return proof.is_empty();
	}
	if leaves.windows(2).any(|w| w[0].0 >= w[1].0) || leaves.last().is_some_and(|&(i, _)| i >= width) {
		return false;
	}
	let mut proof = proof.iter();
	climb(leaves, width, |_, _| proof.next().copied()).is_some_and(|r| r == *root) && proof.next().is_none()
}

/// The levels of the tree over `leaves`, from the leaves up to the root.
pub fn levels(leaves: Vec<Hash>) -> Vec<Vec<Hash>> {
	let mut levels = alloc::vec![leaves];
	while levels.last().unwrap().len() > 1 {
		let up = levels.last().unwrap().chunks(2).map(|p| if let [l, r] = p { node(l, r) } else { p[0] }).collect();
		levels.push(up);
	}
	levels
}

/// The multiproof for leaves `indices` (strictly increasing) of the tree with these `levels`.
pub fn prove(levels: &[Vec<Hash>], indices: &[u32]) -> Vec<Hash> {
	let mut proof = Vec::new();
	if !indices.is_empty() {
		let leaves = indices.iter().map(|&i| (i, levels[0][i as usize])).collect();
		climb(leaves, levels[0].len() as u32, |depth, i| {
			proof.push(levels[depth][i as usize]);
			Some(levels[depth][i as usize])
		});
	}
	proof
}
