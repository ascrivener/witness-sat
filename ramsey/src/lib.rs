//! Witness check for Ramsey lower bounds: the witness is a graph on `n` vertices with no clique
//! of size `s` and no independent set of size `t`, which proves R(s, t) > n.
//!
//! - **Params:** three bytes, `n`, `s` and `t`, with 2 ≤ s, t ≤ n ≤ [`MAX_N`].
//! - **Witness:** the graph's upper triangle, row by row: bit `k` (least significant first in
//!   each byte) is the edge `(i, j)`, `i < j`, `k`th in the order (0, 1), (0, 2), …, (0, n − 1),
//!   (1, 2), …. Exactly ⌈n(n − 1)/16⌉ bytes, and the padding bits after the last edge are zero,
//!   so each graph has one witness.
//!
//! A bounty with params `42 5 5` pays for a graph proving R(5, 5) ≥ 43, which Exoo found in 1989;
//! one with `43 5 5` would prove R(5, 5) ≥ 44, which is open.
//!
//! The search is over vertex bitsets, so it touches only the cliques it has to: it extends a
//! clique only by vertices adjacent to all of it, and gives up on a branch with too few left.

#![cfg_attr(not(test), no_std)]

/// The most vertices a graph may have: a vertex's neighbourhood is one `u64`.
pub const MAX_N: usize = 64;

/// The bytes a witness for a graph on `n` vertices takes.
pub const fn witness_len(n: usize) -> usize {
	(n * (n.saturating_sub(1)) / 2).div_ceil(8)
}

/// Decode a witness into adjacency bitsets; `None` unless it is exactly one for `n` vertices.
pub fn decode(n: usize, x: &[u8]) -> Option<[u64; MAX_N]> {
	if !(1..=MAX_N).contains(&n) || x.len() != witness_len(n) {
		return None;
	}
	let mut adj = [0u64; MAX_N];
	let mut k = 0;
	for i in 0..n {
		for j in i + 1..n {
			if x[k / 8] >> (k % 8) & 1 == 1 {
				adj[i] |= 1 << j;
				adj[j] |= 1 << i;
			}
			k += 1;
		}
	}
	// Padding bits must be clear.
	if k % 8 != 0 && x[k / 8] >> (k % 8) != 0 {
		return None;
	}
	Some(adj)
}

/// Whether the vertices in `cand` hold a clique of `k` more vertices, in the graph `adj`.
fn has_clique(adj: &[u64; MAX_N], mut cand: u64, k: u32) -> bool {
	if k == 0 {
		return true;
	}
	while cand.count_ones() >= k {
		let v = cand.trailing_zeros() as usize;
		cand &= cand - 1;
		// The rest of the clique comes from `v`'s neighbours after it.
		if has_clique(adj, adj[v] & cand, k - 1) {
			return true;
		}
	}
	false
}

/// Whether the graph on `n` vertices has neither a clique of size `s` nor an independent set of
/// size `t`.
pub fn is_ramsey(adj: &[u64; MAX_N], n: usize, s: u32, t: u32) -> bool {
	let all = if n == 64 { u64::MAX } else { (1 << n) - 1 };
	let mut complement = [0u64; MAX_N];
	for v in 0..n {
		complement[v] = !adj[v] & all & !(1 << v);
	}
	!has_clique(adj, all, s) && !has_clique(&complement, all, t)
}

fn check(params: &[u8], x: &[u8]) -> bool {
	let &[n, s, t] = params else { return false };
	let (n, s, t) = (n as usize, s as u32, t as u32);
	if s < 2 || t < 2 || s as usize > n || t as usize > n {
		return false;
	}
	decode(n, x).is_some_and(|adj| is_ramsey(&adj, n, s, t))
}

witness_check::declare_check!(check);

#[cfg(test)]
mod tests;
