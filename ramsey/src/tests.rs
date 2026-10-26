use super::*;
use witness_types::{CheckMode, check_args};

/// Encode the graph on `n` vertices with edges where `edge(i, j)`, `i < j`, as a witness.
fn encode(n: usize, edge: impl Fn(usize, usize) -> bool) -> Vec<u8> {
	let mut x = vec![0u8; witness_len(n)];
	let mut k = 0;
	for i in 0..n {
		for j in i + 1..n {
			if edge(i, j) {
				x[k / 8] |= 1 << (k % 8);
			}
			k += 1;
		}
	}
	x
}

/// The Paley graph on a prime `p ≡ 1 (mod 4)`: `i ~ j` when `j − i` is a nonzero square mod p.
fn paley(p: usize) -> Vec<u8> {
	let squares: Vec<bool> = (0..p).map(|a| (1..p).any(|b| b * b % p == a)).collect();
	encode(p, |i, j| squares[(j - i) % p])
}

/// Whether some `k` of the `n` vertices are pairwise `related`, by trying every `k`-subset.
fn naive_has(n: usize, k: usize, related: &dyn Fn(usize, usize) -> bool) -> bool {
	fn go(n: usize, k: usize, from: usize, chosen: &mut Vec<usize>, related: &dyn Fn(usize, usize) -> bool) -> bool {
		if chosen.len() == k {
			return true;
		}
		(from..n).any(|v| {
			if !chosen.iter().all(|&u| related(u, v)) {
				return false;
			}
			chosen.push(v);
			let found = go(n, k, v + 1, chosen, related);
			chosen.pop();
			found
		})
	}
	go(n, k, 0, &mut Vec::new(), related)
}

fn run(params: &[u8], x: &[u8]) -> bool {
	witness_check::run_simple(&check_args(CheckMode::Reveal, &[], params, x), check) == 1
}

#[test]
fn small_cases() {
	// The 5-cycle has no triangle and no independent set of 3: R(3, 3) > 5.
	let c5 = encode(5, |i, j| j - i == 1 || j - i == 4);
	assert!(run(&[5, 3, 3], &c5));
	// K6 minus anything still has one or the other: R(3, 3) = 6.
	assert!(!run(&[6, 3, 3], &encode(6, |i, j| (j - i) % 2 == 1)));
	// The empty graph on 4 vertices has an independent set of 4, but not of 5.
	let empty = encode(4, |_, _| false);
	assert!(!run(&[4, 2, 4], &empty));
	assert!(run(&[4, 2, 5], &[0]) == false, "t > n is malformed");
}

#[test]
fn paley_17_is_the_ramsey_4_4_graph() {
	let g = paley(17);
	assert!(run(&[17, 4, 4], &g), "R(4, 4) > 17");
	assert!(!run(&[17, 3, 4], &g), "it has triangles");
	// It's the only (4, 4)-graph on 17 vertices, so flipping any edge makes a K4 or an
	// independent 4-set: every edge matters.
	for k in 0..17 * 16 / 2 {
		let mut bad = g.clone();
		bad[k / 8] ^= 1 << (k % 8);
		assert!(!run(&[17, 4, 4], &bad), "flipped edge {k}");
	}
}

#[test]
fn paley_37_bounds_r55() {
	// Paley(37) has no K5 (and, being self-complementary, no independent 5-set).
	assert!(run(&[37, 5, 5], &paley(37)));
	assert!(!run(&[37, 4, 4], &paley(37)));
}

#[test]
fn refuses_malformed_witnesses() {
	let g = paley(17);
	assert!(!run(&[18, 4, 4], &g), "wrong n");
	assert!(!run(&[16, 4, 4], &g), "wrong n");
	assert!(!run(&[17, 4, 4], &g[..g.len() - 1]), "short");
	assert!(!run(&[17, 4, 4], &[&g[..], &[0]].concat()), "long");
	assert!(!run(&[17, 4], &g), "short params");
	assert!(!run(&[17, 4, 4, 0], &g), "long params");
	assert!(!run(&[17, 1, 4], &g), "s < 2");
	assert!(!run(&[65, 4, 4], &vec![0; witness_len(65)]), "n > 64");
	// 17 vertices have 136 edges, a whole number of bytes; 5 have 10, so 6 padding bits.
	let mut c5 = encode(5, |i, j| j - i == 1 || j - i == 4);
	assert!(run(&[5, 3, 3], &c5));
	c5[1] |= 0x80;
	assert!(!run(&[5, 3, 3], &c5), "a padding bit set");
}

#[test]
fn agrees_with_brute_force() {
	// A small xorshift, so the test is deterministic.
	let mut state = 0x2545_f491_4f6c_dd1du64;
	let mut next = move || {
		state ^= state << 13;
		state ^= state >> 7;
		state ^= state << 17;
		state
	};
	for round in 0..400 {
		let n = 4 + round % 11;
		let density = next() % 100;
		let bits: Vec<bool> = (0..n * n).map(|_| next() % 100 < density).collect();
		let x = encode(n, |i, j| bits[i * n + j]);
		let adj = decode(n, &x).unwrap();
		let edge = |i: usize, j: usize| adj[i] >> j & 1 == 1;
		let non_edge = |i: usize, j: usize| adj[i] >> j & 1 == 0;
		for s in 2..=5.min(n) {
			for t in 2..=5.min(n) {
				let expected = !naive_has(n, s, &edge) && !naive_has(n, t, &non_edge);
				assert_eq!(is_ramsey(&adj, n, s as u32, t as u32), expected, "n {n} s {s} t {t}");
			}
		}
	}
}

#[test]
fn full_size_graphs() {
	// 64 vertices, the most: the empty graph has no edge but every independent set.
	let empty = vec![0u8; witness_len(64)];
	assert!(!run(&[64, 2, 64], &empty));
	assert!(run(&[64, 2, 65], &empty) == false, "t > n");
	let complete = vec![0xffu8; witness_len(64)];
	assert!(run(&[64, 65 - 1, 2], &complete) == false, "K64 has a 64-clique");
	assert!(decode(64, &complete).is_some());
}

/// A graph6 line (fewer than 63 vertices) as a witness.
fn from_graph6(line: &str) -> (usize, Vec<u8>) {
	let bytes = line.trim().as_bytes();
	let n = bytes[0] as usize - 63;
	let bits: Vec<bool> = bytes[1..].iter().flat_map(|&b| (0..6).rev().map(move |k| (b - 63) >> k & 1 == 1)).collect();
	// graph6 lists the upper triangle column by column: (0,1), (0,2), (1,2), (0,3), ….
	let mut adj = vec![false; n * n];
	let mut k = 0;
	for j in 1..n {
		for i in 0..j {
			adj[i * n + j] = bits[k];
			k += 1;
		}
	}
	(n, encode(n, |i, j| adj[i * n + j]))
}

#[test]
fn a_known_r55_42_graph() {
	// One of McKay and Radziszowski's 656 (5,5,42)-graphs (r55_42some.g6, line 1).
	let (n, g) = from_graph6(include_str!("../testdata/r55_42.g6"));
	assert_eq!(n, 42);
	assert!(run(&[42, 5, 5], &g), "R(5, 5) > 42");
	assert!(!run(&[43, 5, 5], &g), "wrong n");
	assert!(!run(&[42, 4, 5], &g), "it has a K4");
	assert!(!run(&[42, 5, 4], &g), "and an independent 4-set");
	let breaking = (0..42 * 41 / 2)
		.filter(|&k| {
			let mut bad = g.clone();
			bad[k / 8] ^= 1 << (k % 8);
			!run(&[42, 5, 5], &bad)
		})
		.count();
	assert_eq!(breaking, BREAKING_FLIPS, "edges whose flip makes a K5 or an independent 5-set");
}
/// Of the 861 edges, flipping all but 6 makes a K5 or an independent 5-set; those 6 give other
/// (5,5,42)-graphs.
const BREAKING_FLIPS: usize = 855;
