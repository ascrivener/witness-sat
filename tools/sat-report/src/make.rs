//! Formulas and graphs for demos and tests.

use crate::cnf::{Cnf, canonical};
use sat_check::enc::code;

/// The pigeonhole formula: `n + 1` pigeons in `n` holes, each pigeon in a hole, no hole shared.
/// Unsatisfiable, and hard for resolution: its proofs grow exponentially in `n`.
pub fn pigeonhole(n: u32) -> Cnf {
	let var = |pigeon: u32, hole: u32| (pigeon * n + hole + 1) as i32;
	let mut clauses = Vec::new();
	for p in 0..=n {
		clauses.push(canonical((0..n).map(|h| code(var(p, h))).collect()));
	}
	for h in 0..n {
		for p in 0..=n {
			for q in p + 1..=n {
				clauses.push(canonical(vec![code(-var(p, h)), code(-var(q, h))]));
			}
		}
	}
	Cnf { vars: (n + 1) * n, clauses }
}

/// A random 3-SAT formula with a planted solution: clauses are drawn at random and kept only if
/// the solution satisfies them. Returns the formula and the solution (variable `v` true when
/// `solution[v - 1]`).
pub fn planted(vars: u32, clauses: usize, seed: u64) -> (Cnf, Vec<bool>) {
	let mut state = seed | 1;
	let mut next = move || {
		state ^= state << 13;
		state ^= state >> 7;
		state ^= state << 17;
		state
	};
	let solution: Vec<bool> = (0..vars).map(|_| next() & 1 == 1).collect();
	let mut out = Vec::with_capacity(clauses);
	while out.len() < clauses {
		let lits: Vec<i32> = (0..3)
			.map(|_| {
				let v = (next() % vars as u64) as i32 + 1;
				if next() & 1 == 1 { v } else { -v }
			})
			.collect();
		if lits.iter().any(|&l| solution[l.unsigned_abs() as usize - 1] == (l > 0)) {
			out.push(canonical(lits.iter().map(|&l| code(l)).collect()));
		}
	}
	(Cnf { vars, clauses: out }, solution)
}

/// An assignment as the SAT check's witness: a bit a variable, least significant first.
pub fn assignment_bits(values: &[bool]) -> Vec<u8> {
	let mut out = vec![0u8; values.len().div_ceil(8)];
	for (v, &x) in values.iter().enumerate() {
		if x {
			out[v / 8] |= 1 << (v % 8);
		}
	}
	out
}

/// A solver's `v` lines (`v 1 -2 3 … 0`) as values of variables 1..=vars.
pub fn parse_solution(text: &str, vars: u32) -> Option<Vec<bool>> {
	let mut values = vec![false; vars as usize];
	let mut seen = 0;
	for line in text.lines().filter_map(|l| l.strip_prefix("v ")) {
		for w in line.split_whitespace() {
			let l: i32 = w.parse().ok()?;
			if l != 0 {
				*values.get_mut(l.unsigned_abs() as usize - 1)? = l > 0;
				seen += 1;
			}
		}
	}
	(seen > 0).then_some(values)
}

/// Decode a graph6 line (a graph on fewer than 63 vertices) into its vertex count and edges.
pub fn graph6(line: &str) -> Option<(usize, Vec<(usize, usize)>)> {
	let bytes = line.trim().as_bytes();
	let n = (*bytes.first()? as usize).checked_sub(63)?;
	if n > 62 {
		return None;
	}
	let bits = bytes[1..].iter().flat_map(|&b| (0..6).rev().map(move |k| (b.wrapping_sub(63) >> k) & 1 == 1));
	// graph6 lists the upper triangle column by column: (0,1), (0,2), (1,2), (0,3), ….
	let pairs = (1..n).flat_map(|j| (0..j).map(move |i| (i, j)));
	let edges: Vec<(usize, usize)> = pairs.zip(bits).filter(|&(_, b)| b).map(|(p, _)| p).collect();
	(bytes.len() == 1 + (n * (n - 1) / 2).div_ceil(6)).then_some((n, edges))
}

/// The Ramsey check's witness for a graph: its upper triangle, row by row.
pub fn ramsey_witness(n: usize, edges: &[(usize, usize)]) -> Vec<u8> {
	let mut adj = vec![false; n * n];
	for &(i, j) in edges {
		adj[i * n + j] = true;
		adj[j * n + i] = true;
	}
	let mut out = vec![0u8; (n * (n - 1) / 2).div_ceil(8)];
	let mut k = 0;
	for i in 0..n {
		for j in i + 1..n {
			if adj[i * n + j] {
				out[k / 8] |= 1 << (k % 8);
			}
			k += 1;
		}
	}
	out
}
