//! The host tool end to end on the pigeonhole fixture (7 pigeons, 6 holes; CaDiCaL's LRAT).

use crate::{cnf::Cnf, lrat, make, plan, proof};
use sat_check::check_chunk;
use std::{fs, path::PathBuf};

const CNF: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/php6.cnf");
const LRAT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/php6.lrat");

/// A fresh directory for one test.
fn scratch(name: &str) -> String {
	let dir: PathBuf = std::env::temp_dir().join(format!("sat-report-test-{}-{name}", std::process::id()));
	let _ = fs::remove_dir_all(&dir);
	fs::create_dir_all(&dir).unwrap();
	dir.to_str().unwrap().to_string()
}

fn all_steps(path: &str) -> Vec<lrat::Step> {
	let mut r = proof::Steps::open(path).unwrap();
	let mut s = lrat::Step::default();
	let mut out = Vec::new();
	while r.next(&mut s).unwrap() {
		out.push(s.clone());
	}
	out
}

/// A batch's trusted clauses, subjects and witness, from the plan's files.
fn batch(work: &str, n: usize) -> (Vec<Vec<u8>>, Vec<Vec<u8>>, Vec<u8>, Vec<usize>) {
	let read = |kind: &str| fs::read_to_string(format!("{work}/batch-{n}.{kind}")).unwrap();
	let refs: Vec<(usize, usize)> = read("trust")
		.split(',')
		.filter(|r| !r.is_empty())
		.map(|r| {
			let (claim, entry) = r.split_once(':').unwrap();
			(claim.trim_start_matches("batch-").trim_end_matches(".claim").parse().unwrap(), entry.parse().unwrap())
		})
		.collect();
	let trusted = refs.iter().map(|(b, e)| fs::read(format!("{work}/subjects/{b}-{e}")).unwrap()).collect();
	let subjects = read("subjects").split(',').map(|s| fs::read(format!("{work}/{s}")).unwrap()).collect();
	(trusted, subjects, fs::read(format!("{work}/batch-{n}.witness")).unwrap(), refs.iter().map(|r| r.0).collect())
}

fn plan(proof: &str, work: &str, gas: u64) -> plan::Summary {
	let cnf = Cnf::read(CNF).unwrap();
	plan::plan(&cnf, proof, work, plan::Budget { gas, witness: 8 << 20, trusted: 3000 }, &plan::GAS_MODEL).unwrap()
}

#[test]
fn plans_check_and_cite_only_earlier_batches() {
	let cnf = Cnf::read(CNF).unwrap();
	let f = cnf.unsat(&cnf.levels());
	for gas in [3_000_000, 10_000_000, 3_000_000_000] {
		let work = scratch(&format!("plan-{gas}"));
		let s = plan(LRAT, &work, gas);
		assert!(s.batches >= 2);
		for n in 0..s.batches {
			let (trusted, subjects, witness, from) = batch(&work, n);
			assert!(from.iter().all(|&m| m < n), "batch {n} cites a later batch");
			assert!(!subjects.is_empty());
			let subjects: Vec<&[u8]> = subjects.iter().map(|s| s.as_slice()).collect();
			let checks = |w: &[u8]| check_chunk(&f, trusted.iter().map(|t| t.as_slice()), w, &subjects);
			assert!(checks(&witness), "batch {n}");
			// Any change to the witness fails it (or panics, which on PolkaVM is a trap: false).
			for at in [witness.len() / 3, witness.len() - 2] {
				let mut bad = witness.clone();
				bad[at] ^= 0x01;
				let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| checks(&bad))).unwrap_or(false);
				assert!(!ok, "batch {n}, byte {at} flipped");
			}
		}
		assert_eq!(fs::read(format!("{work}/subjects/{}", s.empty.replace(".claim:", "-").trim_start_matches("batch-"))).unwrap(), sat_check::EMPTY);
	}
}

#[test]
fn split_and_trimmed_proofs_plan_the_same() {
	let dir = scratch("split");
	let (steps, segments) = proof::split(LRAT, &dir, 4096).unwrap();
	assert!(segments > 2);
	// The segments are binary LRAT, read back as the same steps up to the empty clause.
	let text = all_steps(LRAT);
	let binary = all_steps(&dir);
	assert_eq!(binary.len() as u64, steps);
	for (a, b) in text.iter().zip(&binary) {
		assert_eq!((a.id, &a.lits, &a.hints), (b.id, &b.lits, &b.hints));
	}
	let (total, kept) = proof::trim(&dir, Cnf::read(CNF).unwrap().clauses.len() as u64).unwrap();
	assert_eq!(total, steps);
	assert!(kept < total, "the empty clause doesn't need every step");
	let (a, b) = (scratch("whole"), scratch("segments"));
	let (x, y) = (plan(LRAT, &a, 10_000_000), plan(&dir, &b, 10_000_000));
	assert_eq!((x.batches, x.steps, &x.gas), (y.batches, y.steps, &y.gas));
	assert_eq!(x.steps, kept);
}

#[test]
fn graph6() {
	let line = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/../../ramsey/testdata/r55_42.g6")).unwrap();
	let (n, edges) = make::graph6(&line).unwrap();
	assert_eq!(n, 42);
	// A (5,5,42)-graph is close to regular, with about half the 861 edges.
	assert!((380..480).contains(&edges.len()), "{} edges", edges.len());
	assert_eq!(make::ramsey_witness(n, &edges).len(), 108);
	assert!(make::graph6(&line[..line.len() - 2]).is_none(), "truncated");
}

#[test]
fn planted_formulas_are_satisfied() {
	let (f, solution) = make::planted(50, 200, 3);
	let formula = sat_check::Formula::encode(f.vars, &f.clauses);
	assert!(sat_check::satisfies(&formula, &make::assignment_bits(&solution)));
}
