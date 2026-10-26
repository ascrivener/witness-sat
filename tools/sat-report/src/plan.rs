//! Planning an LRAT refutation into chunks, each one attestation, in the layout
//! witness's `scripts/attest-batches.py` attests in parallel.
//!
//! Two passes over the proof, so it streams: the first cuts the steps into chunks by a budget,
//! and records, for each clause a later chunk cites, the first chunk to cite it; the second
//! writes each chunk, renumbered ([`sat_check::lrat`]), with those clauses as its subjects.
//! Steps after the first empty clause are ignored. Every chunk is checked natively as it's
//! written.
//!
//! A subject is a *bundle* of clauses (see [`sat_check`]): chunk `j`'s clauses first cited by
//! chunk `k` go in one bundle, `(j, k)`, so chunk `k` trusts exactly the clauses it needs from
//! `j`, and a later chunk citing any of them trusts the whole bundle. The empty clause is a bundle
//! of its own. A chunk is cut when its estimated gas, witness bytes, trusted bundles, trusted
//! bytes, the two together, or the attestations it cites would pass the budget: witness caps an
//! op's blobs at 4,096 and their bytes at 16 MiB, a work package carries about 13.8 MB, and
//! refine's output, which lists the attestations an op relies on (32 bytes each), 48 KiB.
//!
//! WORK gets:
//! - `batch-N.subjects`, `batch-N.trust`, `batch-N.witness`, `batch-N.gas`: batch N's attest
//!   arguments, as attest-batches.py reads them. Subjects are files under `subjects/`.
//! - batch 0, the *anchor*: the formula's first clause, proven in its tree. An UNSAT bounty cites
//!   it (`batch-0.claim:0`), and nothing else needs it.
//! - `params`: the bounty's params, hex. `empty`: the reference to the attested empty clause, for
//!   the reveal's `--trust`. `plan.tsv`: a line a batch.

use crate::{
	cnf::Cnf,
	lrat,
	proof::{Needed, Steps},
};
use sat_check::{ChunkSpec, check_chunk, enc, tree};
use std::{
	collections::{HashMap, HashSet},
	fmt::Write as _,
	fs, io,
	time::Instant,
};

/// The gas model, fitted (`tools/fit_gas.py`, nonnegative least squares) to witness-sim
/// measurements of the check (`scripts/gas.sh`, see `docs/design.md`): gas for each hint, each
/// literal a RUP check visits (hinted clauses' and the step's own, padding not counted), each
/// byte of witness, each hash proving the formula's clauses, and each byte of trusted bundles.
/// Over 703 chunks of pigeonhole, random 3-SAT and Erdős discrepancy proofs, measured gas was at
/// most 1.26 times it.
#[derive(Clone, Copy, Debug)]
pub struct GasModel {
	pub base: u64,
	pub per_hint: u64,
	pub per_visit: u64,
	pub per_byte: u64,
	pub per_hash: u64,
	pub per_trusted_byte: u64,
}

pub const GAS_MODEL: GasModel =
	GasModel { base: 100_000, per_hint: 99, per_visit: 82, per_byte: 155, per_hash: 6_900, per_trusted_byte: 236 };

#[derive(Clone, Copy, Debug)]
pub struct Budget {
	/// Estimated check gas a chunk may use.
	pub gas: u64,
	/// Bytes of witness a chunk may have.
	pub witness: u64,
	/// Bundles a chunk may trust (witness's MAX_BLOBS is 4,096, with the subjects).
	pub trusted: usize,
	/// Bytes of trusted bundles a chunk may have (witness's MAX_BLOBS_LEN is 16 MiB, with the
	/// subjects).
	pub trusted_bytes: u64,
	/// Attestations a chunk may cite: refine's 48 KiB of output holds about 1,500 ids.
	pub claims: usize,
	/// Bytes of witness and trusted bundles together: an op's work package carries both, with
	/// the check, the subjects and the citations, in about 13.8 MB.
	pub package: u64,
}

/// What a chunk costs so far, by the model.
#[derive(Clone, Copy, Default)]
struct Cost {
	hints: u64,
	visits: u64,
	bytes: u64,
	hashes: u64,
	trusted_bytes: u64,
}

impl Cost {
	fn gas(&self, m: &GasModel) -> u64 {
		m.base +
			m.per_hint * self.hints +
			m.per_visit * self.visits +
			m.per_byte * self.bytes +
			m.per_hash * self.hashes +
			m.per_trusted_byte * self.trusted_bytes
	}

	fn add(&mut self, o: &Cost) {
		self.hints += o.hints;
		self.visits += o.visits;
		self.bytes += o.bytes;
		self.hashes += o.hashes;
		self.trusted_bytes += o.trusted_bytes;
	}
}

/// A step's estimated encoding: about a byte a literal, and three a hint (they're distances
/// back, which in a chunk trusting a few hundred thousand clauses run to three LEB128 bytes:
/// the Erdős proof's averaged 3.4).
fn step_bytes(s: &lrat::Step) -> u64 {
	2 + s.lits.len() as u64 + 3 * s.hints.len() as u64
}

/// A clause's estimated encoding.
fn clause_bytes(len: u32) -> u64 {
	2 + len as u64
}

pub struct Summary {
	pub batches: usize,
	pub steps: u64,
	pub gas: Vec<u64>,
	pub empty: String,
}

fn bad(msg: impl Into<String>) -> io::Error {
	io::Error::new(io::ErrorKind::InvalidData, msg.into())
}

/// No chunk: the formula's clauses' chunk, and a clause no later chunk cites' first citer.
const NONE: u32 = u32::MAX;

/// A bundle: the chunk whose clauses it holds, and the chunk that first cites them.
type Key = (u32, u32);

/// Number a step's clause and hints densely when the proof is trimmed: its slot among needed
/// clauses, plus one. False for a step the refutation doesn't need.
fn renumber(s: &mut lrat::Step, needed: &Option<Needed>) -> io::Result<bool> {
	let Some(n) = needed else { return Ok(true) };
	if !n.has(s.id) {
		return Ok(false);
	}
	s.id = n.slot(s.id) as u64 + 1;
	for h in &mut s.hints {
		if !n.has(*h) {
			return Err(bad(format!("a needed step cites clause {h}, which trimming dropped")));
		}
		*h = n.slot(*h) as u64 + 1;
	}
	Ok(true)
}

/// Read the next step the refutation needs, renumbered.
fn next(steps: &mut Steps, s: &mut lrat::Step, needed: &Option<Needed>) -> io::Result<bool> {
	while steps.next(s)? {
		if renumber(s, needed)? {
			return Ok(true);
		}
	}
	Ok(false)
}

/// What pass 1 knows of each clause, by id − 1 (dense, once trimmed).
struct Clauses {
	/// The formula's clause count: ids up to it are the formula's.
	originals: usize,
	len: Vec<u32>,
	chunk: Vec<u32>,
	/// The first later chunk to cite it, or NONE.
	citer: Vec<u32>,
}

impl Clauses {
	/// The bundle a clause from an earlier chunk would be trusted in by chunk `now`.
	fn key(&self, h: usize, now: u32) -> Key {
		(self.chunk[h], if self.citer[h] == NONE { now } else { self.citer[h] })
	}
}

/// The chunk pass 1 is filling.
#[derive(Default)]
struct Filling {
	steps: u64,
	cost: Cost,
	originals: HashSet<usize>,
	bundles: HashSet<Key>,
	claims: HashSet<u32>,
}

impl Filling {
	/// What adding step `s` (id − 1 = `i`) to chunk `now` would add: its cost, and the bundles and
	/// attestations it would add.
	fn adding(&self, c: &Clauses, s: &lrat::Step, now: u32, bundle_bytes: &HashMap<Key, u64>, depth: u64) -> (Cost, usize, usize) {
		let mut add = Cost { hints: s.hints.len() as u64, visits: s.lits.len() as u64, bytes: step_bytes(s), ..Cost::default() };
		let (mut bundles, mut claims) = (HashSet::new(), HashSet::new());
		let mut originals = HashSet::new();
		for &h in &s.hints {
			let h = h as usize - 1;
			add.visits += c.len[h] as u64;
			if h < c.originals {
				if !self.originals.contains(&h) && originals.insert(h) {
					add.hashes += 2 + depth;
					add.bytes += clause_bytes(c.len[h]) + 32;
				}
			} else if c.chunk[h] != now {
				let key = c.key(h, now);
				if key.1 == now {
					// A bundle this chunk is first to cite grows by the clause, if it's new to it.
					if c.citer[h] == NONE {
						add.trusted_bytes += clause_bytes(c.len[h]);
					}
				} else if !self.bundles.contains(&key) && !bundles.contains(&key) {
					add.trusted_bytes += bundle_bytes[&key];
				}
				if !self.bundles.contains(&key) {
					bundles.insert(key);
				}
				if !self.claims.contains(&key.0) {
					claims.insert(key.0);
				}
			}
		}
		(add, bundles.len(), claims.len())
	}
}

pub fn plan(cnf: &Cnf, proof: &str, work: &str, budget: Budget, model: &GasModel) -> io::Result<Summary> {
	let needed = Some(crate::proof::needed(proof, cnf.clauses.len() as u64)?);
	let n = cnf.clauses.len();
	let depth = ((n.max(2)) as f64).log2().ceil() as u64;
	let mut c = Clauses {
		originals: n,
		len: cnf.clauses.iter().map(|c| c.len() as u32).collect(),
		chunk: vec![NONE; n],
		citer: vec![NONE; n],
	};
	let mut bundle_bytes: HashMap<Key, u64> = HashMap::new();

	// Pass 1: cut chunks.
	let started = Instant::now();
	let mut r = Steps::open(proof)?;
	let mut s = lrat::Step::default();
	let mut now = 0u32;
	let mut f = Filling::default();
	let mut steps = 0u64;
	let mut found_empty = false;
	while next(&mut r, &mut s, &needed)? {
		let i = s.id as usize - 1;
		// Ids increase, past the formula's (with gaps: CaDiCaL numbers clauses it never writes).
		if i < c.len.len() {
			return Err(bad(format!("clause {} added out of order, or over an original", s.id)));
		}
		c.len.resize(i + 1, 0);
		c.chunk.resize(i + 1, NONE);
		c.citer.resize(i + 1, NONE);
		for &h in &s.hints {
			let h = h as usize;
			if h == 0 || h > i || h > n && c.chunk[h - 1] == NONE {
				return Err(bad(format!("clause {}: hint {h} isn't an earlier clause", s.id)));
			}
		}
		let (add, bundles, claims) = f.adding(&c, &s, now, &bundle_bytes, depth);
		let mut over = f.cost;
		over.add(&add);
		if f.steps > 0 &&
			(over.gas(model) > budget.gas ||
				over.bytes > budget.witness ||
				over.trusted_bytes > budget.trusted_bytes ||
				over.bytes + over.trusted_bytes > budget.package ||
				f.bundles.len() + bundles > budget.trusted ||
				f.claims.len() + claims > budget.claims)
		{
			now += 1;
			f = Filling::default();
		}
		// Add it to the chunk.
		let (add, _, _) = f.adding(&c, &s, now, &bundle_bytes, depth);
		f.cost.add(&add);
		for &h in &s.hints {
			let h = h as usize - 1;
			if h < n {
				f.originals.insert(h);
			} else if c.chunk[h] != now {
				if c.citer[h] == NONE {
					c.citer[h] = now;
					*bundle_bytes.entry((c.chunk[h], now)).or_default() += clause_bytes(c.len[h]);
				}
				let key = c.key(h, now);
				f.bundles.insert(key);
				f.claims.insert(key.0);
			}
		}
		c.len[i] = s.lits.len() as u32;
		c.chunk[i] = now;
		f.steps += 1;
		steps += 1;
		if s.lits.is_empty() {
			found_empty = true;
			break;
		}
	}
	if !found_empty {
		return Err(bad("the proof never derives the empty clause"));
	}
	eprintln!("pass 1: {steps} steps in {} chunks ({:.1} s)", now + 1, started.elapsed().as_secs_f64());
	drop(bundle_bytes);

	// Pass 2: write them.
	fs::create_dir_all(format!("{work}/subjects"))?;
	let levels = cnf.levels();
	let unsat = cnf.unsat(&levels);
	fs::write(format!("{work}/params"), hex(&unsat.encode()))?;
	let mut w = Writer {
		cnf,
		levels: &levels,
		f: &unsat,
		c: &c,
		bundles: HashMap::new(),
		codes: HashMap::new(),
		work,
		model,
		gas: Vec::new(),
		table: String::from(
			"batch\tsteps\toriginals\tbundles\tclaims\ttrusted\ttrusted_bytes\tsubjects\tsubject_clauses\twitness_bytes\thints\tvisits\thashes\tgas_estimate\tnative_ms\n",
		),
		empty: String::new(),
	};
	w.anchor()?;
	let mut r = Steps::open(proof)?;
	let mut buffer: Vec<lrat::Step> = Vec::new();
	while next(&mut r, &mut s, &needed)? {
		if buffer.first().is_some_and(|b| c.chunk[b.id as usize - 1] != c.chunk[s.id as usize - 1]) {
			w.write(&buffer)?;
			buffer.clear();
		}
		buffer.push(s.clone());
		if s.lits.is_empty() {
			break;
		}
	}
	w.write(&buffer)?;
	fs::write(format!("{work}/empty"), &w.empty)?;
	fs::write(format!("{work}/plan.tsv"), &w.table)?;
	Ok(Summary { batches: now as usize + 2, steps, gas: w.gas, empty: w.empty })
}

/// The blobs an op may give its check: witness's `MAX_BLOBS`.
const MAX_BLOBS: usize = 4096;

/// A written bundle: its batch and entry, and its clauses' ids.
struct Bundle {
	batch: usize,
	entry: usize,
	clauses: Vec<u64>,
}

/// Writes chunks as batches: chunk `j` is batch `j + 1`, after the anchor.
struct Writer<'a> {
	cnf: &'a Cnf,
	levels: &'a [Vec<tree::Hash>],
	f: &'a sat_check::Unsat,
	c: &'a Clauses,
	bundles: HashMap<Key, Bundle>,
	/// The codes of every clause in a written bundle.
	codes: HashMap<u64, Vec<u32>>,
	work: &'a str,
	model: &'a GasModel,
	gas: Vec<u64>,
	table: String,
	empty: String,
}

impl Writer<'_> {
	/// Batch 0: the anchor, the formula's first clause proven in its tree.
	fn anchor(&mut self) -> io::Result<()> {
		let first = &self.cnf.clauses[0];
		let witness = ChunkSpec { originals: &[(0, first.clone())], proof: &tree::prove(self.levels, &[0]), steps: &[], exports: &[vec![0]] }
			.encode(0);
		let subject = sat_check::bundle([enc::clause_bytes(first).as_slice()].into_iter());
		assert!(check_chunk(self.f, [].into_iter(), &witness, &[&subject]));
		write_batch(self.work, 0, &[subject], &[], &witness, self.model.base)?;
		self.gas.push(self.model.base);
		writeln!(self.table, "0\t0\t1\t0\t0\t0\t0\t1\t1\t{}\t0\t0\t0\t{}\t0", witness.len(), self.model.base).unwrap();
		Ok(())
	}

	fn bundle_bytes(&self, b: &Bundle) -> Vec<u8> {
		let clauses: Vec<Vec<u8>> = b.clauses.iter().map(|id| enc::clause_bytes(&self.codes[id])).collect();
		sat_check::bundle(clauses.iter().map(|c| c.as_slice()))
	}

	/// Write one chunk's batch.
	fn write(&mut self, steps: &[lrat::Step]) -> io::Result<()> {
		let started = Instant::now();
		let (c, cnf) = (self.c, self.cnf);
		let j = c.chunk[steps[0].id as usize - 1];
		let batch = j as usize + 1;
		let is_original = |id: u64| id as usize <= c.originals;
		// Number trusted bundles' clauses in order of the bundles' first use, then originals by
		// index, then steps.
		let mut trusted: Vec<Key> = Vec::new();
		let mut number: HashMap<u64, u32> = HashMap::new();
		let mut next_number = 0u32;
		let mut originals: Vec<u64> = Vec::new();
		for s in steps {
			for &h in &s.hints {
				if is_original(h) {
					originals.push(h);
				} else if c.chunk[h as usize - 1] != j && !number.contains_key(&h) {
					let key = (c.chunk[h as usize - 1], c.citer[h as usize - 1]);
					let b = self.bundles.get(&key).ok_or_else(|| bad(format!("batch {batch}: clause {h}'s bundle isn't written")))?;
					trusted.push(key);
					for &id in &b.clauses {
						number.insert(id, next_number);
						next_number += 1;
					}
				}
			}
		}
		originals.sort_unstable();
		originals.dedup();
		let t = next_number;
		for (k, &o) in originals.iter().enumerate() {
			number.insert(o, t + k as u32);
		}
		let first_step = t + originals.len() as u32;
		let mut cost = Cost::default();
		let mut spec_steps: Vec<(Vec<u32>, Vec<u32>)> = Vec::with_capacity(steps.len());
		for (k, s) in steps.iter().enumerate() {
			let codes = crate::cnf::canonical(s.lits.iter().map(|&l| enc::code(l)).collect());
			let hints: Vec<u32> = s.hints.iter().map(|h| number[h]).collect();
			cost.hints += hints.len() as u64;
			cost.visits += codes.len() as u64;
			for &h in &s.hints {
				cost.visits += c.len[h as usize - 1] as u64;
			}
			number.insert(s.id, first_step + k as u32);
			spec_steps.push((codes, hints));
		}
		// Subjects: the clauses each later chunk first cites, a bundle a chunk, then the empty
		// clause on its own.
		let mut by_citer: Vec<(u32, u64, usize)> = Vec::new();
		let mut empty_step = None;
		for (k, s) in steps.iter().enumerate() {
			let citer = c.citer[s.id as usize - 1];
			if citer != NONE {
				by_citer.push((citer, s.id, k));
			}
			if s.lits.is_empty() {
				empty_step = Some(k);
			}
		}
		by_citer.sort_unstable();
		let mut exports: Vec<Vec<u32>> = Vec::new();
		for group in by_citer.chunk_by(|a, b| a.0 == b.0) {
			let entry = exports.len();
			exports.push(group.iter().map(|&(_, _, k)| first_step + k as u32).collect());
			for &(_, id, k) in group {
				self.codes.insert(id, spec_steps[k].0.clone());
			}
			self.bundles.insert((j, group[0].0), Bundle { batch, entry, clauses: group.iter().map(|g| g.1).collect() });
		}
		if let Some(k) = empty_step {
			self.empty = format!("batch-{batch}.claim:{}", exports.len());
			exports.push(vec![first_step + k as u32]);
		}
		let subjects: Vec<Vec<u8>> = exports
			.iter()
			.map(|e| {
				let clauses: Vec<Vec<u8>> = e.iter().map(|&n| enc::clause_bytes(&spec_steps[(n - first_step) as usize].0)).collect();
				sat_check::bundle(clauses.iter().map(|c| c.as_slice()))
			})
			.collect();
		let original_specs: Vec<(u32, Vec<u32>)> =
			originals.iter().map(|&o| (o as u32 - 1, cnf.clauses[o as usize - 1].clone())).collect();
		let indices: Vec<u32> = originals.iter().map(|&o| o as u32 - 1).collect();
		let proof = tree::prove(self.levels, &indices);
		let witness = ChunkSpec { originals: &original_specs, proof: &proof, steps: &spec_steps, exports: &exports }.encode(t);
		let trusted_bytes: Vec<Vec<u8>> = trusted.iter().map(|k| self.bundle_bytes(&self.bundles[k])).collect();
		let subject_refs: Vec<&[u8]> = subjects.iter().map(|s| s.as_slice()).collect();
		if !check_chunk(self.f, trusted_bytes.iter().map(|b| b.as_slice()), &witness, &subject_refs) {
			return Err(bad(format!("batch {batch} fails the check natively")));
		}
		if subjects.len() + trusted.len() > MAX_BLOBS {
			return Err(bad(format!("batch {batch}: {} bundles trusted and {} subjects, over witness's 4,096 blobs", trusted.len(), subjects.len())));
		}
		if subjects.is_empty() {
			return Err(bad(format!("batch {batch} exports nothing")));
		}
		cost.bytes = witness.len() as u64;
		cost.hashes = 2 * originals.len() as u64 + proof.len() as u64;
		cost.trusted_bytes = trusted_bytes.iter().map(|b| b.len() as u64).sum();
		let refs: Vec<String> = trusted
			.iter()
			.map(|k| {
				let b = &self.bundles[k];
				format!("batch-{}.claim:{}", b.batch, b.entry)
			})
			.collect();
		let claims: HashSet<usize> = trusted.iter().map(|k| self.bundles[k].batch).collect();
		let estimate = cost.gas(self.model);
		write_batch(self.work, batch, &subjects, &refs, &witness, estimate)?;
		self.gas.push(estimate);
		writeln!(
			self.table,
			"{batch}\t{}\t{}\t{}\t{}\t{t}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{estimate}\t{:.2}",
			steps.len(),
			originals.len(),
			trusted.len(),
			claims.len(),
			cost.trusted_bytes,
			subjects.len(),
			exports.iter().map(Vec::len).sum::<usize>(),
			witness.len(),
			cost.hints,
			cost.visits,
			cost.hashes,
			started.elapsed().as_secs_f64() * 1e3
		)
		.unwrap();
		Ok(())
	}
}

fn write_batch(work: &str, batch: usize, subjects: &[Vec<u8>], trust: &[String], witness: &[u8], gas: u64) -> io::Result<()> {
	let mut names = Vec::with_capacity(subjects.len());
	for (e, s) in subjects.iter().enumerate() {
		let name = format!("subjects/{batch}-{e}");
		fs::write(format!("{work}/{name}"), s)?;
		names.push(name);
	}
	fs::write(format!("{work}/batch-{batch}.subjects"), names.join(","))?;
	fs::write(format!("{work}/batch-{batch}.trust"), trust.join(","))?;
	fs::write(format!("{work}/batch-{batch}.witness"), witness)?;
	fs::write(format!("{work}/batch-{batch}.gas"), gas.to_string())?;
	Ok(())
}

pub fn hex(bytes: &[u8]) -> String {
	let mut s = String::with_capacity(2 + 2 * bytes.len());
	s.push_str("0x");
	for b in bytes {
		write!(s, "{b:02x}").unwrap();
	}
	s
}
