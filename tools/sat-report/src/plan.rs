//! Planning an LRAT refutation into chunks, each one attestation, in the layout
//! witness's `scripts/attest-batches.py` attests in parallel.
//!
//! Two passes over the proof, so it streams: the first cuts the steps into chunks by a budget
//! of gas and bytes, and marks the clauses a later chunk cites; the second writes each chunk,
//! renumbered ([`sat_check::lrat`]), with those clauses as its subjects. Steps after the first
//! empty clause are ignored. Every chunk is checked natively as it's written.
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

/// The gas model, fitted (`tools/fit_gas.py`) to witness-sim measurements of the check
/// (`scripts/gas.sh`, see `docs/design.md`): gas for each hint, each literal a RUP check visits
/// (hinted clauses' and the step's own, padding not counted), each byte of witness, each hash
/// proving the formula's clauses, and each byte of trusted clauses. Measured gas was within
/// −10% and +22% of it over 544 batches of pigeonhole and random 3-SAT proofs.
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
	GasModel { base: 100_000, per_hint: 390, per_visit: 112, per_byte: 47, per_hash: 7_600, per_trusted_byte: 21 };

#[derive(Clone, Copy, Debug)]
pub struct Budget {
	/// Estimated check gas a chunk may use.
	pub gas: u64,
	/// Bytes of witness a chunk may have.
	pub witness: u64,
	/// Trusted clauses a chunk may cite (witness's MAX_BLOBS is 4,096, with the subjects).
	pub trusted: usize,
}

/// What a chunk costs so far, by the model.
#[derive(Default)]
struct Cost {
	hints: u64,
	visits: u64,
	bytes: u64,
	hashes: u64,
	trusted_bytes: u64,
}

impl Cost {
	fn gas(&self, m: &GasModel) -> u64 {
		m.base + m.per_hint * self.hints + m.per_visit * self.visits + m.per_byte * self.bytes + m.per_hash * self.hashes + m.per_trusted_byte * self.trusted_bytes
	}
}

/// A step's estimated encoding: about a byte a literal and two a hint.
fn step_bytes(s: &lrat::Step) -> u64 {
	2 + s.lits.len() as u64 + 2 * s.hints.len() as u64
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

const ORIGINAL: u32 = u32::MAX;

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

pub fn plan(cnf: &Cnf, proof: &str, work: &str, budget: Budget, model: &GasModel) -> io::Result<Summary> {
	let needed = Some(crate::proof::needed(proof, cnf.clauses.len() as u64)?);
	let originals = cnf.clauses.len() as u64;
	let depth = (originals.max(2) as f64).log2().ceil() as u64;
	// Each id's clause length, chunk (ORIGINAL for the formula's), and whether a later chunk cites it.
	let mut len: Vec<u32> = cnf.clauses.iter().map(|c| c.len() as u32).collect();
	let mut chunk_of: Vec<u32> = vec![ORIGINAL; cnf.clauses.len()];
	let mut cited: Vec<bool> = vec![false; cnf.clauses.len()];
	let index = |id: u64| -> io::Result<usize> {
		id.checked_sub(1).map(|i| i as usize).ok_or_else(|| bad("clause id 0"))
	};

	// Pass 1: cut chunks.
	let started = Instant::now();
	let mut r = Steps::open(proof)?;
	let mut s = lrat::Step::default();
	let (mut chunk, mut steps_in) = (0u32, 0u64);
	let mut cost = Cost::default();
	let mut trusted: HashSet<u64> = HashSet::new();
	let mut used: HashSet<u64> = HashSet::new();
	let mut steps = 0u64;
	let mut found_empty = false;
	while next(&mut r, &mut s, &needed)? {
		let i = index(s.id)?;
		// Ids increase, past the formula's.
		if i < len.len() {
			return Err(bad(format!("clause {} added out of order, or over an original", s.id)));
		}
		// With gaps: CaDiCaL numbers clauses it never writes too.
		len.resize(i + 1, 0);
		chunk_of.resize(i + 1, ORIGINAL);
		cited.resize(i + 1, false);
		let mut add = Cost { hints: s.hints.len() as u64, visits: s.lits.len() as u64, bytes: step_bytes(&s), ..Cost::default() };
		let mut new_trusted = 0;
		for &h in &s.hints {
			let h = index(h)?;
			if h >= i || chunk_of[h] == ORIGINAL && h >= cnf.clauses.len() {
				return Err(bad(format!("clause {}: hint {} isn't an earlier clause", s.id, h + 1)));
			}
			add.visits += len[h] as u64;
			if chunk_of[h] == ORIGINAL {
				if !used.contains(&(h as u64)) {
					add.hashes += 2 + depth;
					add.bytes += len[h] as u64 + 2 + 32;
				}
			} else if chunk_of[h] != chunk && !trusted.contains(&(h as u64)) {
				new_trusted += 1;
				add.trusted_bytes += len[h] as u64 * 2 + 2;
			}
		}
		let over = Cost {
			hints: cost.hints + add.hints,
			visits: cost.visits + add.visits,
			bytes: cost.bytes + add.bytes,
			hashes: cost.hashes + add.hashes,
			trusted_bytes: cost.trusted_bytes + add.trusted_bytes,
		};
		if steps_in > 0 &&
			(over.gas(model) > budget.gas || over.bytes > budget.witness || trusted.len() + new_trusted > budget.trusted)
		{
			chunk += 1;
			(steps_in, cost) = (0, Cost::default());
			trusted.clear();
			used.clear();
			// Count the step again against the new chunk: everything it cites is outside it now.
			cost.hints = s.hints.len() as u64;
			cost.visits = s.lits.len() as u64;
			cost.bytes = step_bytes(&s);
		} else {
			cost = Cost {
				hints: cost.hints + s.hints.len() as u64,
				visits: cost.visits + s.lits.len() as u64,
				bytes: cost.bytes + step_bytes(&s),
				..cost
			};
		}
		for &h in &s.hints {
			let h = index(h)?;
			cost.visits += len[h] as u64;
			if chunk_of[h] == ORIGINAL {
				if used.insert(h as u64) {
					cost.hashes += 2 + depth;
					cost.bytes += len[h] as u64 + 2 + 32;
				}
			} else if chunk_of[h] != chunk {
				cited[h] = true;
				if trusted.insert(h as u64) {
					cost.trusted_bytes += len[h] as u64 * 2 + 2;
				}
			}
		}
		len[i] = s.lits.len() as u32;
		chunk_of[i] = chunk;
		steps += 1;
		steps_in += 1;
		if s.lits.is_empty() {
			found_empty = true;
			break;
		}
	}
	if !found_empty {
		return Err(bad("the proof never derives the empty clause"));
	}
	eprintln!("pass 1: {steps} steps in {} chunks ({:.1} s)", chunk + 1, started.elapsed().as_secs_f64());

	// Pass 2: write them.
	fs::create_dir_all(format!("{work}/subjects"))?;
	let levels = cnf.levels();
	let f = cnf.unsat(&levels);
	fs::write(format!("{work}/params"), hex(&f.encode()))?;
	let mut table = String::from(
		"batch\tsteps\toriginals\ttrusted\tsubjects\twitness_bytes\thints\tvisits\thashes\ttrusted_bytes\tgas_estimate\tnative_ms\n",
	);
	let mut gas = Vec::new();

	// The anchor: batch 0.
	let anchor = ChunkSpec {
		originals: &[(0, cnf.clauses[0].clone())],
		proof: &tree::prove(&levels, &[0]),
		steps: &[],
		exports: &[0],
	}
	.encode(0);
	let anchor_subject = enc::clause_bytes(&cnf.clauses[0]);
	assert!(check_chunk(&f, [].into_iter(), &anchor, &[&anchor_subject]));
	write_batch(work, 0, &[anchor_subject], &[], &anchor, model.base)?;
	gas.push(model.base);
	writeln!(table, "0\t0\t1\t0\t1\t{}\t0\t0\t0\t0\t{}\t0", anchor.len(), model.base).unwrap();

	let mut w = Writer {
		cnf,
		levels: &levels,
		f: &f,
		cited: &cited,
		exported: HashMap::new(),
		work,
		depth,
		model,
		gas,
		table,
		empty: String::new(),
		batch: 1,
	};
	let mut r = Steps::open(proof)?;
	let mut buffer: Vec<lrat::Step> = Vec::new();
	while next(&mut r, &mut s, &needed)? {
		if buffer.first().is_some_and(|b| chunk_of[b.id as usize - 1] != chunk_of[s.id as usize - 1]) {
			w.emit(&buffer, &HashSet::new())?;
			buffer.clear();
		}
		buffer.push(s.clone());
		if s.lits.is_empty() {
			break;
		}
	}
	w.emit(&buffer, &HashSet::new())?;
	fs::write(format!("{work}/empty"), &w.empty)?;
	fs::write(format!("{work}/plan.tsv"), &w.table)?;
	Ok(Summary { batches: w.batch, steps, gas: w.gas, empty: w.empty })
}

/// The blobs an op may give its check: witness's `MAX_BLOBS`.
const MAX_BLOBS: usize = 4096;

/// Writes chunks as batches, numbered as written.
struct Writer<'a> {
	cnf: &'a Cnf,
	levels: &'a [Vec<tree::Hash>],
	f: &'a sat_check::Unsat,
	/// Whether a later chunk cites each clause.
	cited: &'a [bool],
	/// Exported clauses: their batch and entry, and codes.
	exported: HashMap<u64, (usize, usize, Vec<u32>)>,
	work: &'a str,
	depth: u64,
	model: &'a GasModel,
	gas: Vec<u64>,
	table: String,
	empty: String,
	/// The next batch's number.
	batch: usize,
}

impl Writer<'_> {
	fn is_original(&self, id: u64) -> bool {
		id <= self.cnf.clauses.len() as u64
	}

	/// Write `steps` as a batch, or two or more if it would give its check too many blobs. `later`
	/// holds the clauses the rest of the chunk cites, which must be exported too.
	fn emit(&mut self, steps: &[lrat::Step], later: &HashSet<u64>) -> io::Result<()> {
		let mine: HashSet<u64> = steps.iter().map(|s| s.id).collect();
		let trusted: HashSet<u64> =
			steps.iter().flat_map(|s| &s.hints).filter(|&&h| !self.is_original(h) && !mine.contains(&h)).copied().collect();
		let exports = steps.iter().filter(|s| self.exports(s, later)).count();
		if trusted.len() + exports > MAX_BLOBS && steps.len() > 1 {
			let (left, right) = steps.split_at(steps.len() / 2);
			let mut left_later = later.clone();
			left_later.extend(right.iter().flat_map(|s| &s.hints).copied());
			self.emit(left, &left_later)?;
			return self.emit(right, later);
		}
		let started = Instant::now();
		let written = self.write(steps, later)?;
		let ms = started.elapsed().as_secs_f64() * 1e3;
		let estimate = written.cost.gas(self.model);
		self.gas.push(estimate);
		if let Some(e) = written.empty {
			self.empty = e;
		}
		let c = &written.cost;
		writeln!(
			self.table,
			"{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{estimate}\t{ms:.2}",
			self.batch - 1,
			steps.len(),
			written.originals,
			written.trusted,
			written.subjects,
			written.bytes,
			c.hints,
			c.visits,
			c.hashes,
			c.trusted_bytes
		)
		.unwrap();
		Ok(())
	}

	/// Whether a step's clause must be a subject: a later chunk, or the rest of this one, cites
	/// it, or it's the empty clause.
	fn exports(&self, s: &lrat::Step, later: &HashSet<u64>) -> bool {
		self.cited[s.id as usize - 1] || later.contains(&s.id) || s.lits.is_empty()
	}

	/// Write the next batch, for `steps`.
	fn write(&mut self, steps: &[lrat::Step], later: &HashSet<u64>) -> io::Result<Written> {
		let batch = self.batch;
		self.batch += 1;
		let cnf = self.cnf;
		let mine: HashSet<u64> = steps.iter().map(|s| s.id).collect();
		// Number trusted clauses in order of first use, then originals by index, then steps.
		let mut trusted: Vec<u64> = Vec::new();
		let mut number: HashMap<u64, u32> = HashMap::new();
		let mut originals: Vec<u64> = Vec::new();
		for s in steps {
			for &h in &s.hints {
				if self.is_original(h) {
					originals.push(h);
				} else if !mine.contains(&h) && !number.contains_key(&h) {
					number.insert(h, trusted.len() as u32);
					trusted.push(h);
				}
			}
		}
		originals.sort_unstable();
		originals.dedup();
		let t = trusted.len() as u32;
		for (k, &o) in originals.iter().enumerate() {
			number.insert(o, t + k as u32);
		}
		let first_step = t + originals.len() as u32;
		let mut spec_steps = Vec::with_capacity(steps.len());
		let mut cost = Cost::default();
		for (k, s) in steps.iter().enumerate() {
			let codes = crate::cnf::canonical(s.lits.iter().map(|&l| enc::code(l)).collect());
			let hints: Vec<u32> = s.hints.iter().map(|h| number[h]).collect();
			cost.hints += hints.len() as u64;
			cost.visits += codes.len() as u64;
			number.insert(s.id, first_step + k as u32);
			spec_steps.push((codes, hints));
		}
		// Clause lengths for the visit count: trusted from their codes, originals and steps known.
		let clause_len = |n: u32| -> u64 {
			if n < t {
				self.exported[&trusted[n as usize]].2.len() as u64
			} else if n < first_step {
				cnf.clauses[originals[(n - t) as usize] as usize - 1].len() as u64
			} else {
				spec_steps[(n - first_step) as usize].0.len() as u64
			}
		};
		for (_, hints) in &spec_steps {
			cost.visits += hints.iter().map(|&h| clause_len(h)).sum::<u64>();
		}
		let mut exports = Vec::new();
		let mut subjects = Vec::new();
		let mut empty = None;
		for (k, s) in steps.iter().enumerate() {
			if self.exports(s, later) {
				let entry = subjects.len();
				exports.push(first_step + k as u32);
				subjects.push(enc::clause_bytes(&spec_steps[k].0));
				if s.lits.is_empty() {
					empty = Some(format!("batch-{batch}.claim:{entry}"));
				}
				self.exported.insert(s.id, (batch, entry, spec_steps[k].0.clone()));
			}
		}
		let original_specs: Vec<(u32, Vec<u32>)> =
			originals.iter().map(|&o| (o as u32 - 1, cnf.clauses[o as usize - 1].clone())).collect();
		let indices: Vec<u32> = originals.iter().map(|&o| o as u32 - 1).collect();
		let proof = tree::prove(self.levels, &indices);
		let witness = ChunkSpec { originals: &original_specs, proof: &proof, steps: &spec_steps, exports: &exports }.encode(t);
		let trusted_bytes: Vec<Vec<u8>> = trusted.iter().map(|h| enc::clause_bytes(&self.exported[h].2)).collect();
		let subject_refs: Vec<&[u8]> = subjects.iter().map(|s| s.as_slice()).collect();
		if !check_chunk(self.f, trusted_bytes.iter().map(|b| b.as_slice()), &witness, &subject_refs) {
			return Err(bad(format!("batch {batch} fails the check natively")));
		}
		if subjects.len() + trusted.len() > MAX_BLOBS {
			return Err(bad(format!("batch {batch}: one step cites {} clauses, over witness's 4,096 blobs", trusted.len())));
		}
		cost.bytes = witness.len() as u64;
		cost.hashes = 2 * originals.len() as u64 + proof.len() as u64;
		cost.trusted_bytes = trusted_bytes.iter().map(|b| b.len() as u64 + 32 * self.depth).sum();
		let refs: Vec<String> = trusted
			.iter()
			.map(|h| {
				let (b, e, _) = &self.exported[h];
				format!("batch-{b}.claim:{e}")
			})
			.collect();
		write_batch(self.work, batch, &subjects, &refs, &witness, cost.gas(self.model))?;
		Ok(Written { originals: originals.len(), trusted: trusted.len(), subjects: subjects.len(), bytes: witness.len(), cost, empty })
	}
}

/// What writing a chunk's batch made.
struct Written {
	originals: usize,
	trusted: usize,
	subjects: usize,
	bytes: usize,
	cost: Cost,
	/// The reference to the empty clause, if the chunk derives it.
	empty: Option<String>,
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
