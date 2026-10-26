//! Proofs too big for memory or disk: split into compressed segments, trimmed backwards.
//!
//! A proof is one LRAT file (plain, or `.zst`) or a directory of segments, `seg-NNNNN.lrat.zst`,
//! each binary LRAT holding whole steps, in order (`sat-report split` writes them). Compressed
//! files are read through `zstd -dc`.
//!
//! **Trimming** keeps only the steps the empty clause depends on: going backwards from it, a
//! step is needed if a needed step cites it. Segments are read newest first, one at a time, so
//! memory holds one segment's steps and a bit per clause id. The result, `needed.bits` in the
//! directory, is a bitset over ids (the formula's clauses always set), which also numbers the
//! needed clauses densely ([`Needed::slot`]), so planning's per-clause arrays stay small.

use crate::lrat::{Reader, Step};
use std::{
	fs::{self, File},
	io::{self, BufWriter, Read, Write},
	path::{Path, PathBuf},
	process::{Command, Stdio},
};

/// The files of a proof, in order.
pub fn files(path: &str) -> io::Result<Vec<PathBuf>> {
	let p = Path::new(path);
	if !p.is_dir() {
		return Ok(vec![p.to_path_buf()]);
	}
	let mut segs: Vec<PathBuf> = fs::read_dir(p)?
		.filter_map(|e| e.ok().map(|e| e.path()))
		.filter(|f| f.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("seg-")))
		.collect();
	segs.sort();
	Ok(segs)
}

/// A reader of one proof file, decompressing `.zst`.
pub fn open(file: &Path) -> io::Result<Box<dyn Read>> {
	if file.extension().is_some_and(|e| e == "zst") {
		let child = Command::new("zstd").args(["-dcq"]).arg(file).stdout(Stdio::piped()).spawn()?;
		Ok(Box::new(child.stdout.expect("piped")))
	} else {
		Ok(Box::new(File::open(file)?))
	}
}

/// Reads every step of a proof, file by file.
pub struct Steps {
	files: Vec<PathBuf>,
	next: usize,
	reader: Option<Reader>,
}

impl Steps {
	pub fn open(path: &str) -> io::Result<Self> {
		Ok(Steps { files: files(path)?, next: 0, reader: None })
	}

	pub fn next(&mut self, step: &mut Step) -> io::Result<bool> {
		loop {
			if let Some(r) = &mut self.reader {
				if r.next(step)? {
					return Ok(true);
				}
			}
			let Some(f) = self.files.get(self.next) else { return Ok(false) };
			self.reader = Some(Reader::new(open(f)?)?);
			self.next += 1;
		}
	}
}

fn put(out: &mut Vec<u8>, x: i64) {
	let mut v = (x.unsigned_abs() << 1) | (x < 0) as u64;
	loop {
		let b = (v & 0x7f) as u8;
		v >>= 7;
		if v == 0 {
			out.push(b);
			return;
		}
		out.push(b | 0x80);
	}
}

/// Append a step as binary LRAT.
pub fn encode(out: &mut Vec<u8>, s: &Step) {
	out.push(b'a');
	put(out, s.id as i64);
	for &l in &s.lits {
		put(out, l as i64);
	}
	put(out, 0);
	for &h in &s.hints {
		put(out, h as i64);
	}
	put(out, 0);
}

/// Write a compressed segment.
fn write_segment(dir: &str, n: usize, bytes: &[u8]) -> io::Result<()> {
	let path = format!("{dir}/seg-{n:05}.lrat.zst");
	let mut child = Command::new("zstd").args(["-q", "-3", "-T2", "-f", "-o", &path]).stdin(Stdio::piped()).spawn()?;
	child.stdin.take().expect("piped").write_all(bytes)?;
	let status = child.wait()?;
	if !status.success() {
		return Err(io::Error::other(format!("zstd failed writing {path}")));
	}
	Ok(())
}

/// Split a proof into segments of about `bytes` of binary LRAT each, deletions dropped, ending
/// at its first empty clause. Returns the steps and segments written.
pub fn split(proof: &str, dir: &str, bytes: usize) -> io::Result<(u64, usize)> {
	fs::create_dir_all(dir)?;
	let mut steps = Steps::open(proof)?;
	let mut s = Step::default();
	let (mut count, mut segment) = (0u64, 0usize);
	let mut buf = Vec::with_capacity(bytes + (1 << 20));
	while steps.next(&mut s)? {
		encode(&mut buf, &s);
		count += 1;
		let end = s.lits.is_empty();
		if buf.len() >= bytes || end {
			write_segment(dir, segment, &buf)?;
			buf.clear();
			segment += 1;
		}
		if end {
			return Ok((count, segment));
		}
	}
	Err(io::Error::other("the proof never derives the empty clause"))
}

/// The clauses a refutation needs, as a bitset over clause ids (bit `id − 1`), with ranks.
pub struct Needed {
	words: Vec<u64>,
	/// Set bits before each word.
	before: Vec<u32>,
}

impl Needed {
	fn with(words: Vec<u64>) -> Self {
		let mut before = Vec::with_capacity(words.len());
		let mut n = 0u32;
		for w in &words {
			before.push(n);
			n += w.count_ones();
		}
		Needed { words, before }
	}

	pub fn read(dir: &str) -> io::Result<Option<Self>> {
		let path = format!("{dir}/needed.bits");
		if !Path::new(&path).exists() {
			return Ok(None);
		}
		let bytes = fs::read(path)?;
		Ok(Some(Needed::with(bytes.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect())))
	}

	pub fn has(&self, id: u64) -> bool {
		let i = id - 1;
		self.words.get((i / 64) as usize).is_some_and(|w| w >> (i % 64) & 1 == 1)
	}

	/// The dense number of a needed clause: its rank among needed ids.
	pub fn slot(&self, id: u64) -> usize {
		let i = id - 1;
		let (w, b) = ((i / 64) as usize, i % 64);
		self.before[w] as usize + (self.words[w] & ((1u64 << b) - 1)).count_ones() as usize
	}
}

/// Trim a split proof: write `needed.bits` to its directory. `originals` is the formula's clause
/// count. Returns (steps, needed steps).
pub fn trim(dir: &str, originals: u64) -> io::Result<(u64, u64)> {
	let (words, total, kept) = mark(&files(dir)?, originals)?;
	let mut out = BufWriter::new(File::create(format!("{dir}/needed.bits"))?);
	for w in &words {
		out.write_all(&w.to_le_bytes())?;
	}
	out.flush()?;
	Ok((total, kept))
}

/// The steps a proof needs: of a split proof, as `trim` wrote them; of a single file, trimmed in
/// memory.
pub fn needed(path: &str, originals: u64) -> io::Result<Needed> {
	if Path::new(path).is_dir() {
		return Needed::read(path)?.ok_or_else(|| io::Error::other(format!("{path}: no needed.bits: run `sat-report trim`")));
	}
	Ok(Needed::with(mark(&files(path)?, originals)?.0))
}

/// Mark the needed steps of a proof's files, newest first: the bitset, and the steps and needed
/// steps there were.
fn mark(segs: &[PathBuf], originals: u64) -> io::Result<(Vec<u64>, u64, u64)> {
	let mut words: Vec<u64> = Vec::new();
	let set = |words: &mut Vec<u64>, id: u64| {
		let i = id - 1;
		let w = (i / 64) as usize;
		if words.len() <= w {
			words.resize(w + 1, 0);
		}
		words[w] |= 1 << (i % 64);
	};
	let is_set = |words: &Vec<u64>, id: u64| {
		let i = id - 1;
		words.get((i / 64) as usize).is_some_and(|w| w >> (i % 64) & 1 == 1)
	};
	let (mut total, mut kept) = (0u64, 0u64);
	let mut first = true;
	for seg in segs.iter().rev() {
		// The whole segment: ids and hints.
		let mut r = Reader::new(open(seg)?)?;
		let mut s = Step::default();
		let mut steps: Vec<(u64, Vec<u64>)> = Vec::new();
		let mut empty = None;
		while r.next(&mut s)? {
			let is_empty = s.lits.is_empty();
			steps.push((s.id, std::mem::take(&mut s.hints)));
			if is_empty {
				// Only the first empty clause counts: planning stops there.
				empty = Some(s.id);
				break;
			}
		}
		if first {
			set(&mut words, empty.ok_or_else(|| io::Error::other("the last segment doesn't end in the empty clause"))?);
			first = false;
		}
		total += steps.len() as u64;
		for (id, hints) in steps.iter().rev() {
			if is_set(&words, *id) {
				kept += 1;
				for &h in hints {
					set(&mut words, h);
				}
			}
		}
	}
	for id in 1..=originals {
		set(&mut words, id);
	}
	Ok((words, total, kept))
}
