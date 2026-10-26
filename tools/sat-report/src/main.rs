//! Host tool for witness-sat. See `usage()`.

mod cnf;
mod lrat;
mod make;
mod plan;
mod proof;
#[cfg(test)]
mod tests;

use cnf::Cnf;
use plan::{Budget, GAS_MODEL, hex};
use std::{fs, io, process::exit, time::Instant};
use witness_types::{CheckBlob, CheckMode, blake2b256, check_args};

fn usage() -> ! {
	eprintln!(
		"usage: sat-report <command> ...

  php N OUT.cnf                      the pigeonhole formula, N + 1 pigeons in N holes
  planted VARS CLAUSES SEED OUT.cnf OUT.assignment
                                     random 3-SAT with a planted solution (the SAT check's witness)
  formula IN.cnf OUT                 a SAT bounty's blob: the formula, encoded
  assignment IN.cnf SOLVER_OUT OUT   a solver's `v` lines as the SAT check's witness
  unsat-params IN.cnf                an UNSAT bounty's params (hex), and the formula's size
  split PROOF DIR [--segment BYTES]  a proof (LRAT, plain or .zst) as compressed segments (see proof.rs)
  trim IN.cnf DIR                    mark the steps a split proof's empty clause needs (DIR/needed.bits)
  plan IN.cnf PROOF WORK [--gas G] [--witness BYTES] [--trusted N]
                                     cut an LRAT refutation into attestable chunks (see plan.rs)
  args WORK BATCH OUT                batch BATCH's attest arguments, for `witness-sim check`
  reveal-args WORK OUT               a reveal trusting WORK's empty clause, for `witness-sim check`
  sat-args FORMULA WITNESS OUT       a SAT reveal's arguments
  ramsey FILE.g6 LINE OUT            line LINE (from 0) of a graph6 file as the Ramsey check's witness
  ramsey-args N S T WITNESS OUT      a Ramsey reveal's arguments"
	);
	exit(2)
}

fn main() {
	let args: Vec<String> = std::env::args().skip(1).collect();
	if let Err(e) = run(&args) {
		eprintln!("error: {e}");
		exit(1);
	}
}

fn num<T: std::str::FromStr>(s: Option<&String>) -> T {
	s.and_then(|s| s.replace('_', "").parse().ok()).unwrap_or_else(|| usage())
}

fn flag<T: std::str::FromStr>(args: &[String], name: &str, default: T) -> T {
	args.iter().position(|a| a == name).map(|i| num(args.get(i + 1))).unwrap_or(default)
}

fn blob(trusted: bool, data: &[u8]) -> CheckBlob<'_> {
	CheckBlob { trusted, hash: blake2b256(data), data }
}

/// The subject a `batch-M.claim:E` reference names, from WORK.
fn subject(work: &str, reference: &str) -> io::Result<Vec<u8>> {
	let (claim, entry) = reference.trim().split_once(':').unwrap_or_else(|| usage());
	let batch = claim.trim_start_matches("batch-").trim_end_matches(".claim");
	fs::read(format!("{work}/subjects/{batch}-{entry}"))
}

fn unhex(s: &str) -> Vec<u8> {
	let s = s.trim().trim_start_matches("0x");
	(0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap_or_else(|_| usage())).collect()
}

fn run(args: &[String]) -> io::Result<()> {
	let a = |i: usize| args.get(i).map(String::as_str).unwrap_or_else(|| usage());
	match a(0) {
		"php" => make::pigeonhole(num(args.get(1))).write(a(2))?,
		"planted" => {
			let (f, solution) = make::planted(num(args.get(1)), num(args.get(2)), num(args.get(3)));
			f.write(a(4))?;
			fs::write(a(5), make::assignment_bits(&solution))?;
		},
		"formula" => {
			let f = Cnf::read(a(1))?;
			fs::write(a(2), sat_check::Formula::encode(f.vars, &f.clauses))?;
		},
		"assignment" => {
			let f = Cnf::read(a(1))?;
			let values = make::parse_solution(&fs::read_to_string(a(2))?, f.vars)
				.ok_or_else(|| io::Error::other("no `v` lines"))?;
			let bits = make::assignment_bits(&values);
			let formula = sat_check::Formula::encode(f.vars, &f.clauses);
			if !sat_check::satisfies(&formula, &bits) {
				return Err(io::Error::other("the assignment doesn't satisfy the formula"));
			}
			fs::write(a(3), bits)?;
		},
		"unsat-params" => {
			let f = Cnf::read(a(1))?;
			let p = f.unsat(&f.levels());
			eprintln!("{} variables, {} clauses", p.vars, p.clauses);
			println!("{}", hex(&p.encode()));
		},
		"split" => {
			let started = Instant::now();
			let (steps, segments) = proof::split(a(1), a(2), flag(args, "--segment", 256 << 20))?;
			println!("{steps} steps in {segments} segments ({:.1} s)", started.elapsed().as_secs_f64());
		},
		"trim" => {
			let f = Cnf::read(a(1))?;
			let started = Instant::now();
			let (steps, kept) = proof::trim(a(2), f.clauses.len() as u64)?;
			println!("{kept} of {steps} steps needed ({:.1} s)", started.elapsed().as_secs_f64());
		},
		"plan" => {
			let f = Cnf::read(a(1))?;
			let budget = Budget {
				gas: flag(args, "--gas", 3_000_000_000),
				witness: flag(args, "--witness", 8 << 20),
				trusted: flag(args, "--trusted", 3_000),
			};
			fs::create_dir_all(a(3))?;
			let started = Instant::now();
			let s = plan::plan(&f, a(2), a(3), budget, &GAS_MODEL)?;
			let total: u64 = s.gas.iter().sum();
			let max = s.gas.iter().max().copied().unwrap_or(0);
			println!(
				"{} steps in {} batches (with the anchor); estimated gas {total:.3e} in all, {max:.3e} at most; the empty clause is {} ({:.1} s)",
				s.steps,
				s.batches,
				s.empty,
				started.elapsed().as_secs_f64()
			);
		},
		"args" => {
			let work = a(1);
			let batch: usize = num(args.get(2));
			let params = unhex(&fs::read_to_string(format!("{work}/params"))?);
			let witness = fs::read(format!("{work}/batch-{batch}.witness"))?;
			let refs = fs::read_to_string(format!("{work}/batch-{batch}.trust"))?;
			let trusted: Vec<Vec<u8>> =
				refs.split(',').filter(|r| !r.is_empty()).map(|r| subject(work, r)).collect::<io::Result<_>>()?;
			let names = fs::read_to_string(format!("{work}/batch-{batch}.subjects"))?;
			let subjects: Vec<Vec<u8>> =
				names.split(',').map(|n| fs::read(format!("{work}/{n}"))).collect::<io::Result<_>>()?;
			let blobs: Vec<CheckBlob> =
				trusted.iter().map(|d| blob(true, d)).chain(subjects.iter().map(|d| blob(false, d))).collect();
			fs::write(a(3), check_args(CheckMode::Attest, &blobs, &params, &witness))?;
		},
		"reveal-args" => {
			let work = a(1);
			let params = unhex(&fs::read_to_string(format!("{work}/params"))?);
			let anchor = subject(work, "batch-0.claim:0")?;
			let empty = subject(work, &fs::read_to_string(format!("{work}/empty"))?)?;
			let blobs = [blob(true, &anchor), blob(true, &empty)];
			fs::write(a(2), check_args(CheckMode::Reveal, &blobs, &params, b"hunter"))?;
		},
		"sat-args" => {
			let formula = fs::read(a(1))?;
			let witness = fs::read(a(2))?;
			fs::write(a(3), check_args(CheckMode::Reveal, &[blob(false, &formula)], &[sat_check::SAT], &witness))?;
		},
		"ramsey" => {
			let text = fs::read_to_string(a(1))?;
			let line: usize = num(args.get(2));
			let (n, edges) =
				text.lines().nth(line).and_then(make::graph6).ok_or_else(|| io::Error::other("no such graph6 line"))?;
			fs::write(a(3), make::ramsey_witness(n, &edges))?;
			println!("{n}");
		},
		"ramsey-args" => {
			let params = [num::<u8>(args.get(1)), num(args.get(2)), num(args.get(3))];
			fs::write(a(5), check_args(CheckMode::Reveal, &[], &params, &fs::read(a(4))?))?;
		},
		_ => usage(),
	}
	Ok(())
}
