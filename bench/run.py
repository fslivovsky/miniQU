#!/usr/bin/env python3
"""Benchmark runner for QCIR solvers (miniQU and its rewrite).

Runs every instance once, each job pinned to its own core, and records
wall time, CPU time and peak RSS.  Timeout and memory limit are enforced by
killing the process group.  The verdict comes from the exit code (10 = SAT,
20 = UNSAT) and is cross-checked against the printed "SATISFIABLE" /
"UNSATISFIABLE" line.  Results go to results/TAG/results.csv and
results/TAG/meta.json.  The run is resumable: instances already present in
the CSV are skipped.

--seed S is recorded in meta.json and substituted for {seed} in --args;
--seed-args (default "--seed={seed}") is appended only when S > 0, so seed 0
is the deterministic default.  Every run is made with -verb=1 and the
statistics it prints (the "c stat" lines of the new solver; conflicts,
decisions, propagations and restarts of the baseline) go to stats.csv.

With --proof-check, a second phase (after all timed runs, on separate cores
so timings stay clean) re-runs the instances solved within
--proof-max-solve-sec with -proof=FILE, checks the proof with the Lean
checker qlrup-check, and deletes the proof file.  When the checker runs out of
time or memory the proof is trimmed with qlrup-trim and checked again; a proof
above --proof-max-gb is abandoned ("too_large").  A "{proof}" in --args is
replaced by a proof file for timed proof-on runs (proof overhead).

See bench/README.md for details and examples.
"""
import argparse
import csv
import datetime
import glob
import hashlib
import json
import os
import platform
import queue
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_BENCH_DIR = "/home/ec2-user/benchmarks/qcir"
DEFAULT_CHECKER = "/home/ec2-user/qu-check/.lake/build/bin/qlrup-check"
DEFAULT_PROOF_DIR = "/home/ec2-user/miniqu-work/proofs"
DEFAULT_LOG_DIR = "/home/ec2-user/miniqu-work/logs"
DEFAULT_TRIM = "/home/ec2-user/miniqu-work/build/release/qlrup-trim"
COLUMNS = ["instance", "family", "result", "exit", "wall", "cpu", "rss_mb",
           "proof_status", "proof_check_sec", "proof_bytes", "proof_trim_bytes"]
MAX_LONG_PROOF_JOBS = 6  # with a checker limit of an hour or more: 6 x 8 GB of proofs at most
# Proof statuses that are bugs; every other status except ok is a gap in coverage.
REJECTED_STATUSES = ("rejected", "wrong_verdict", "check_error")
STAT_COLUMNS = ["instance", "counter", "value"]
BASELINE_STATS = ("restarts", "conflicts", "decisions", "propagations")
# Fields of meta.json that must agree for a run to be resumed.
RESUME_KEYS = ("args", "seed_args", "seed", "timeout", "mem_gb", "jobs", "cores", "instances_sha256")


def family_of(instance):
    """Family = leading alphabetic prefix of the file name ("chess", "ci",
    "klieber", ...); names starting with a digit form the family "numeric"."""
    m = re.match(r"[A-Za-z]+", os.path.basename(instance))
    return m.group(0) if m else "numeric"


def parse_cores(spec):
    cores = []
    for part in spec.split(","):
        if "-" in part:
            lo, hi = part.split("-")
            cores.extend(range(int(lo), int(hi) + 1))
        else:
            cores.append(int(part))
    return cores


def resolve_instances(specs, bench_dir):
    """Each spec is a glob (relative to bench_dir), an instance path, or a text
    file with one instance name per line (lines starting with '#' are comments).  Returns sorted unique
    absolute paths."""
    found = {}
    for spec in specs:
        base = spec if os.path.isabs(spec) else os.path.join(bench_dir, spec)
        if spec.endswith(".txt") and os.path.isfile(spec):
            with open(spec) as f:
                names = [l.strip() for l in f if not l.lstrip().startswith("#")]
            for n in filter(None, names):
                p = n if os.path.isabs(n) else os.path.join(bench_dir, n)
                if not os.path.isfile(p):
                    sys.exit("run.py: instance %s listed in %s not found" % (n, spec))
                found[p] = 1
        else:
            hits = glob.glob(base)
            if not hits:
                sys.exit("run.py: no instance matches %r" % spec)
            for p in hits:
                found[p] = 1
    return sorted(found)


def run_pinned(cmd, core, timeout, mem_mb, out_path, fsize_limit=None):
    """Run cmd pinned to core with stdout+stderr in out_path.  Returns a dict
    with keys status (ok|timeout|memout), exit (code, or -signal), wall, cpu,
    rss_mb."""
    # No core dumps: dumping a solver that holds gigabytes takes minutes and fills the disk.
    prefix = ["prlimit", "--core=0"] + (["--fsize=%d" % fsize_limit] if fsize_limit else []) + \
        ["taskset", "-c", str(core)]
    with open(out_path, "wb") as out:
        t0 = time.monotonic()
        p = subprocess.Popen(prefix + cmd, stdin=subprocess.DEVNULL, stdout=out,
                             stderr=subprocess.STDOUT, start_new_session=True)
        status = "ok"
        wstatus = ru = None
        while True:
            pid, wstatus, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            elapsed = time.monotonic() - t0
            if elapsed > timeout:
                status = "timeout"
            elif mem_mb and _rss_mb(p.pid) > mem_mb:
                status = "memout"
            if status != "ok":
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                _, wstatus, ru = os.wait4(p.pid, 0)
                break
            time.sleep(0.01 if elapsed < 1 else 0.05)
        wall = time.monotonic() - t0
    p.returncode = 0  # reaped by hand; keep Popen quiet
    try:  # stragglers in the process group
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    code = os.WEXITSTATUS(wstatus) if os.WIFEXITED(wstatus) else -os.WTERMSIG(wstatus)
    return {"status": status, "exit": code, "wall": wall,
            "cpu": ru.ru_utime + ru.ru_stime, "rss_mb": ru.ru_maxrss / 1024.0}


def _rss_mb(pid):
    try:
        with open("/proc/%d/statm" % pid) as f:
            return int(f.read().split()[1]) * os.sysconf("SC_PAGE_SIZE") / 2**20
    except (OSError, ValueError, IndexError):
        return 0


def printed_verdict(path):
    """SAT/UNSAT as printed by the solver (last 64 KiB of output), or None."""
    try:
        with open(path, "rb") as f:
            f.seek(0, os.SEEK_END)
            f.seek(max(0, f.tell() - 65536))
            text = f.read().decode("latin-1")
    except OSError:
        return None
    verdict = None
    for line in text.splitlines():
        m = re.match(r"^(?:s\s+)?(SATISFIABLE|UNSATISFIABLE)\s*$", line.strip())
        if m:
            verdict = "SAT" if m.group(1) == "SATISFIABLE" else "UNSAT"
    return verdict


def parse_stats(path):
    """Counters printed at -verb=1: "c stat NAME VALUE" lines of the new solver,
    else the baseline's "name : value" lines.  Empty when the run was killed."""
    try:
        with open(path, errors="replace") as f:
            text = f.read()
    except OSError:
        return {}
    stats = {m.group(1): int(m.group(2))
             for m in re.finditer(r"^c stat (\S+) (\d+)$", text, re.M)}
    if not stats:
        stats = {m.group(1): int(m.group(2))
                 for m in re.finditer(r"^(%s)\s*:\s*(\d+)" % "|".join(BASELINE_STATS), text, re.M)}
    return stats


def classify(r, printed):
    if r["status"] == "timeout":
        return "TIMEOUT"
    if r["status"] == "memout":
        return "MEMOUT"
    if r["exit"] == -signal.SIGXFSZ:
        return "TOOLARGE"  # the proof file reached --proof-max-gb
    by_exit = {10: "SAT", 20: "UNSAT"}.get(r["exit"])
    if by_exit is None:
        return "ERROR"
    if printed is not None and printed != by_exit:
        return "MISMATCH"  # exit code and printed line disagree
    return by_exit


class Runner:
    def __init__(self, args):
        self.args = args
        self.proof_in_args = "{proof}" in args.args
        seed_args = args.seed_args if args.seed > 0 else ""
        self.solver_args = shlex.split(args.args.replace("{seed}", str(args.seed)) + " " +
                                       seed_args.replace("{seed}", str(args.seed)))
        self.proof_args = shlex.split(args.proof_args)
        self.fsize_limit = int(args.proof_max_gb * 2**30)
        # qlrup-trim must be told the proof format; the solver flag decides it.
        self.trim_format = "--binary" if re.search(r"-proof-?binary(?!=0)", args.args + " " + args.proof_args) \
            else "--text"
        self.logdir = os.path.join(args.log_dir, args.tag)
        os.makedirs(self.logdir, exist_ok=True)
        self.outdir = os.path.join(args.results_dir, args.tag)
        os.makedirs(self.outdir, exist_ok=True)
        self.csv_path = os.path.join(self.outdir, "results.csv")
        self.stats_path = os.path.join(self.outdir, "stats.csv")
        self.rows = {}
        self.lock = threading.Lock()
        self.done = 0

    # ---- CSV --------------------------------------------------------------
    def load(self):
        if os.path.exists(self.csv_path):
            with open(self.csv_path, newline="") as f:
                for row in csv.DictReader(f):
                    self.rows[row["instance"]] = {c: row.get(c) or "" for c in COLUMNS}

    def append_row(self, row):
        new = not os.path.exists(self.csv_path) or os.path.getsize(self.csv_path) == 0
        with open(self.csv_path, "a", newline="") as f:
            w = csv.DictWriter(f, COLUMNS)
            if new:
                w.writeheader()
            w.writerow(row)

    def append_stats(self, name, stats):
        if not stats:
            return
        with self.lock:  # jobs finish concurrently; the header must be written once
            new = not os.path.exists(self.stats_path) or os.path.getsize(self.stats_path) == 0
            with open(self.stats_path, "a", newline="") as f:
                w = csv.writer(f)
                if new:
                    w.writerow(STAT_COLUMNS)
                w.writerows([name, k, v] for k, v in sorted(stats.items()))

    def rewrite(self):
        tmp = self.csv_path + ".tmp"
        with open(tmp, "w", newline="") as f:
            w = csv.DictWriter(f, COLUMNS)
            w.writeheader()
            for k in sorted(self.rows):
                w.writerow(self.rows[k])
        os.replace(tmp, self.csv_path)

    # ---- phase 1: timed runs -----------------------------------------------
    def solve_one(self, path, core):
        a = self.args
        name = os.path.basename(path)
        out = os.path.join(self.logdir, name + ".out")
        proof = os.path.join(a.proof_dir, "%s-%s.proof" % (a.tag, name))
        solver_args = [x.replace("{proof}", proof) for x in self.solver_args]
        if self.proof_in_args:
            os.makedirs(a.proof_dir, exist_ok=True)
        r = run_pinned([a.solver, "-verb=1"] + solver_args + [path], core, a.timeout,
                       a.mem_gb * 1024, out,
                       fsize_limit=self.fsize_limit if self.proof_in_args else None)
        result = classify(r, printed_verdict(out))
        self.append_stats(name, parse_stats(out))
        if result in ("SAT", "UNSAT"):
            os.remove(out)  # keep logs only for failures
        row = {c: "" for c in COLUMNS}
        row.update(instance=name, family=family_of(name), result=result, exit=r["exit"],
                   wall="%.3f" % r["wall"], cpu="%.3f" % r["cpu"], rss_mb="%.1f" % r["rss_mb"])
        if self.proof_in_args:
            row["proof_bytes"] = os.path.getsize(proof) if os.path.exists(proof) else 0
            if result in ("SAT", "UNSAT") and a.trim_size:
                row["proof_trim_bytes"] = self.trimmed_size(proof, core)
            if os.path.exists(proof):
                os.remove(proof)
        return row

    def trimmed_size(self, proof, core):
        """Size of the proof after qlrup-trim, or "" if trimming failed."""
        trimmed = proof + ".trim"
        try:
            code = subprocess.call(["taskset", "-c", str(core), self.args.trim, self.trim_format, "--quiet",
                                    proof, trimmed], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return os.path.getsize(trimmed) if code == 0 else ""
        finally:
            if os.path.exists(trimmed):
                os.remove(trimmed)

    def phase1(self, instances):
        a = self.args
        todo = [p for p in instances if os.path.basename(p) not in self.rows]
        print("run.py: %d instances, %d already done, %d to run (jobs=%d)" %
              (len(instances), len(instances) - len(todo), len(todo),
               min(a.jobs, len(a.cores))), flush=True)
        cores = queue.Queue()
        for c in a.cores[:a.jobs]:
            cores.put(c)

        def work(path):
            core = cores.get()
            try:
                row = self.solve_one(path, core)
            finally:
                cores.put(core)
            with self.lock:
                self.rows[row["instance"]] = row
                self.append_row(row)
                self.done += 1
                print("[%d/%d] %-50s %-8s %8.2fs" % (self.done, len(todo), row["instance"][:50],
                                                    row["result"], float(row["wall"])), flush=True)

        with ThreadPoolExecutor(max_workers=min(a.jobs, len(a.cores))) as ex:
            list(ex.map(work, todo))

    # ---- phase 2: proof logging and checking -------------------------------
    def check_proof(self, path, proof, core, out):
        """Run the Lean checker.  Returns (status, seconds); status is one of
        ok, rejected, wrong_verdict, check_timeout, check_memout, check_error."""
        a = self.args
        expect = "VERIFIED TRUE" if self.rows[os.path.basename(path)]["result"] == "SAT" else "VERIFIED FALSE"
        t0 = time.monotonic()
        chk = run_pinned([a.checker, path, proof], core, a.proof_timeout, a.proof_mem_gb * 1024, out)
        seconds = time.monotonic() - t0
        if chk["status"] == "timeout":
            return "check_timeout", seconds
        if chk["status"] == "memout":
            return "check_memout", seconds
        m = re.search(r"^s (VERIFIED TRUE|VERIFIED FALSE|NOT VERIFIED.*)$",
                      open(out, errors="replace").read(), re.M)
        if m is None:
            return "check_error", seconds
        if m.group(1) == expect:
            return "ok", seconds
        return ("rejected" if m.group(1).startswith("NOT VERIFIED") else "wrong_verdict"), seconds

    def proof_one(self, path, core):
        a = self.args
        name = os.path.basename(path)
        row = self.rows[name]
        proof = os.path.join(a.proof_dir, "%s-%s.proof" % (a.tag, name))
        trimmed = proof + ".trim"
        out = os.path.join(self.logdir, name + ".proof.out")
        os.makedirs(a.proof_dir, exist_ok=True)
        try:
            r = run_pinned([a.solver, "-verb=1"] + self.solver_args + self.proof_args +
                           ["-proof=" + proof, path], core, a.proof_solve_timeout,
                           a.mem_gb * 1024, out, fsize_limit=self.fsize_limit)
            res = classify(r, printed_verdict(out))
            row["proof_bytes"] = os.path.getsize(proof) if os.path.exists(proof) else 0
            if res == "TOOLARGE":
                row["proof_status"] = "too_large"
                return
            if res != row["result"]:
                row["proof_status"] = "solve_" + res.lower()
                return
            os.remove(out)
            status, seconds = self.check_proof(path, proof, core, out)
            if status in ("check_timeout", "check_memout"):
                # A trimmed proof is much smaller and often checks within the limits.
                code = subprocess.call(["taskset", "-c", str(core), a.trim, self.trim_format, "--quiet",
                                        proof, trimmed], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if code == 0:
                    row["proof_trim_bytes"] = os.path.getsize(trimmed)
                    status2, seconds2 = self.check_proof(path, trimmed, core, out)
                    seconds += seconds2
                    status = status2
            row["proof_status"] = status
            row["proof_check_sec"] = "%.3f" % seconds
            if status == "ok":
                os.remove(out)
        finally:
            for f in (proof, trimmed):
                if os.path.exists(f):
                    os.remove(f)

    def phase2(self, instances):
        a = self.args
        paths = {os.path.basename(p): p for p in instances}
        todo = []
        for name, row in self.rows.items():
            if name not in paths or row["proof_status"] != "":
                continue
            if row["result"] in ("SAT", "UNSAT") and float(row["wall"]) <= a.proof_max_solve_sec:
                todo.append(paths[name])
            else:
                row["proof_status"] = "n/a"
        todo.sort(key=lambda p: os.path.getsize(p))
        if a.proof_timeout >= 3600:  # long checks hold gigabytes of memory and proof files: cap the disk
            a.proof_jobs = min(a.proof_jobs, MAX_LONG_PROOF_JOBS)
        print("run.py: proof phase: %d instances (jobs=%d)" % (len(todo), a.proof_jobs), flush=True)
        pcores = queue.Queue()
        for c in a.proof_cores[:a.proof_jobs]:
            pcores.put(c)
        count = [0]

        def work(path):
            core = pcores.get()
            try:
                self.proof_one(path, core)
            finally:
                pcores.put(core)
            with self.lock:
                row = self.rows[os.path.basename(path)]
                count[0] += 1
                print("[proof %d/%d] %-45s %-8s %s" % (count[0], len(todo), row["instance"][:45],
                                                      row["result"], row["proof_status"]), flush=True)
                self.rewrite()

        with ThreadPoolExecutor(max_workers=min(a.proof_jobs, len(a.proof_cores))) as ex:
            list(ex.map(work, todo))
        self.rewrite()

    # ---- metadata ------------------------------------------------------------
    def write_meta(self, instances):
        a = self.args
        solver = os.path.realpath(a.solver)
        sdir = os.path.dirname(solver)
        git = None
        marker = os.path.join(sdir, "GIT_HASH")
        if os.path.exists(marker):
            git = open(marker).read().strip()
        else:
            for d in (sdir, os.getcwd()):
                try:
                    git = subprocess.check_output(["git", "-C", d, "rev-parse", "--short", "HEAD"],
                                                  stderr=subprocess.DEVNULL, text=True).strip()
                    if subprocess.call(["git", "-C", d, "diff", "--quiet"],
                                       stderr=subprocess.DEVNULL):
                        git += "+dirty"
                    break
                except (subprocess.CalledProcessError, OSError):
                    continue
        sha = hashlib.sha256(open(solver, "rb").read()).hexdigest()
        meta = {"solver": solver, "solver_sha256": sha, "solver_git": git,
                "args": a.args, "seed_args": a.seed_args, "seed": a.seed, "proof_args": a.proof_args,
                "timeout": a.timeout, "mem_gb": a.mem_gb, "jobs": min(a.jobs, len(a.cores)),
                "cores": a.cores_spec, "instances": len(instances),
                "instances_sha256": hashlib.sha256(
                    "\n".join(sorted(os.path.basename(p) for p in instances)).encode()).hexdigest(),
                "proof_check": a.proof_check, "proof_max_solve_sec": a.proof_max_solve_sec,
                "proof_timeout": a.proof_timeout, "proof_mem_gb": a.proof_mem_gb,
                "proof_max_gb": a.proof_max_gb,
                "checker": a.checker if a.proof_check else None,
                "date": datetime.datetime.now().isoformat(timespec="seconds"),
                "host": platform.node(), "cmdline": " ".join(shlex.quote(x) for x in sys.argv),
                "note": a.note}
        path = os.path.join(self.outdir, "meta.json")
        if os.path.exists(path):  # resumed run: keep the original, note the resume
            old = json.load(open(path))
            for k in RESUME_KEYS:
                if old.get(k) != meta[k]:
                    sys.exit("run.py: cannot resume %s: %s was %r, is %r (use a new tag)" %
                             (a.tag, k, old.get(k), meta[k]))
            old.setdefault("resumed", []).append(meta["date"])
            for k in ("proof_check", "proof_max_solve_sec", "proof_timeout", "proof_mem_gb",
                      "proof_max_gb", "checker"):
                old[k] = meta[k]
            meta = old
        with open(path, "w") as f:
            json.dump(meta, f, indent=2)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--solver", required=True, help="solver binary")
    ap.add_argument("--args", default="",
                    help="solver arguments (one quoted string); {seed} is replaced by --seed, "
                         "{proof} by a proof file (timed proof-on runs)")
    ap.add_argument("--seed", type=int, default=0,
                    help="search seed (0 = deterministic default); recorded in meta.json")
    ap.add_argument("--seed-args", default="--seed={seed}",
                    help="appended to the solver arguments when --seed > 0 "
                         "(baseline: '-rnd-init -rnd-seed={seed}')")
    ap.add_argument("--tag", required=True, help="name of the run; results go to results/TAG")
    ap.add_argument("--timeout", type=float, default=300, help="wall-clock limit in seconds")
    ap.add_argument("--jobs", type=int, default=48, help="parallel jobs (one core each)")
    ap.add_argument("--cores", default="64-127", help="cores for timed runs, e.g. 64-127")
    ap.add_argument("--mem-gb", type=float, default=16, help="memory limit per job (RSS)")
    ap.add_argument("--instances", nargs="+", default=["*.qcir"],
                    help="globs (relative to --bench-dir), paths, or .txt lists of names")
    ap.add_argument("--bench-dir", default=DEFAULT_BENCH_DIR)
    ap.add_argument("--results-dir", default=os.path.join(HERE, "results"))
    ap.add_argument("--log-dir", default=DEFAULT_LOG_DIR, help="logs of failed runs")
    ap.add_argument("--note", default="", help="free text stored in meta.json")
    ap.add_argument("--proof-check", action="store_true",
                    help="re-run quick instances with proof logging and check with Lean")
    ap.add_argument("--proof-max-solve-sec", type=float, default=20,
                    help="proofs are attempted for instances solved within this time "
                         "(up to --timeout, i.e. for every solved instance)")
    ap.add_argument("--proof-solve-timeout", type=float, default=None,
                    help="time limit of the proof-logging solver run (default 2 x --timeout)")
    ap.add_argument("--proof-timeout", type=float, default=600, help="checker time limit")
    ap.add_argument("--proof-mem-gb", type=float, default=32, help="checker memory limit")
    ap.add_argument("--proof-max-gb", type=float, default=8,
                    help="a proof file above this size is abandoned (status too_large)")
    ap.add_argument("--trim", default=DEFAULT_TRIM, help="qlrup-trim binary")
    ap.add_argument("--trim-size", action="store_true",
                    help="with {proof} in --args: also record the size after qlrup-trim")
    ap.add_argument("--proof-args", default="-proof-binary",
                    help="extra solver flags for proof runs (default: binary format)")
    ap.add_argument("--proof-jobs", type=int, default=16)
    ap.add_argument("--proof-cores", default="0-63",
                    help="cores for the proof phase (not the benchmark cores)")
    ap.add_argument("--proof-dir", default=DEFAULT_PROOF_DIR)
    ap.add_argument("--checker", default=DEFAULT_CHECKER)
    args = ap.parse_args()
    if args.proof_solve_timeout is None:
        args.proof_solve_timeout = 2 * args.timeout

    if not os.access(args.solver, os.X_OK):
        sys.exit("run.py: solver %s is not executable" % args.solver)
    args.solver = os.path.abspath(args.solver)
    args.cores_spec = args.cores
    args.cores = parse_cores(args.cores)
    args.proof_cores = parse_cores(args.proof_cores)
    if args.proof_check and "{proof}" in args.args:
        sys.exit("run.py: {proof} in --args (timed proof run) cannot be combined with --proof-check")
    if (args.proof_check or args.trim_size) and not os.access(args.trim, os.X_OK):
        sys.exit("run.py: %s not found (cmake --build --preset release)" % args.trim)
    if args.proof_check and not os.access(args.checker, os.X_OK):
        sys.exit("run.py: checker %s not found (cd /home/ec2-user/qu-check && lake build)" % args.checker)

    instances = resolve_instances(args.instances, args.bench_dir)
    runner = Runner(args)
    runner.load()
    runner.write_meta(instances)
    runner.phase1(instances)
    if args.proof_check:
        runner.phase2(instances)
    runner.rewrite()
    rows = [r for r in runner.rows.values() if r["instance"] in {os.path.basename(p) for p in instances}]
    solved = sum(r["result"] in ("SAT", "UNSAT") for r in rows)
    bad = [r["instance"] for r in rows if r["result"] in ("ERROR", "MISMATCH")]
    gaps = [r["instance"] for r in rows if r["proof_status"] not in ("", "n/a", "ok") + REJECTED_STATUSES]
    badproof = [r["instance"] for r in rows if r["proof_status"] in REJECTED_STATUSES]
    print("run.py: %s: solved %d/%d; errors: %d; rejected proofs: %d; proof coverage gaps: %d -> %s" %
          (args.tag, solved, len(rows), len(bad), len(badproof), len(gaps), runner.csv_path))
    for n in bad:
        print("  ERROR/MISMATCH:", n)
    for n in badproof:
        print("  PROOF REJECTED:", n, runner.rows[n]["proof_status"])
    for n in gaps:
        print("  coverage gap:", n, runner.rows[n]["proof_status"])
    sys.exit(1 if bad or badproof else 0)


if __name__ == "__main__":
    main()
