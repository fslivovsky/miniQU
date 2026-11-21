#!/usr/bin/env python3
"""Benchmark runner for QCIR solvers (miniQU and its rewrite).

Runs every instance once, each job pinned to its own core, and records
wall time, CPU time and peak RSS.  Timeout and memory limit are enforced by
killing the process group.  The verdict comes from the exit code (10 = SAT,
20 = UNSAT) and is cross-checked against the printed "SATISFIABLE" /
"UNSATISFIABLE" line.  Results go to results/TAG/results.csv and
results/TAG/meta.json.  The run is resumable: instances already present in
the CSV are skipped.

With --proof-check, a second phase (after all timed runs, on separate cores
so timings stay clean) re-runs the instances solved within
--proof-max-solve-sec with -proof=FILE, checks the proof with the Lean
checker qlrup-check, and deletes the proof file.

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
COLUMNS = ["instance", "family", "result", "exit", "wall", "cpu", "rss_mb",
           "proof_status", "proof_check_sec", "proof_bytes"]
PROOF_FSIZE_LIMIT = 20 * 2**30  # a proof run is aborted when its file exceeds this


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
    prefix = ["taskset", "-c", str(core)]
    if fsize_limit:
        prefix = ["prlimit", "--fsize=%d" % fsize_limit] + prefix
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


def classify(r, printed):
    if r["status"] == "timeout":
        return "TIMEOUT"
    if r["status"] == "memout":
        return "MEMOUT"
    by_exit = {10: "SAT", 20: "UNSAT"}.get(r["exit"])
    if by_exit is None:
        return "ERROR"
    if printed is not None and printed != by_exit:
        return "MISMATCH"  # exit code and printed line disagree
    return by_exit


class Runner:
    def __init__(self, args):
        self.args = args
        self.solver_args = shlex.split(args.args)
        self.proof_args = shlex.split(args.proof_args)
        self.logdir = os.path.join(args.log_dir, args.tag)
        os.makedirs(self.logdir, exist_ok=True)
        self.outdir = os.path.join(args.results_dir, args.tag)
        os.makedirs(self.outdir, exist_ok=True)
        self.csv_path = os.path.join(self.outdir, "results.csv")
        self.rows = {}
        self.lock = threading.Lock()
        self.done = 0

    # ---- CSV --------------------------------------------------------------
    def load(self):
        if os.path.exists(self.csv_path):
            with open(self.csv_path, newline="") as f:
                for row in csv.DictReader(f):
                    self.rows[row["instance"]] = row

    def append_row(self, row):
        new = not os.path.exists(self.csv_path) or os.path.getsize(self.csv_path) == 0
        with open(self.csv_path, "a", newline="") as f:
            w = csv.DictWriter(f, COLUMNS)
            if new:
                w.writeheader()
            w.writerow(row)

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
        r = run_pinned([a.solver] + self.solver_args + [path], core, a.timeout,
                       a.mem_gb * 1024, out)
        result = classify(r, printed_verdict(out))
        if result in ("SAT", "UNSAT"):
            os.remove(out)  # keep logs only for failures
        row = {"instance": name, "family": family_of(name), "result": result,
               "exit": r["exit"], "wall": "%.3f" % r["wall"], "cpu": "%.3f" % r["cpu"],
               "rss_mb": "%.1f" % r["rss_mb"], "proof_status": "", "proof_check_sec": "",
               "proof_bytes": ""}
        return row

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
    def proof_one(self, path, core):
        a = self.args
        name = os.path.basename(path)
        row = self.rows[name]
        proof = os.path.join(a.proof_dir, "%s-%s.proof" % (a.tag, name))
        out = os.path.join(self.logdir, name + ".proof.out")
        os.makedirs(a.proof_dir, exist_ok=True)
        try:
            r = run_pinned([a.solver] + self.solver_args + self.proof_args +
                           ["-proof=" + proof, path], core, a.timeout, a.mem_gb * 1024, out,
                           fsize_limit=PROOF_FSIZE_LIMIT)
            res = classify(r, printed_verdict(out))
            row["proof_bytes"] = os.path.getsize(proof) if os.path.exists(proof) else 0
            if res != row["result"]:
                row["proof_status"] = "solve_" + res.lower()
                return
            os.remove(out)
            t0 = time.monotonic()
            chk = run_pinned([a.checker, path, proof], core, a.proof_timeout,
                             a.mem_gb * 1024, out)
            row["proof_check_sec"] = "%.3f" % (time.monotonic() - t0)
            text = open(out, errors="replace").read()
            m = re.search(r"^s (VERIFIED TRUE|VERIFIED FALSE|NOT VERIFIED.*)$", text, re.M)
            expect = "VERIFIED TRUE" if row["result"] == "SAT" else "VERIFIED FALSE"
            if chk["status"] == "timeout":
                row["proof_status"] = "check_timeout"
            elif chk["status"] == "memout":
                row["proof_status"] = "check_memout"
            elif m is None:
                row["proof_status"] = "check_error"
            elif m.group(1) == expect:
                row["proof_status"] = "ok"
                os.remove(out)
            elif m.group(1).startswith("NOT VERIFIED"):
                row["proof_status"] = "rejected"
            else:
                row["proof_status"] = "wrong_verdict"  # verified, but the opposite result
        finally:
            if os.path.exists(proof):
                os.remove(proof)

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
    def write_meta(self):
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
                "args": a.args, "proof_args": a.proof_args, "timeout": a.timeout,
                "mem_gb": a.mem_gb, "jobs": min(a.jobs, len(a.cores)), "cores": a.cores_spec,
                "proof_check": a.proof_check, "proof_max_solve_sec": a.proof_max_solve_sec,
                "checker": a.checker if a.proof_check else None,
                "date": datetime.datetime.now().isoformat(timespec="seconds"),
                "host": platform.node(), "cmdline": " ".join(shlex.quote(x) for x in sys.argv),
                "note": a.note}
        path = os.path.join(self.outdir, "meta.json")
        if os.path.exists(path):  # resumed run: keep the original, note the resume
            old = json.load(open(path))
            old.setdefault("resumed", []).append(meta["date"])
            for k in ("proof_check", "proof_max_solve_sec", "checker"):
                old[k] = meta[k]
            meta = old
        with open(path, "w") as f:
            json.dump(meta, f, indent=2)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--solver", required=True, help="solver binary")
    ap.add_argument("--args", default="", help="solver arguments (one quoted string)")
    ap.add_argument("--tag", required=True, help="name of the run; results go to results/TAG")
    ap.add_argument("--timeout", type=float, default=300, help="wall-clock limit in seconds")
    ap.add_argument("--jobs", type=int, default=48, help="parallel jobs (one core each)")
    ap.add_argument("--cores", default="64-127", help="cores for timed runs, e.g. 64-127")
    ap.add_argument("--mem-gb", type=float, default=8, help="memory limit per job (RSS)")
    ap.add_argument("--instances", nargs="+", default=["*.qcir"],
                    help="globs (relative to --bench-dir), paths, or .txt lists of names")
    ap.add_argument("--bench-dir", default=DEFAULT_BENCH_DIR)
    ap.add_argument("--results-dir", default=os.path.join(HERE, "results"))
    ap.add_argument("--log-dir", default=DEFAULT_LOG_DIR, help="logs of failed runs")
    ap.add_argument("--note", default="", help="free text stored in meta.json")
    ap.add_argument("--proof-check", action="store_true",
                    help="re-run quick instances with proof logging and check with Lean")
    ap.add_argument("--proof-max-solve-sec", type=float, default=20)
    ap.add_argument("--proof-timeout", type=float, default=600, help="checker time limit")
    ap.add_argument("--proof-args", default="-proof-binary",
                    help="extra solver flags for proof runs (default: binary format)")
    ap.add_argument("--proof-jobs", type=int, default=16)
    ap.add_argument("--proof-cores", default="0-63",
                    help="cores for the proof phase (not the benchmark cores)")
    ap.add_argument("--proof-dir", default=DEFAULT_PROOF_DIR)
    ap.add_argument("--checker", default=DEFAULT_CHECKER)
    args = ap.parse_args()

    if not os.access(args.solver, os.X_OK):
        sys.exit("run.py: solver %s is not executable" % args.solver)
    args.solver = os.path.abspath(args.solver)
    args.cores_spec = args.cores
    args.cores = parse_cores(args.cores)
    args.proof_cores = parse_cores(args.proof_cores)
    if args.proof_check and not os.access(args.checker, os.X_OK):
        sys.exit("run.py: checker %s not found (cd /home/ec2-user/qu-check && lake build)" % args.checker)

    instances = resolve_instances(args.instances, args.bench_dir)
    runner = Runner(args)
    runner.load()
    runner.write_meta()
    runner.phase1(instances)
    if args.proof_check:
        runner.phase2(instances)
    runner.rewrite()
    rows = [r for r in runner.rows.values() if r["instance"] in {os.path.basename(p) for p in instances}]
    solved = sum(r["result"] in ("SAT", "UNSAT") for r in rows)
    bad = [r["instance"] for r in rows if r["result"] in ("ERROR", "MISMATCH")]
    badproof = [r["instance"] for r in rows if r["proof_status"] not in ("", "n/a", "ok")]
    print("run.py: %s: solved %d/%d; errors: %d; proof problems: %d -> %s" %
          (args.tag, solved, len(rows), len(bad), len(badproof), runner.csv_path))
    for n in bad:
        print("  ERROR/MISMATCH:", n)
    for n in badproof:
        print("  PROOF PROBLEM:", n, runner.rows[n]["proof_status"])
    sys.exit(1 if bad or badproof else 0)


if __name__ == "__main__":
    main()
