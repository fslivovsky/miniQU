#!/usr/bin/env python3
"""CPU time of two solver binaries on identical searches under benchmark-like load.

    load_measure.py --a BIN --a-args "ARGS" --b BIN --b-args "ARGS" --tag TAG [options]

A list of instances is run in several copies, one process per core, so that the
machine looks like a benchmark run: every core busy, the shared L3 caches full.
The two binaries run in separate rounds (A, B, A, B, ...; all processes running
at one time are the same binary), because a mixed load hides footprint effects:
a binary that needs more cache hurts itself most when its own copies share a cache.
Copy k of instance j sits on the same core in both arms.

The report gives, per instance, the median user CPU time of each arm over all
copies and rounds and their ratio B / A.  An instance enters the mean only if the
solver reports the same conflict count in every run of both arms, i.e. if all runs
did the same search, so the ratio measures engine speed.  See README.md.
"""
import argparse
import csv
import datetime
import hashlib
import json
import math
import os
import platform
import shlex
import signal
import statistics
import subprocess
import sys
import threading
import time

import run
from benchlib import DEFAULT_RESULTS, table

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_INSTANCES = os.path.join(HERE, "load-instances.txt")
DEFAULT_BENCH_DIR = "/home/ec2-user/benchmarks/qcir"
CSV_COLUMNS = ["arm", "round", "instance", "copy", "core", "result", "user", "sys", "conflicts"]
VERDICTS = {10: "SAT", 20: "UNSAT"}
def ancestors():
    """Pids of this process and its parents (the shell that started us is not a disturbance)."""
    pids, pid = set(), os.getpid()
    while pid > 1:
        pids.add(pid)
        with open("/proc/%d/stat" % pid) as f:
            pid = int(f.read().rsplit(")", 1)[1].split()[1])
    return pids


def is_busy(argv):
    """Whether a process with this argv disturbs the measurement: a solver, a benchmark run
    or another measurement.  Only what the process is counts, not words in its arguments:
    a shell whose -c string mentions miniQU is harmless."""
    if not argv:
        return False
    program = os.path.basename(argv[0])
    if program in ("miniQU", "load_measure.py") or argv[0].endswith("bench/run.py"):
        return True
    if not program.startswith("python"):
        return False
    script = next((a for a in argv[1:] if not a.startswith("-")), "")
    return (os.path.basename(script) == "load_measure.py"
            or (os.path.basename(script) == "run.py"
                and os.path.basename(os.path.dirname(script)) == "bench"))


def busy_processes():
    """'PID command line' of every other process that would disturb the measurement."""
    mine = ancestors()
    found = []
    for entry in os.listdir("/proc"):
        if not entry.isdigit() or int(entry) in mine:
            continue
        try:
            with open("/proc/%s/cmdline" % entry, "rb") as f:
                argv = f.read().decode(errors="replace").split("\0")[:-1]
        except OSError:  # the process exited or is not readable
            continue
        if is_busy(argv):
            found.append("%s %s" % (entry, " ".join(argv)))
    return found


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def start(binary, args, path, core):
    """Start one solver pinned to core, stdout captured; returns the Popen object."""
    return subprocess.Popen([binary] + shlex.split(args) + ["-verb=1", path], stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL, text=True, errors="replace",
                            preexec_fn=lambda: os.sched_setaffinity(0, {core}))


def collect(proc, timeout, out):
    """Wait for proc (killing it after timeout seconds) and store its measurements in out.

    os.wait4 gives the CPU times of this child alone; the pipe is drained first so that
    the solver never blocks on a full pipe."""
    timer = threading.Timer(timeout, lambda: proc.send_signal(signal.SIGKILL))
    timer.start()
    text = proc.stdout.read()
    _, status, usage = os.wait4(proc.pid, 0)
    timer.cancel()
    proc.returncode = os.waitstatus_to_exitcode(status)
    out.update(code=proc.returncode, user=usage.ru_utime, sys=usage.ru_stime,
               conflicts=run.parse_stats_text(text).get("conflicts"))


def run_round(binary, args, jobs, timeout):
    """Run every (instance, copy, core) of jobs at once; returns one result dict per job."""
    procs = [start(binary, args, path, core) for _, _, path, core in jobs]
    results = [{} for _ in jobs]
    threads = [threading.Thread(target=collect, args=(p, timeout, r)) for p, r in zip(procs, results)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return results


def verdict(result):
    code = result["code"]
    if code in VERDICTS:
        return VERDICTS[code]
    return "TIMEOUT" if code == -signal.SIGKILL else "EXIT%d" % code


def geomean(values):
    return math.exp(sum(math.log(v) for v in values) / len(values))


def summarize(rows, instances):
    """Per instance: (times of A, times of B, status) with status identical, different or unfinished."""
    summary = []
    for name in instances:
        mine = [r for r in rows if r["instance"] == name]
        times = {arm: [r["user"] for r in mine if r["arm"] == arm] for arm in "AB"}
        if any(r["result"] not in VERDICTS.values() for r in mine):
            status = "unfinished"
        elif len({r["conflicts"] for r in mine}) == 1 and mine[0]["conflicts"] is not None:
            status = "identical"
        else:
            status = "different search"
        summary.append((name, times["A"], times["B"], status))
    return summary


def report(meta, summary):
    out = ["# Load measurement %s" % meta["tag"], ""]
    for arm in "AB":
        b = meta["binaries"][arm]
        out.append("- %s (%s): `%s`, sha256 %s, args `%s`" % (arm, b["name"], b["path"], b["sha256"], b["args"]))
    out.append("- cores %s, %d copies of %d instances, %d rounds" % (
        meta["cores"], meta["copies"], len(summary), meta["rounds"]))
    out.append("- order of the arms: %s" % ", ".join(
        "%s (%s)" % (r["arm"], r["start"]) for r in meta["order"]))
    if meta["force"]:
        out.append("- **--force**: other solver or benchmark processes may have been running")
    out += ["", "User CPU seconds, median over all copies and rounds; ratio is B / A.", ""]
    rows, ratios, unfinished = [], [], []
    for name, a, b, status in summary:
        if status == "unfinished":
            unfinished.append(name)
            rows.append([name, "-", "-", "-", "-", "-", "unfinished"])
            continue
        ma, mb = statistics.median(a), statistics.median(b)
        ratio = mb / ma if ma > 0 else float("nan")
        mark = "yes" if status == "identical" else "different search"
        if status == "identical" and ma > 0 and mb > 0:
            ratios.append(ratio)
        rows.append([name, "%.2f" % ma, "%.2f" % mb, "%.3f" % ratio, "%.2f-%.2f" % (min(a), max(a)),
                     "%.2f-%.2f" % (min(b), max(b)), mark])
    rows.append(["**geometric mean** (n=%d identical searches)" % len(ratios), "", "",
                 "**%.3f**" % geomean(ratios) if ratios else "-", "", "", ""])
    out += table(["instance", "A median", "B median", "B / A", "A min-max", "B min-max",
                  "identical search"], rows) + [""]
    if unfinished:
        out += ["Unfinished (timeout or unexpected exit code, excluded): %s" % ", ".join(unfinished), ""]
    return "\n".join(out) + "\n"


def read_instances(path, bench_dir):
    with open(path) as f:
        names = [line.strip() for line in f if line.strip() and not line.startswith("#")]
    paths = []
    for name in names:
        full = name if os.path.isabs(name) else os.path.join(bench_dir, name)
        if not os.path.exists(full):
            sys.exit("load_measure.py: instance %s not found (--bench-dir %s)" % (name, bench_dir))
        paths.append(full)
    return names, paths


def glue_arguments(argv):
    """argparse takes a value like "--seed=1" for an option; turn "--b-args VALUE" into "--b-args=VALUE"."""
    out = []
    for i, word in enumerate(argv):
        if i > 0 and argv[i - 1] in ("--a-args", "--b-args"):
            out[-1] += "=" + word
        else:
            out.append(word)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--a", required=True, help="binary of arm A (the reference)")
    ap.add_argument("--a-args", default="", help="arguments of A (one quoted string)")
    ap.add_argument("--b", required=True, help="binary of arm B")
    ap.add_argument("--b-args", default="")
    ap.add_argument("--a-name", default="A")
    ap.add_argument("--b-name", default="B")
    ap.add_argument("--tag", required=True)
    ap.add_argument("--instances", default=DEFAULT_INSTANCES, help="file with one instance name per line")
    ap.add_argument("--bench-dir", default=DEFAULT_BENCH_DIR)
    ap.add_argument("--copies", type=int, default=4)
    ap.add_argument("--rounds", type=int, default=2, help="rounds per arm, alternating A, B, A, B, ...")
    ap.add_argument("--cores", default=run.half_cores()[0], help="default: the lower half of the machine")
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--force", action="store_true", help="start although other solver processes run")
    args = ap.parse_args(glue_arguments(sys.argv[1:]))

    names, paths = read_instances(args.instances, args.bench_dir)
    cores = run.parse_cores(args.cores)
    if len(names) * args.copies > len(cores):
        sys.exit("load_measure.py: %d processes (%d instances x %d copies) but only %d cores in %s" % (
            len(names) * args.copies, len(names), args.copies, len(cores), args.cores))
    busy = busy_processes()
    if busy and not args.force:
        sys.exit("load_measure.py: other processes would disturb the measurement (--force overrides):\n  "
                 + "\n  ".join(busy))

    # copy k of instance j gets the same core in both arms
    jobs = [(name, k, path, cores[k * len(names) + j])
            for k in range(args.copies) for j, (name, path) in enumerate(zip(names, paths))]
    binaries = {"A": (args.a, args.a_args, args.a_name), "B": (args.b, args.b_args, args.b_name)}
    meta = {"tag": args.tag, "cores": args.cores, "copies": args.copies, "rounds": args.rounds,
            "timeout": args.timeout, "force": args.force, "host": platform.node(),
            "date": datetime.datetime.now().isoformat(timespec="seconds"), "order": [],
            "binaries": {arm: {"name": name, "path": os.path.realpath(b), "sha256": sha256(b), "args": a}
                         for arm, (b, a, name) in binaries.items()}}
    rows = []
    for rnd in range(1, args.rounds + 1):
        for arm in "AB":
            binary, arm_args, _ = binaries[arm]
            meta["order"].append({"arm": arm, "round": rnd,
                                  "start": datetime.datetime.now().isoformat(timespec="seconds")})
            print("round %d, arm %s ..." % (rnd, arm), file=sys.stderr, flush=True)
            started = time.time()
            for (name, k, _, core), res in zip(jobs, run_round(binary, arm_args, jobs, args.timeout)):
                rows.append({"arm": arm, "round": rnd, "instance": name, "copy": k, "core": core,
                             "result": verdict(res), "user": res["user"], "sys": res["sys"],
                             "conflicts": res["conflicts"]})
            print("  %.0f s" % (time.time() - started), file=sys.stderr, flush=True)

    outdir = os.path.join(args.results_dir, args.tag)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "load.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, CSV_COLUMNS)
        w.writeheader()
        for r in rows:
            w.writerow({**r, "user": "%.3f" % r["user"], "sys": "%.3f" % r["sys"],
                        "conflicts": "" if r["conflicts"] is None else r["conflicts"]})
    with open(os.path.join(outdir, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2)
    text = report(meta, summarize(rows, names))
    with open(os.path.join(outdir, "load.md"), "w") as f:
        f.write(text)
    sys.stdout.write(text)


if __name__ == "__main__":
    main()
