#!/usr/bin/env python3
"""CPU time of two solver binaries on identical searches under benchmark-like load.

    load_measure.py --a BIN --a-args "ARGS" --b BIN --b-args "ARGS" --tag TAG [options]

The machine is loaded the way a benchmark run loads it.  bench/run.py hands the
name-sorted instances to the cores one by one, so the 8 cores that share an L3
cache run 8 neighbouring names, usually one family, and a core takes the next
job as soon as its job ends.  Here every L3 group of --cores runs one group of
bench/load-instances.txt (a window of 8 consecutive names of the sorted
instance list), instance j on the j-th core of the L3 group, and every core
restarts its instance as soon as it ends, so that all cores stay busy.  A round
lasts until every core has completed one run; the unfinished runs are then killed
and discarded.  The two binaries run in separate rounds (A, B, A, B, ...; all
processes running at one time are the same binary), because a mixed load hides
footprint effects: a binary that needs more cache hurts itself most when its
own neighbours share a cache with it.

The report gives, per instance, the median user CPU time of each arm over all
completed runs and rounds and their ratio B / A.  An instance enters the mean
only if the solver reports the same conflict count in every run of both arms,
i.e. if all runs did the same search, so the ratio measures engine speed.  See
README.md.
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
SYSFS_CPU = "/sys/devices/system/cpu"
CORES_PER_L3 = 8
# "copy" is the index of the run in the loop of its core
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


def run_core(binary, args, job, timeout, live, stop, first_done, runs):
    """Run one instance in a loop on one core until stop is set; every run that ended by
    itself or by the timeout is appended to runs.  A run cut short by the end of the round
    is discarded: its time says nothing."""
    name, path, core = job
    while not stop.is_set():
        proc = start(binary, args, path, core)
        live.append(proc)
        if stop.is_set():  # the round ended while this process was starting
            proc.kill()
        out = {}
        collect(proc, timeout, out)
        if stop.is_set():
            break
        runs.append({"instance": name, "copy": len(runs), "core": core, **out})
        first_done.set()


def run_round(binary, args, jobs, timeout):
    """Run every (instance, path, core) of jobs, each in a loop so that all cores stay busy,
    until every core has completed a run; returns the completed runs as dicts."""
    stop = threading.Event()
    live = []  # list.append is atomic; the processes are killed after stop is set
    first_done = [threading.Event() for _ in jobs]
    runs = [[] for _ in jobs]
    threads = [threading.Thread(target=run_core, args=(binary, args, job, timeout, live, stop, done, mine))
               for job, done, mine in zip(jobs, first_done, runs)]
    for t in threads:
        t.start()
    for done in first_done:
        done.wait()
    stop.set()
    for proc in live:
        if proc.returncode is None:
            proc.send_signal(signal.SIGKILL)
    for t in threads:
        t.join()
    return [r for mine in runs for r in mine]


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


def ratio_of(a, b):
    """Ratio of the medians B / A, or None when one of them is zero."""
    ma, mb = statistics.median(a), statistics.median(b)
    return mb / ma if ma > 0 and mb > 0 else None


def group_means(groups, summary):
    """(group, ratios of its instances with an identical search) for every group; the group is
    the dict of the meta data (comment, instances, cores)."""
    by_name = {name: (a, b, status) for name, a, b, status in summary}
    result = []
    for g in groups:
        ratios = []
        for name in g["instances"]:
            a, b, status = by_name[name]
            ratio = ratio_of(a, b) if status == "identical" else None
            if ratio is not None:
                ratios.append(ratio)
        result.append((g, ratios))
    return result


def report(meta, summary):
    out = ["# Load measurement %s" % meta["tag"], ""]
    for arm in "AB":
        b = meta["binaries"][arm]
        out.append("- %s (%s): `%s`, sha256 %s, args `%s`" % (arm, b["name"], b["path"], b["sha256"], b["args"]))
    out.append("- placement: L3 groups, cores kept busy (every core loops over its instance until every "
               "core has completed a run; timeout %g s per run); %d rounds" % (meta["timeout"], meta["rounds"]))
    for i, g in enumerate(meta["groups"]):
        idle = g["l3_cores"][len(g["instances"]):]
        out.append("- group %d on cores %s: %d instances%s" % (
            i, ",".join(map(str, g["l3_cores"])), len(g["instances"]),
            ", cores %s idle" % ",".join(map(str, idle)) if idle else ""))
    idle_groups = meta["idle_l3_groups"]
    if idle_groups:
        out.append("- L3 groups without instances (idle): %s" % "; ".join(
            ",".join(map(str, g)) for g in idle_groups))
    out.append("- order of the arms: %s" % ", ".join(
        "%s (%s)" % (r["arm"], r["start"]) for r in meta["order"]))
    if meta["force"]:
        out.append("- **--force**: other solver or benchmark processes may have been running")
    out += ["", "User CPU seconds, median over all completed runs and rounds; ratio is B / A.", ""]
    rows, ratios, unfinished = [], [], []
    for name, a, b, status in summary:
        if status == "unfinished":
            unfinished.append(name)
            rows.append([name, "-", "-", "-", "-", "-", "unfinished"])
            continue
        ratio = ratio_of(a, b)
        mark = "yes" if status == "identical" else "different search"
        if status == "identical" and ratio is not None:
            ratios.append(ratio)
        rows.append([name, "%.2f" % statistics.median(a), "%.2f" % statistics.median(b),
                     "%.3f" % ratio if ratio is not None else "-", "%.2f-%.2f" % (min(a), max(a)),
                     "%.2f-%.2f" % (min(b), max(b)), mark])
    rows.append(["**geometric mean** (n=%d identical searches)" % len(ratios), "", "",
                 "**%.3f**" % geomean(ratios) if ratios else "-", "", "", ""])
    out += table(["instance", "A median", "B median", "B / A", "A min-max", "B min-max",
                  "identical search"], rows) + [""]
    out += ["Per group (geometric mean of B / A over the identical searches of the group):", ""]
    grows = []
    for i, (g, rs) in enumerate(group_means(meta["groups"], summary)):
        grows.append([str(i), g["instances"][0], g["comment"], str(len(rs)),
                      "%.3f" % geomean(rs) if rs else "-"])
    out += table(["group", "first instance", "chosen as", "n", "geometric mean B / A"], grows) + [""]
    if unfinished:
        out += ["Unfinished (timeout or unexpected exit code, excluded): %s" % ", ".join(unfinished), ""]
    return "\n".join(out) + "\n"


def l3_groups(cores, sysfs_root=SYSFS_CPU):
    """The cores split into the L3 cache groups of the machine, as lists in the order of first
    appearance.  Raises ValueError if a group is only partly inside cores: neighbours outside
    the measurement would share the cache."""
    groups = []
    for core in cores:
        path = os.path.join(sysfs_root, "cpu%d" % core, "cache", "index3", "shared_cpu_list")
        try:
            with open(path) as f:
                members = sorted(run.parse_cores(f.read().strip()))
        except OSError as e:
            raise ValueError("cannot read the L3 group of core %d: %s" % (core, e))
        if members not in groups:
            groups.append(members)
    outside = sorted(c for g in groups for c in g if c not in cores)
    if outside:
        raise ValueError("--cores must consist of whole L3 groups; cores %s share a cache with them"
                         % ",".join(map(str, outside)))
    return groups


def read_groups(path, bench_dir):
    """Groups of the instance file: blocks of instance names separated by blank lines; the
    comment lines directly above a block (without the '#') describe it.  Returns a list of
    {"comment", "instances"}.  Every group must be a window of consecutive names of the sorted
    instance list, because that is what shares an L3 cache in a benchmark run."""
    groups, comment, names = [], [], []

    def close():
        if names:
            groups.append({"comment": " ".join(comment), "instances": list(names)})
        comment.clear()
        names.clear()

    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                close()
            elif line.startswith("#"):
                if names:
                    close()
                comment.append(line.lstrip("# "))
            else:
                names.append(line)
    close()
    listing = sorted(f for f in os.listdir(bench_dir) if f.endswith(".qcir"))
    for g in groups:
        if len(g["instances"]) > CORES_PER_L3:
            raise ValueError("group of %s has %d instances, an L3 group has %d cores"
                             % (g["instances"][0], len(g["instances"]), CORES_PER_L3))
        for name in g["instances"]:
            if name not in listing:
                raise ValueError("instance %s not found in %s" % (name, bench_dir))
        first = listing.index(g["instances"][0])
        if g["instances"] != listing[first:first + len(g["instances"])]:
            raise ValueError("group of %s is not a window of consecutive names of the sorted instance "
                             "list in %s" % (g["instances"][0], bench_dir))
    return groups


def place(groups, l3):
    """Group g on the g-th L3 group; returns (groups with their l3_cores, idle L3 groups)."""
    if len(groups) > len(l3):
        raise ValueError("%d groups in the instance file but only %d L3 groups in --cores"
                         % (len(groups), len(l3)))
    for g, cores in zip(groups, l3):
        if len(g["instances"]) > len(cores):
            raise ValueError("group of %s has %d instances but its L3 group only %d cores"
                             % (g["instances"][0], len(g["instances"]), len(cores)))
    placed = [{**g, "l3_cores": l3[i]} for i, g in enumerate(groups)]
    return placed, l3[len(groups):]


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
    ap.add_argument("--instances", default=DEFAULT_INSTANCES,
                    help="file with groups of at most 8 instance names, separated by blank lines")
    ap.add_argument("--bench-dir", default=DEFAULT_BENCH_DIR)
    ap.add_argument("--rounds", type=int, default=2, help="rounds per arm, alternating A, B, A, B, ...")
    ap.add_argument("--cores", default=run.half_cores()[0],
                    help="whole L3 groups; default: the lower half of the machine")
    ap.add_argument("--timeout", type=float, default=60, help="limit of a single run in seconds")
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--sysfs-root", default=SYSFS_CPU, help=argparse.SUPPRESS)  # a fake tree for the test
    ap.add_argument("--force", action="store_true", help="start although other solver processes run")
    args = ap.parse_args(glue_arguments(sys.argv[1:]))

    try:
        groups, idle_l3 = place(read_groups(args.instances, args.bench_dir),
                                l3_groups(run.parse_cores(args.cores), args.sysfs_root))
    except ValueError as e:
        sys.exit("load_measure.py: %s" % e)
    busy = busy_processes()
    if busy and not args.force:
        sys.exit("load_measure.py: other processes would disturb the measurement (--force overrides):\n  "
                 + "\n  ".join(busy))

    jobs = [(name, os.path.join(args.bench_dir, name), g["l3_cores"][j])
            for g in groups for j, name in enumerate(g["instances"])]
    binaries = {"A": (args.a, args.a_args, args.a_name), "B": (args.b, args.b_args, args.b_name)}
    meta = {"tag": args.tag, "cores": args.cores, "rounds": args.rounds, "groups": groups,
            "idle_l3_groups": idle_l3, "timeout": args.timeout, "force": args.force,
            "host": platform.node(), "order": [],
            "date": datetime.datetime.now().isoformat(timespec="seconds"),
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
            for res in run_round(binary, arm_args, jobs, args.timeout):
                rows.append({"arm": arm, "round": rnd, "result": verdict(res), **res})
            print("  %.0f s" % (time.time() - started), file=sys.stderr, flush=True)

    outdir = os.path.join(args.results_dir, args.tag)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "load.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, CSV_COLUMNS, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow({**r, "user": "%.3f" % r["user"], "sys": "%.3f" % r["sys"],
                        "conflicts": "" if r["conflicts"] is None else r["conflicts"]})
    with open(os.path.join(outdir, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2)
    text = report(meta, summarize(rows, [n for g in groups for n in g["instances"]]))
    with open(os.path.join(outdir, "load.md"), "w") as f:
        f.write(text)
    sys.stdout.write(text)


if __name__ == "__main__":
    main()
