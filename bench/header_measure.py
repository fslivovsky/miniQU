#!/usr/bin/env python3
"""Header measurement of ROADMAP M1.3 (review 00, S3).

Compares the baseline and the new release binary, both with default options,
on (a) the ten largest instances (by file size) the baseline solves and (b)
the ten solved instances with the highest baseline propagation counts.  Each
run is pinned to one core, at most 8 run in parallel on cores 0-63.  This
is a ratio measurement of propagation speed and memory, not a benchmark
claim: different search paths make the two binaries do different work.

Per instance and binary: propagations, conflicts, wall and CPU seconds,
parse seconds, propagations per second of search time (CPU time minus
parse time), peak RSS.  Output: <out>/results.csv and <out>/table.md with
the geometric means of the new/baseline ratios.

Candidates that either binary does not solve within the timeout are
skipped in favour of the next one of the same group.

    bench/header_measure.py --new BUILD/miniQU --tag TAG
"""

import argparse
import csv
import math
import os
import re
import subprocess
import threading
import sys
from concurrent.futures import ThreadPoolExecutor

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORK = "/home/ec2-user/miniqu-work"
INSTANCES = "/home/ec2-user/benchmarks/qcir"
BASELINE = WORK + "/baseline/miniQU"
BASELINE_CSV = REPO + "/bench/results/baseline-t180/results.csv"

PATTERNS = {
    "baseline": {
        "propagations": r"^propagations\s*:\s*(\d+)",
        "conflicts": r"^conflicts\s*:\s*(\d+)",
        "parse": r"Parse time:\s*([\d.]+) s",
    },
    "new": {
        "propagations": r"^c stat propagations (\d+)",
        "conflicts": r"^c stat conflicts (\d+)",
        "parse": r"^c parsed and encoded in ([\d.]+) seconds",
    },
}


def run(binary, kind, name, core, timeout):
    """One run under /usr/bin/time -v on one core; returns a dict."""
    cmd = ["taskset", "-c", str(core), "/usr/bin/time", "-v", "timeout",
           str(timeout), binary, "-verb=1", f"{INSTANCES}/{name}"]
    p = subprocess.run(cmd, capture_output=True, text=True)
    out, err = p.stdout, p.stderr
    result = {"solved": p.returncode in (10, 20), "exit": p.returncode}
    for key, pattern in PATTERNS[kind].items():
        m = re.search(pattern, out, re.M)
        result[key] = float(m.group(1)) if m else None
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", err)
    result["rss_mb"] = int(m.group(1)) / 1024 if m else None
    user = re.search(r"User time \(seconds\): ([\d.]+)", err)
    system = re.search(r"System time \(seconds\): ([\d.]+)", err)
    result["cpu"] = float(user.group(1)) + float(system.group(1))
    m = re.search(r"Elapsed.*: (?:(\d+):)?(\d+):([\d.]+)$", err, re.M)
    result["wall"] = (int(m.group(1) or 0) * 3600 + int(m.group(2)) * 60 +
                      float(m.group(3)))
    result["verdict"] = {10: "SAT", 20: "UNSAT"}.get(p.returncode, "FAIL")
    search = result["cpu"] - (result["parse"] or 0)
    props = result["propagations"]
    result["props_per_sec"] = props / search if props and search > 0 else None
    return result


def parallel(jobs, workers=8):
    """jobs: list of (binary, kind, name); core = worker slot."""
    free = list(range(workers))
    lock = threading.Lock()

    def task(job):
        with lock:
            core = free.pop()
        try:
            return run(*job[:3], core, job[3])
        finally:
            with lock:
                free.append(core)

    with ThreadPoolExecutor(workers) as pool:
        return list(pool.map(task, jobs))


def geomean(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--new", required=True, help="new release binary")
    ap.add_argument("--tag", required=True)
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--pool", type=int, default=30,
                    help="longest baseline runs searched for high counts")
    ap.add_argument("--count", type=int, default=10)
    args = ap.parse_args()
    out = f"{REPO}/bench/results/header-{args.tag}"
    os.makedirs(out, exist_ok=True)

    rows = list(csv.DictReader(open(BASELINE_CSV)))
    solved = [r["instance"] for r in rows if r["result"] in ("SAT", "UNSAT")]
    by_size = sorted(solved, key=lambda n: -os.path.getsize(f"{INSTANCES}/{n}"))
    longest = sorted(solved, key=lambda n: -float(
        next(r for r in rows if r["instance"] == n)["wall"]))[:args.pool]

    # Baseline propagation counts of the long runs, for group (b).
    counts = parallel([(BASELINE, "baseline", n, args.timeout)
                       for n in longest])
    by_props = [n for n, r in sorted(
        zip(longest, counts), key=lambda x: -(x[1]["propagations"] or 0))]

    groups = {"largest": by_size[:args.count + 4],
              "propagations": by_props[:args.count + 4]}
    names = sorted(set(groups["largest"]) | set(groups["propagations"]))
    jobs = [(b, k, n, args.timeout) for n in names
            for b, k in ((BASELINE, "baseline"), (args.new, "new"))]
    measured = parallel(jobs)
    result = {}
    for (b, k, n, _), r in zip(jobs, measured):
        result[(n, k)] = r

    fields = ["group", "instance", "binary", "verdict", "propagations",
              "conflicts", "wall", "cpu", "parse", "props_per_sec", "rss_mb"]
    chosen = []
    with open(f"{out}/results.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fields, extrasaction="ignore")
        w.writeheader()
        for g, candidates in groups.items():
            picked = [n for n in candidates
                      if result[(n, "baseline")]["solved"] and
                      result[(n, "new")]["solved"] and
                      result[(n, "baseline")]["verdict"] ==
                      result[(n, "new")]["verdict"]][:args.count]
            for n in picked:
                chosen.append((g, n))
                for k in ("baseline", "new"):
                    w.writerow({"group": g, "instance": n, "binary": k,
                                **result[(n, k)]})
    with open(f"{out}/table.md", "w") as f:
        f.write("| group | instance | props base | props new | props/s base "
                "| props/s new | ratio | conflicts base | conflicts new "
                "| RSS base MB | RSS new MB | RSS ratio | time base | time new |\n"
                "|" + "---|" * 14 + "\n")
        ratios = {}
        for g, n in chosen:
            b, c = result[(n, "baseline")], result[(n, "new")]
            pr = c["props_per_sec"] / b["props_per_sec"]
            rr = c["rss_mb"] / b["rss_mb"]
            ratios.setdefault(g, []).append((pr, rr, c["cpu"] / b["cpu"]))
            f.write(f"| {g} | {n} | {b['propagations']:.0f} | "
                    f"{c['propagations']:.0f} | {b['props_per_sec']:.3g} | "
                    f"{c['props_per_sec']:.3g} | {pr:.2f} | "
                    f"{b['conflicts']:.0f} | {c['conflicts']:.0f} | "
                    f"{b['rss_mb']:.0f} | {c['rss_mb']:.0f} | {rr:.2f} | "
                    f"{b['cpu']:.1f} | {c['cpu']:.1f} |\n")
        f.write("\nGeometric means of new/baseline:\n\n"
                "| group | instances | props/s | RSS | CPU time |\n"
                "|---|---|---|---|---|\n")
        for g, rs in list(ratios.items()) + [
                ("all", [x for v in ratios.values() for x in v])]:
            f.write(f"| {g} | {len(rs)} | {geomean([x[0] for x in rs]):.3f} | "
                    f"{geomean([x[1] for x in rs]):.3f} | "
                    f"{geomean([x[2] for x in rs]):.3f} |\n")
    print(open(f"{out}/table.md").read())


if __name__ == "__main__":
    sys.exit(main())
