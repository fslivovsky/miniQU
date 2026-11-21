#!/usr/bin/env python3
"""Compare benchmark runs produced by run.py.

    compare.py TAG_A TAG_B [TAG_C ...] [--out FILE] [--cactus FILE] [--top N]

The first tag is the reference for the speedup/regression tables.  Only
instances present in every run are compared.  Output is markdown (stdout, or
--out).  Result discrepancies (one run says SAT, another UNSAT) and solver
errors are listed at the top; they are blocking bugs.  --cactus writes the
cactus-plot data (sorted solve times per tag) as CSV.
"""
import argparse
import csv
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SOLVED = ("SAT", "UNSAT")
MIN_TIME = 0.1  # seconds; times below this are clamped when computing ratios


def load(results_dir, tag):
    d = os.path.join(results_dir, tag)
    try:
        with open(os.path.join(d, "results.csv"), newline="") as f:
            rows = {r["instance"]: r for r in csv.DictReader(f)}
    except OSError:
        sys.exit("compare.py: no results for tag %r in %s" % (tag, d))
    try:
        with open(os.path.join(d, "meta.json")) as f:
            meta = json.load(f)
    except OSError:
        meta = {}
    return rows, meta


def wall(r):
    return float(r["wall"])


def table(header, rows):
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join(["---"] + ["---:"] * (len(header) - 1)) + "|"]
    out += ["| " + " | ".join(str(c) for c in row) + " |" for row in rows]
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("tags", nargs="+")
    ap.add_argument("--results-dir", default=os.path.join(HERE, "results"))
    ap.add_argument("--out", help="write markdown here instead of stdout")
    ap.add_argument("--cactus", help="write cactus-plot data CSV here")
    ap.add_argument("--top", type=int, default=10, help="rows in speedup/regression tables")
    args = ap.parse_args()

    tags = args.tags
    data = {t: load(args.results_dir, t) for t in tags}
    common = set.intersection(*(set(data[t][0]) for t in tags))
    union = set.union(*(set(data[t][0]) for t in tags))
    insts = sorted(common)
    timeouts = {t: float(data[t][1].get("timeout", 0)) or max(
        [wall(r) for r in data[t][0].values()] or [0]) for t in tags}
    R = lambda t, i: data[t][0][i]
    ok = lambda t, i: R(t, i)["result"] in SOLVED
    out = ["# Benchmark comparison: " + " vs ".join(tags), ""]

    # ---- blocking problems --------------------------------------------------
    problems = []
    for i in insts:
        verdicts = {t: R(t, i)["result"] for t in tags if ok(t, i)}
        if len(set(verdicts.values())) > 1:
            problems.append("RESULT DISCREPANCY on `%s`: %s" % (i, ", ".join(
                "%s=%s" % (t, v) for t, v in sorted(verdicts.items()))))
    for t in tags:
        for i, r in sorted(data[t][0].items()):
            if r["result"] in ("ERROR", "MISMATCH"):
                problems.append("SOLVER ERROR in `%s` on `%s`: %s (exit %s)" % (t, i, r["result"], r["exit"]))
            if r["proof_status"] not in ("", "n/a", "ok"):
                problems.append("PROOF PROBLEM in `%s` on `%s`: %s" % (t, i, r["proof_status"]))
    if problems:
        out += ["## !!! BLOCKING PROBLEMS (%d) !!!" % len(problems), ""]
        out += ["- **%s**" % p for p in problems] + [""]
    else:
        out += ["No result discrepancies, solver errors or proof problems.", ""]

    out.append("%d common instances compared (%d in the union%s)." % (
        len(insts), len(union), "; others are missing from some run" if len(union) > len(insts) else ""))
    if len(set(timeouts.values())) > 1:
        out.append("**Warning:** timeouts differ between runs: %s" % timeouts)
    out.append("")

    # ---- summary ----------------------------------------------------------------
    out += ["## Summary", ""]
    rows = []
    for t in tags:
        sat = sum(R(t, i)["result"] == "SAT" for i in insts)
        unsat = sum(R(t, i)["result"] == "UNSAT" for i in insts)
        to = timeouts[t]
        par2 = sum(wall(R(t, i)) if ok(t, i) else 2 * to for i in insts) / max(1, len(insts))
        solved_t = sum(wall(R(t, i)) for i in insts if ok(t, i))
        cpu_t = sum(float(R(t, i)["cpu"]) for i in insts if ok(t, i))
        mem = max([float(R(t, i)["rss_mb"]) for i in insts] or [0])
        rows.append([t, sat, unsat, sat + unsat, len(insts), "%.1f" % par2,
                     "%.0f" % solved_t, "%.0f" % cpu_t, "%.0f" % mem])
    out += table(["run", "SAT", "UNSAT", "solved", "total", "PAR2", "wall sum (solved) s",
                  "cpu sum (solved) s", "max RSS MB"], rows) + [""]
    meta_rows = [[t, data[t][1].get("solver_git", "?"), "`%s`" % data[t][1].get("args", ""),
                  data[t][1].get("timeout", "?"), data[t][1].get("date", "?")] for t in tags]
    out += table(["run", "git", "args", "timeout", "date"], meta_rows) + [""]

    # ---- uniquely solved ------------------------------------------------------
    if len(tags) > 1:
        out += ["## Uniquely solved", ""]
        any_unique = False
        for t in tags:
            u = [i for i in insts if ok(t, i) and not any(ok(s, i) for s in tags if s != t)]
            if u:
                any_unique = True
                out.append("- **%s** only (%d): %s" % (t, len(u), ", ".join(
                    "`%s` (%.1fs)" % (i, wall(R(t, i))) for i in u[:50]) + (" ..." if len(u) > 50 else "")))
        out += ["" if any_unique else "- none", ""]

    # ---- per family -------------------------------------------------------------
    out += ["## Per family (solved / total)", ""]
    fams = sorted({R(tags[0], i)["family"] for i in insts})
    rows = []
    for fam in fams:
        fi = [i for i in insts if R(tags[0], i)["family"] == fam]
        rows.append([fam, len(fi)] + ["%d" % sum(ok(t, i) for i in fi) for t in tags] +
                    ["%.1f" % (sum(wall(R(t, i)) if ok(t, i) else 2 * timeouts[t] for i in fi) / len(fi))
                     for t in tags])
    out += table(["family", "n"] + tags + ["PAR2 " + t for t in tags], rows) + [""]

    # ---- speedups / regressions ---------------------------------------------------
    ref = tags[0]
    for t in tags[1:]:
        both = [i for i in insts if ok(ref, i) and ok(t, i)]
        ratio = lambda i: max(wall(R(ref, i)), MIN_TIME) / max(wall(R(t, i)), MIN_TIME)
        both.sort(key=ratio, reverse=True)
        fmt = lambda i: [i, R(ref, i)["result"], "%.2f" % wall(R(ref, i)), "%.2f" % wall(R(t, i)),
                         "%.2fx" % ratio(i)]
        hdr = ["instance", "result", ref + " s", t + " s", "speedup"]
        out += ["## %s relative to %s (%d instances solved by both)" % (t, ref, len(both)), ""]
        if both:
            geo = 1.0
            for i in both:
                geo *= ratio(i) ** (1.0 / len(both))
            out += ["Geometric-mean speedup (times clamped at %.1fs): **%.2fx**." % (MIN_TIME, geo), ""]
            out += ["Top %d speedups:" % args.top, ""] + table(hdr, [fmt(i) for i in both[:args.top]]) + [""]
            out += ["Top %d regressions:" % args.top, ""] + table(
                hdr, [fmt(i) for i in reversed(both[-args.top:])]) + [""]

    # ---- proof statistics -----------------------------------------------------------
    if any(R(t, i)["proof_status"] not in ("", "n/a") for t in tags for i in insts):
        out += ["## Proof checking (Lean qlrup-check)", ""]
        rows = []
        for t in tags:
            rs = [R(t, i) for i in insts if R(t, i)["proof_status"] not in ("", "n/a")]
            if not rs:
                continue
            counts = {}
            for r in rs:
                counts[r["proof_status"]] = counts.get(r["proof_status"], 0) + 1
            chk = [float(r["proof_check_sec"]) for r in rs if r["proof_check_sec"]]
            byt = [int(r["proof_bytes"]) for r in rs if r["proof_bytes"]]
            rows.append([t, len(rs), counts.get("ok", 0),
                         ", ".join("%s: %d" % kv for kv in sorted(counts.items()) if kv[0] != "ok") or "-",
                         "%.1f" % sum(chk), "%.1f" % max(chk or [0]),
                         "%.1f" % (sum(byt) / 2**20), "%.1f" % (max(byt or [0]) / 2**20)])
        out += table(["run", "checked", "verified", "other statuses", "check s (sum)",
                      "check s (max)", "proof MB (sum)", "proof MB (max)"], rows) + [""]

    text = "\n".join(out) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)

    # ---- cactus data ---------------------------------------------------------------
    if args.cactus:
        times = {t: sorted(wall(R(t, i)) for i in insts if ok(t, i)) for t in tags}
        n = max(len(v) for v in times.values())
        with open(args.cactus, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["solved"] + tags)
            for k in range(n):
                w.writerow([k + 1] + ["%.3f" % times[t][k] if k < len(times[t]) else "" for t in tags])
    sys.exit(2 if problems else 0)


if __name__ == "__main__":
    main()
