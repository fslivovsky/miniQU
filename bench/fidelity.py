#!/usr/bin/env python3
"""Port-fidelity report (ROADMAP M1.9): engine speed against search behaviour.

    fidelity.py TAG_BASELINE TAG_NEW [--out FILE] [--min-time SECONDS] [--results-dir DIR]

Search is not trace-identical between the old and the new solver, so "not
worse" mixes engine speed with heuristic drift.  For every instance solved by
both, from the counters run.py stored in stats.csv: propagations and
conflicts per CPU second (new / baseline) and the ratio of conflict counts
(new / baseline).  A faithful port has speed ratios at or above 1 and conflict
ratios scattered around 1.  Rates are taken over the whole CPU time, parsing
included, and only for instances both solvers need at least --min-time seconds
for (default 1), since the parser is faster in the new solver and would
dominate the rate of short runs.  Output is markdown.
"""
import argparse
import math
import sys

from benchlib import DEFAULT_RESULTS, Run

HISTOGRAM_RANGE = 4  # bins of log2(ratio): below -4, -4..-3, ..., 3..4, above 4


def geometric_mean(values):
    return math.exp(sum(math.log(v) for v in values) / len(values)) if values else float("nan")


def histogram(ratios):
    bins = {}
    for r in ratios:
        k = max(-HISTOGRAM_RANGE, min(HISTOGRAM_RANGE, math.floor(math.log2(r))))
        bins[k] = bins.get(k, 0) + 1
    out = ["| log2 of the conflict ratio | ratio | instances | |", "|---|---|---:|---|"]
    for k in range(-HISTOGRAM_RANGE, HISTOGRAM_RANGE + 1):
        label = ("(-inf, %d)" % (-HISTOGRAM_RANGE + 1)) if k == -HISTOGRAM_RANGE else \
            ("[%d, inf)" % HISTOGRAM_RANGE if k == HISTOGRAM_RANGE else "[%d, %d)" % (k, k + 1))
        span = ("< %g" % 2.0 ** (k + 1)) if k == -HISTOGRAM_RANGE else \
            (">= %g" % 2.0 ** k if k == HISTOGRAM_RANGE else "%g - %g" % (2.0 ** k, 2.0 ** (k + 1)))
        out.append("| %s | %s | %d | %s |" % (label, span, bins.get(k, 0), "#" * bins.get(k, 0)))
    return out


def report(base, new, min_time):
    both = [i for i in sorted(base.rows) if i in new.rows and base.solved(i) and new.solved(i)]
    counted = [i for i in both if i in base.stats and i in new.stats]
    out = ["# Port fidelity: %s (baseline) vs %s (new)" % (base.tag, new.tag), "",
           "Instances solved by both: %d; with counters in both runs: %d." % (len(both), len(counted)), ""]
    flips = [i for i in both if base.rows[i]["result"] != new.rows[i]["result"]]
    if flips:
        out += ["**VERDICT DISAGREEMENT on:** " + ", ".join("`%s`" % i for i in flips), ""]

    def rate(run, i, counter):
        cpu = float(run.rows[i]["cpu"])
        return run.stats[i].get(counter, 0) / cpu if cpu > 0 else 0.0

    timed = [i for i in counted if min(float(base.rows[i]["cpu"]), float(new.rows[i]["cpu"])) >= min_time]
    out += ["## Speed (instances with at least %g CPU s in both runs: %d)" % (min_time, len(timed)), ""]
    out += ["| counter per CPU second | geometric mean of new / baseline | min | max |", "|---|---:|---:|---:|"]
    for counter in ("propagations", "conflicts"):
        ratios = [rate(new, i, counter) / rate(base, i, counter) for i in timed
                  if rate(base, i, counter) > 0 and rate(new, i, counter) > 0]
        if ratios:
            out.append("| %s | %.3f | %.3f | %.3f |" % (counter, geometric_mean(ratios), min(ratios), max(ratios)))
    out.append("")

    usable = [i for i in counted if base.stats[i].get("conflicts", 0) > 0 and new.stats[i].get("conflicts", 0) > 0]
    ratios = {i: new.stats[i]["conflicts"] / base.stats[i]["conflicts"] for i in usable}
    out += ["## Conflict counts, new / baseline (%d instances with conflicts in both; %d without)" % (
        len(usable), len(counted) - len(usable)), ""]
    if usable:
        values = sorted(ratios.values())
        out += ["Geometric mean **%.3f**, median %.3f, min %.3f, max %.3f; above 2: %d; below 0.5: %d." % (
            geometric_mean(values), values[len(values) // 2], values[0], values[-1],
            sum(v > 2 for v in values), sum(v < 0.5 for v in values)), ""]
        out += histogram(values) + [""]
        extreme = sorted(usable, key=lambda i: -abs(math.log(ratios[i])))[:10]
        out += ["Largest deviations:", "", "| instance | baseline conflicts | new conflicts | ratio |", "|---|---:|---:|---:|"]
        out += ["| %s | %d | %d | %.2f |" % (i, base.stats[i]["conflicts"], new.stats[i]["conflicts"], ratios[i])
                for i in extreme] + [""]
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("baseline")
    ap.add_argument("new")
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--min-time", type=float, default=1.0)
    ap.add_argument("--out")
    args = ap.parse_args()
    text = report(Run(args.results_dir, args.baseline), Run(args.results_dir, args.new), args.min_time)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
