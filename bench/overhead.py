#!/usr/bin/env python3
"""Proof overhead (ROADMAP 0.3): the same run with and without proof logging.

    overhead.py TAG_WITHOUT TAG_WITH [--out FILE] [--results-dir DIR]

TAG_WITH was run with "{proof}" in --args (and --trim-size for the trimmed
size).  On the instances solved by both: total and geometric-mean wall time
ratio (instances above 1 s), proof bytes in total and per conflict, and the
size after qlrup-trim.  Output is markdown.
"""
import argparse
import sys

from benchlib import DEFAULT_RESULTS, Run, table
from fidelity import geometric_mean


def report(without, with_proof):
    both = [i for i in sorted(without.rows) if i in with_proof.rows and without.solved(i) and with_proof.solved(i)]
    long_runs = [i for i in both if min(without.wall(i), with_proof.wall(i)) > 1.0]
    total_off = sum(without.wall(i) for i in both)
    total_on = sum(with_proof.wall(i) for i in both)
    sizes = {i: int(with_proof.rows[i]["proof_bytes"] or 0) for i in both}
    trimmed = {i: int(with_proof.rows[i]["proof_trim_bytes"]) for i in both if with_proof.rows[i]["proof_trim_bytes"]}
    conflicts = sum(with_proof.stats.get(i, {}).get("conflicts", 0) for i in both)
    rows = [["instances solved by both", len(both)],
            ["wall time without proof / with proof (s)", "%.1f / %.1f" % (total_off, total_on)],
            ["total time ratio (with / without)", "%.3f" % (total_on / total_off if total_off else float("nan"))],
            ["geometric-mean time ratio, %d instances above 1 s" % len(long_runs),
             "%.3f" % geometric_mean([with_proof.wall(i) / without.wall(i) for i in long_runs])],
            ["proof bytes, total (MB)", "%.1f" % (sum(sizes.values()) / 2 ** 20)],
            ["proof bytes per conflict", "%.1f" % (sum(sizes.values()) / conflicts) if conflicts else "n/a"]]
    if trimmed:
        rows += [["size after qlrup-trim, %d instances (MB), as percent of untrimmed" % len(trimmed),
                  "%.1f (%.1f%%)" % (sum(trimmed.values()) / 2 ** 20,
                                     100.0 * sum(trimmed.values()) / max(1, sum(sizes[i] for i in trimmed)))]]
    return "\n".join(["# Proof overhead: %s (without) vs %s (with)" % (without.tag, with_proof.tag), ""]
                     + table(["quantity", "value"], rows)) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("without")
    ap.add_argument("with_proof")
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--out")
    args = ap.parse_args()
    text = report(Run(args.results_dir, args.without), Run(args.results_dir, args.with_proof))
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
