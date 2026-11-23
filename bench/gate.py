#!/usr/bin/env python3
"""Evaluate the identical-search gate of a milestone round, line by line.

    gate.py [--results-dir DIR] [--pooled-limit 1.04] [--family-limit 1.10] [--family-min 3]
            [--out FILE] [--force] --pair NAME:A_TAGS:B_TAGS [--pair ...] [--report NAME:A_TAGS:B_TAGS ...]
            [--confirm NAME:A_TAGS:B_TAGS ...] [--self NAME:TAGS_1:TAGS_2 ...]

A is the reference (baseline or the previous accepted state), B the new binary; the tags of a
set are comma separated, one per seed, and are paired by seed exactly as `compare.py --paired`
does (same loading, same comparability check, exit 3 unless --force).  Per configuration the
output has the pooled geometric mean of the CPU-time ratios B / A over the identical searches
(paired.IdenticalSearches), the complete per-family table, and the instances that hit the
memory limit or ended in ERROR / MISMATCH.  A `--pair` configuration is gated: a pooled value
above the pooled limit or a family of at least --family-min instances above the family limit
is FAIL.  `--confirm NAME:A_TAGS:B_TAGS` is a second, back-to-back pair of the configuration NAME of
a `--pair`: a family that FAILs in the pair and is within the limit in the confirm pair is
`NOISE (first X, repeat Y)` and does not fail the gate, one above the limit again is
`FAIL (repeated)` (review M1-r3, follow-up 1; the pooled line is never excused).  `--self
NAME:TAGS_1:TAGS_2` prints, for two runs of the same binary, the family ratios as information:
it shows how far from 1 pure noise goes on this machine.  A `--report` configuration is evaluated the same way, but its lines read REPORT
(above, to be explained) and do not change the exit status.  Exit status: 0 PASS, 1 FAIL.

The default pooled limit 1.04 is the ROADMAP's "at most about 1.03" with the 1-2% resolution
of three seeds (review M1-r2, section 5).  The output is pasted verbatim into the report.
"""
import argparse
import sys

from benchlib import DEFAULT_RESULTS, table
import paired

MEMORY_RESULT = "MEMOUT"   # the result string run.py's classify() writes for a memory-limit hit
ERROR_RESULTS = ("ERROR", "MISMATCH")


def parse_config(text):
    """NAME:A_TAGS:B_TAGS -> (name, [a tags], [b tags])."""
    parts = text.split(":")
    if len(parts) != 3 or not all(parts):
        sys.exit("gate.py: %r is not NAME:A_TAGS:B_TAGS" % text)
    return parts[0], parts[1].split(","), parts[2].split(",")


def runs_with(runs, result_in):
    """Instance -> number of runs of the arm whose result is in result_in."""
    counts = {}
    for run in runs:
        for i, row in run.rows.items():
            if row["result"] in result_in:
                counts[i] = counts.get(i, 0) + 1
    return counts


def count_line(label, runs_a, runs_b, results):
    """Text listing the instances with a result in `results`, with runs per arm."""
    a, b = runs_with(runs_a, results), runs_with(runs_b, results)
    names = sorted(set(a) | set(b))
    if not names:
        return "%s: none" % label
    return "%s: %s" % (label, ", ".join("`%s` (A %d/%d runs, B %d/%d runs)" % (
        i, a.get(i, 0), len(runs_a), b.get(i, 0), len(runs_b)) for i in names))


def family_means(ident, family_min):
    """Family -> geometric mean of the identical searches, for the families with n >= family_min."""
    return {fam: paired.geomean(ratios) for fam, ratios in ident.family_ratios().items()
            if len(ratios) >= family_min}


def family_verdict(g, limit, bad, confirm, fam):
    """Verdict of a gated family above/below the limit; `confirm` maps family -> mean of the repeat."""
    if g <= limit:
        return "PASS"
    if confirm is None:
        return bad
    repeat = confirm.get(fam)
    if repeat is None:
        return bad  # nothing to confirm with: the failure stands
    if repeat <= limit:
        return "NOISE (first %.3f, repeat %.3f)" % (g, repeat)
    return bad + " (repeated)"


def evaluate(name, runs_a, runs_b, args, gated, confirm=None):
    """Markdown lines of one configuration and the list of its FAIL / REPORT / NOISE lines."""
    ident = paired.IdenticalSearches(runs_a, runs_b)
    bad = "FAIL" if gated else "REPORT (above, to be explained)"
    lines, failures = ["## %s" % name, ""], []

    pooled = ident.pooled_ratios()
    if pooled:
        value = paired.geomean(pooled)
        ok = value <= args.pooled_limit
        shown = "%.3f" % value
    else:  # nothing to judge: that is not a pass
        ok, shown = False, "-"
    verdict = "PASS" if ok else bad
    per_seed = ", ".join("seed %s: %s (n=%d)" % (row[0], row[2], row[1]) for row in ident.seed_rows()[:-1])
    lines += ["%s: pooled identical searches: n=%d, geometric mean new/reference = %s, limit %.2f: %s" % (
        name, len(pooled), shown, args.pooled_limit, verdict), "", "Per seed: %s." % per_seed, ""]
    if not ok:
        failures.append([name, "pooled", len(pooled), shown, verdict])

    rows = []
    for fam, ratios in ident.family_ratios().items():
        g = paired.geomean(ratios)
        if len(ratios) < args.family_min:
            verdict = "n < %d" % args.family_min
        else:
            verdict = family_verdict(g, args.family_limit, bad, confirm, fam)
            if verdict != "PASS":
                failures.append([name + " " + fam, "family", len(ratios), "%.3f" % g, verdict])
        rows.append([fam, len(ratios), "%.3f" % g, verdict])
    lines += ["Per family (identical searches pooled over the seeds; gated if n >= %d, limit %.2f):" % (
        args.family_min, args.family_limit), ""]
    lines += (table(["family", "n", "geometric mean", "verdict"], rows) if rows else
              ["no instance with an identical search"]) + [""]

    lines += ["- " + count_line("memory-limit hits (%s)" % MEMORY_RESULT, runs_a, runs_b, (MEMORY_RESULT,)),
              "- " + count_line("ERROR/MISMATCH rows", runs_a, runs_b, ERROR_RESULTS), ""]
    return lines, failures


def self_table(name, runs_1, runs_2, args):
    """Informational family ratios of two runs of the same binary."""
    ident = paired.IdenticalSearches(runs_1, runs_2)
    pooled = ident.pooled_ratios()
    rows = [[fam, len(ratios), "%.3f" % paired.geomean(ratios)] for fam, ratios in ident.family_ratios().items()]
    return ["## %s (same binary twice, information only)" % name, "",
            "pooled identical searches: n=%d, geometric mean run 2 / run 1 = %s" % (
                len(pooled), "%.3f" % paired.geomean(pooled) if pooled else "-"), ""] + (
        table(["family", "n", "geometric mean"], rows) if rows else ["no instance with an identical search"]) + [""]


def load(args, text, out):
    name, tags_a, tags_b = parse_config(text)
    runs_a, runs_b, reasons = paired.load_pair(args.results_dir, tags_a, tags_b, args.force, "gate.py")
    if reasons:
        out += ["**NOT COMPARABLE (%s, --force):** %s" % (name, "; ".join(reasons)), ""]
    return name, runs_a, runs_b


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--pooled-limit", type=float, default=1.04)
    ap.add_argument("--family-limit", type=float, default=paired.FAMILY_LIMIT)
    ap.add_argument("--family-min", type=int, default=paired.FAMILY_MIN_N)
    ap.add_argument("--pair", action="append", default=[], help="gated configuration NAME:A_TAGS:B_TAGS")
    ap.add_argument("--report", action="append", default=[], help="reported configuration NAME:A_TAGS:B_TAGS")
    ap.add_argument("--confirm", action="append", default=[],
                    help="second back-to-back pair NAME:A_TAGS:B_TAGS of the --pair NAME")
    ap.add_argument("--self", action="append", default=[], dest="same",
                    help="two runs of one binary NAME:TAGS_1:TAGS_2, family ratios as information")
    ap.add_argument("--force", action="store_true", help="evaluate even if limits or seeds differ")
    ap.add_argument("--out", help="write markdown here instead of stdout")
    args = ap.parse_args()
    if not args.pair and not args.report:
        ap.error("give at least one --pair or --report")

    pair_names = [parse_config(text)[0] for text in args.pair]
    for text in args.confirm:
        if parse_config(text)[0] not in pair_names:
            ap.error("--confirm %s: no --pair of that name" % text.split(":")[0])

    out, failures, unconfirmed = ["# Gate: identical searches, new / reference", ""], [], set()
    confirms = {}
    for text in args.confirm:  # the repeat of a configuration is evaluated before its pair
        name, runs_a, runs_b = load(args, text, out)
        lines, _ = evaluate(name + " (confirm)", runs_a, runs_b, args, False)
        out += lines
        confirms[name] = family_means(paired.IdenticalSearches(runs_a, runs_b), args.family_min)
    for gated, texts in ((True, args.pair), (False, args.report)):
        for text in texts:
            name, runs_a, runs_b = load(args, text, out)
            lines, bad = evaluate(name, runs_a, runs_b, args, gated, confirms.get(name))
            out += lines
            failures += bad
            if any(row[4].startswith("FAIL") for row in bad) and name not in confirms:
                unconfirmed.add(name)
    for text in args.same:
        name, runs_1, runs_2 = load(args, text, out)
        out += self_table(name, runs_1, runs_2, args)
    out += ["## Summary", ""]
    out += (table(["configuration", "kind", "n", "geometric mean", "verdict"], failures)
            if failures else ["no FAIL, NOISE and REPORT lines"]) + [""]
    fails = sum(row[4].startswith("FAIL") for row in failures)
    out.append("GATE: PASS" if not fails else "GATE: FAIL (%d lines)" % fails)
    if unconfirmed:
        out += ["", "Hint: rerun the configuration back to back and pass --confirm NAME:BASE_TAGS:NEW_TAGS "
                "(configurations: %s); a family that does not fail again is noise." % ", ".join(sorted(unconfirmed))]
    text = "\n".join(out) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
