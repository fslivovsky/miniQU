#!/usr/bin/env python3
"""Summarise the M2-T11 runs: python3 analyze.py runs.csv  (prints the tables of report.md)

Pure counting: time-outs, PAR2, medians, paired discordant counts with an
exact two-sided sign test, and the attribution criterion of the task spec."""
import csv, statistics, sys
from collections import defaultdict
from math import comb

LIMIT, PENALTY = 60.0, 120.0
NAMES = {1: "M1 binary", 2: "baseline", 3: "M2 default", 4: "M2 EQUIV string",
         5: "M2 --no-reusetrail", 6: "M2 --no-rootsimp", 7: "M2 --no-tiers --no-glueupdate",
         8: "M2 M1 trigger+target (tiers kept)", 9: "M2 M1 reduce policy",
         10: "M2 --no-glueupdate", 11: "M2 --no-reusetrail --no-rootsimp"}
ARMS = sorted(NAMES)


def load(path):
    runs = {}
    for r in csv.DictReader(open(path)):
        key = (int(r["arm"]), r["config"], r["instance"], int(r["seed"]))
        runs[key] = (int(r["exit"]), float(r["wall"]))
    return runs


def timed_out(e):
    return e == 124


def sign_p(b, c):
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    return min(1.0, 2 * sum(comb(n, i) for i in range(k + 1)) / 2 ** n)


def main(path):
    runs = load(path)
    configs = sorted({k[1] for k in runs}, key=lambda c: c != "dl")
    insts = sorted({k[2] for k in runs})
    seeds = sorted({k[3] for k in runs})
    out = []
    bad = [(k, v) for k, v in runs.items() if v[0] not in (10, 20, 124)]
    out.append("## Errors\n")
    out.append("none" if not bad else "\n".join(f"- arm {k[0]} {k[1]} {k[2]} seed {k[3]}: exit {v[0]}" for k, v in bad))
    out.append("\n## Verdict agreement\n")
    seen = defaultdict(set)
    for k, v in runs.items():
        if v[0] in (10, 20):
            seen[(k[2], k[3])].add(v[0])
    dis = sorted(k for k, v in seen.items() if len(v) > 1)
    out.append("no (instance, seed) has two different verdicts across arms and configurations"
               if not dis else "DISAGREEMENT: " + ", ".join(map(str, dis)))
    for cfg in configs:
        sel = lambda a, ii=insts: [runs[(a, cfg, i, s)] for i in ii for s in seeds if (a, cfg, i, s) in runs]
        out.append(f"\n## Configuration `{cfg}`: summary per arm\n")
        out.append("| arm | binary / options | time-outs | solved | PAR2 (s) | median wall of solved (s) |\n|---:|---|---:|---:|---:|---:|")
        for a in ARMS:
            rs = sel(a)
            to = sum(timed_out(e) for e, _ in rs)
            sv = [w for e, w in rs if not timed_out(e)]
            par2 = sum(w if not timed_out(e) else PENALTY for e, w in rs)
            out.append(f"| {a} | {NAMES[a]} | {to} of {len(rs)} | {len(sv)} | {par2:.0f} | {statistics.median(sv):.2f} |")
        out.append(f"\n### `{cfg}`: time-outs of {len(seeds)} per instance and arm\n")
        out.append("| instance | " + " | ".join(str(a) for a in ARMS) + " |\n|---|" + "---:|" * len(ARMS))
        for i in insts:
            out.append(f"| {i[:-5]} | " + " | ".join(
                str(sum(timed_out(e) for e, _ in sel(a, [i]))) for a in ARMS) + " |")
    for cfg in configs:
        for label, ii in (("all instances", insts), ("the 8 pass instances", [i for i in insts if "pass" in i])):
            pairs = [(i, s) for i in ii for s in seeds]
            out.append(f"\n## Paired comparison, `{cfg}`, {label} ({len(pairs)} pairs)\n")
            out.append("Only-one-side time-outs: `arm` = pairs where only the arm timed out, `ref` = only the reference did. "
                       "p = exact two-sided sign test on these discordant pairs.\n")
            out.append("| arm | vs 1 (M1): only arm / only ref | p | vs 3 (M2 default): only arm / only ref | p |\n|---|---|---:|---|---:|")
            for a in ARMS:
                cells = []
                for ref in (1, 3):
                    if a == ref:
                        cells += ["-", "-"]
                        continue
                    b = sum(timed_out(runs[(a, cfg, i, s)][0]) and not timed_out(runs[(ref, cfg, i, s)][0]) for i, s in pairs)
                    c = sum(not timed_out(runs[(a, cfg, i, s)][0]) and timed_out(runs[(ref, cfg, i, s)][0]) for i, s in pairs)
                    cells += [f"{b} / {c}", f"{sign_p(b, c):.4f}"]
                out.append(f"| {a} {NAMES[a]} | " + " | ".join(cells) + " |")
    # attribution under -dl over all instances
    cfg = "dl"
    pairs = [(i, s) for i in insts for s in seeds]
    to = lambda a: sum(timed_out(runs[(a, cfg, i, s)][0]) for i, s in pairs)
    def disc(a, ref):
        b = sum(timed_out(runs[(a, cfg, i, s)][0]) and not timed_out(runs[(ref, cfg, i, s)][0]) for i, s in pairs)
        c = sum(not timed_out(runs[(a, cfg, i, s)][0]) and timed_out(runs[(ref, cfg, i, s)][0]) for i, s in pairs)
        return b, c, sign_p(b, c)
    b, c, p = disc(3, 1)
    excess = to(3) - to(1)
    out.append("\n## Attribution (`-dl`, all instances)\n")
    out.append(f"Arm 3 time-outs {to(3)}, arm 1 time-outs {to(1)}, excess {excess}; arm 3 vs arm 1 discordant "
               f"{b} / {c}, p = {p:.4f}.\n")
    worse = b > c and p < 0.05
    if not worse:
        out.append("**Outcome: no regression shown at 20 seeds** (arm 3 is not worse than arm 1 with p < 0.05).")
    else:
        out.append("| arm | time-outs | removed of excess | removes >= half | only arm / only arm 3 | p vs 3 | attributed |\n|---|---:|---:|---|---|---:|---|")
        hits = []
        for a in (5, 6, 7, 8, 10, 9, 11, 4):
            removed = to(3) - to(a)
            bb, cc, pp = disc(a, 3)
            ok = removed >= excess / 2 and pp < 0.05 and cc > bb
            if ok:
                hits.append(a)
            out.append(f"| {a} {NAMES[a]} | {to(a)} | {removed} | {'yes' if removed >= excess / 2 else 'no'} | {bb} / {cc} | {pp:.4f} | {'yes' if ok else 'no'} |")
        single = [a for a in hits if a in (5, 6, 7, 8, 10)]
        if single:
            out.append(f"\n**Outcome: attributed to the switch of arm(s) {single}.**")
        elif hits:
            out.append(f"\n**Outcome: loss is real, no single switch meets the criterion; combination arm(s) {hits} do.**")
        else:
            out.append("\n**Outcome: loss is real, but neither a single switch nor the combinations (arms 9, 11, 4) meet the criterion.**")
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1])
