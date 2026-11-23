#!/usr/bin/env python3
"""Table of a bench/l3.sh output file.

    l3_table.py OUT

OUT has one line "ROUND ARM INSTANCE USER SYS EXIT" per process.  The table has one row per
instance: the mean user seconds of the first arm and, for every other arm, its mean and the
ratio to the first arm; the last row is the geometric mean of the ratios.  An instance is left
out when any run of any arm ended with an exit status other than 10 or 20: a timeout makes
the time of a run meaningless, it only served as a neighbour.
"""
import collections
import math
import sys

from benchlib import table

VERDICT_EXITS = {"10", "20"}


def parse(lines):
    """(arms in order of appearance, {(instance, arm): [user seconds]}, instances with a bad exit)."""
    arms, times, bad = [], collections.defaultdict(list), set()
    for line in lines:
        fields = line.split()
        if len(fields) != 6:
            continue
        _, arm, instance, user, _, code = fields
        if arm not in arms:
            arms.append(arm)
        times[(instance, arm)].append(float(user))
        if code not in VERDICT_EXITS:
            bad.add(instance)
    return arms, times, bad


def build_table(arms, times, bad):
    """Markdown lines of the table; instances in `bad` and instances missing in an arm are left out."""
    first, others = arms[0], arms[1:]
    mean = lambda instance, arm: sum(times[(instance, arm)]) / len(times[(instance, arm)])
    instances = sorted({i for i, _ in times} - bad)
    instances = [i for i in instances if all((i, a) in times for a in arms)]
    logs = {a: [] for a in others}
    rows = []
    for i in instances:
        base = mean(i, first)
        row = [i, "%.2f" % base]
        for a in others:
            ratio = mean(i, a) / base
            logs[a].append(math.log(ratio))
            row += ["%.2f" % mean(i, a), "%.3f" % ratio]
        rows.append(row)
    last = ["**geometric mean**", ""]
    for a in others:
        last += ["n=%d" % len(logs[a]),
                 "**%.3f**" % math.exp(sum(logs[a]) / len(logs[a])) if logs[a] else "-"]
    header = ["instance", first] + [c for a in others for c in (a, "%s / %s" % (a, first))]
    return table(header, rows + [last])


def main():
    if len(sys.argv) != 2:
        sys.exit("usage: l3_table.py OUT")
    with open(sys.argv[1]) as f:
        arms, times, bad = parse(f)
    if not arms:
        sys.exit("l3_table.py: no runs in %s" % sys.argv[1])
    print("\n".join(build_table(arms, times, bad)))


if __name__ == "__main__":
    main()
