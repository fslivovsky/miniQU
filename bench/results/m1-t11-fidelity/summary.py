#!/usr/bin/env python3
"""summary.py BASELINE.csv NEW.csv...: per configuration, conflicts new /
baseline over the seeds both solved: geometric mean, min, max, identical
counts, and the timeouts of each side (CSV rows of run.sh)."""
import csv, math, sys
from collections import defaultdict

def load(path):
    d = {}
    for label, seed, config, ec, c in csv.reader(open(path)):
        d[(config, int(seed))] = int(c) if c else None
    return label, d

_, base = load(sys.argv[1])
print('| binary | config | both solved | geo. mean | min | max | identical | timeouts new / baseline |')
print('|---|---|---|---|---|---|---|---|')
for path in sys.argv[2:]:
    label, new = load(path)
    for config in ['default', '-dl', '-mode=1', '-mode=2']:
        keys = [k for k in base if k[0] == config]
        both = [k for k in keys if base[k] is not None and new.get(k) is not None]
        if not both:
            continue
        r = [max(new[k], 1) / max(base[k], 1) for k in both]
        g = math.exp(sum(map(math.log, r)) / len(r))
        same = sum(new[k] == base[k] for k in both)
        to_n = sum(new.get(k) is None for k in keys)
        to_b = sum(base[k] is None for k in keys)
        print(f'| {label} | {config} | {len(both)} | {g:.3f} | {min(r):.3g} | {max(r):.3g} | {same} | {to_n} / {to_b} |')
