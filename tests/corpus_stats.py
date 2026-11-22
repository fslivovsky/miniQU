#!/usr/bin/env python3
"""Measure how hard the instances of tests/corpus.py are for a solver.

Usage: corpus_stats.py [--tier search] [--first 1] [--last 400] [--solver BIN]
                       [--check] [--jobs 16] [--timeout 20] [--csv FILE]

For every seed, the instance is generated and solved with the default options
and with -dl (statistics on, "conflicts :" line parsed). Prints, per parameter
set and configuration, a histogram of conflict counts, the fraction in
[100, 10000), and the maximal solve time. With --check the default run is
repeated with a binary proof that the Lean checker must accept within 120 s.
Run it under taskset -c 0-63; scratch files are deleted after use.
"""
import argparse
import csv
import os
import re
import subprocess
import sys
import tempfile
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
BUCKETS = [(0, 9), (10, 99), (100, 999), (1000, 9999), (10000, None)]
LABELS = ['0-9', '10-99', '100-999', '1000-9999', '>=10000']
CONFIGS = [('default', []), ('dl', ['-dl'])]


def bucket(conflicts):
    for i, (lo, hi) in enumerate(BUCKETS):
        if conflicts >= lo and (hi is None or conflicts <= hi):
            return i


def solve(solver, path, options, timeout, proof=None):
    cmd = [solver, '-verb=1'] + options + (['-proof=' + proof, '-proof-binary'] if proof else []) + [path]
    start = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, timeout, 'TIMEOUT'
    m = re.search(r'^(?:c stat conflicts |conflicts\s*:\s*)(\d+)', p.stdout, re.M)  # new solver, baseline
    verdict = {10: 'SAT', 20: 'UNSAT'}.get(p.returncode, 'ERROR%d' % p.returncode)
    return (int(m.group(1)) if m else None), time.time() - start, verdict


def measure(args, seed):
    with tempfile.TemporaryDirectory(dir=args.work) as tmp:
        path = os.path.join(tmp, 'f.qcir')
        gen = subprocess.run([sys.executable, os.path.join(HERE, 'corpus.py'), '--tier', args.tier,
                              '--seed', str(seed), '--out', path], capture_output=True, text=True, check=True)
        name = re.search(r'set=(\S+)', gen.stderr).group(1)
        row = {'seed': seed, 'set': name}
        for label, options in CONFIGS:
            row[label + '_conflicts'], row[label + '_sec'], row[label + '_verdict'] = \
                solve(args.solver, path, options, args.timeout)
        if args.check:
            proof = os.path.join(tmp, 'f.proof')
            _, _, verdict = solve(args.solver, path, [], args.timeout, proof)
            start = time.time()
            try:
                out = subprocess.run([args.checker, path, proof], capture_output=True, text=True,
                                     timeout=args.check_timeout).stdout
                want = 'VERIFIED TRUE' if verdict == 'SAT' else 'VERIFIED FALSE'
                row['proof'] = 'ok' if re.search(r'^s ' + want, out, re.M) else 'REJECTED'
            except subprocess.TimeoutExpired:
                row['proof'] = 'timeout'
            row['check_sec'] = time.time() - start
        return row


def report(rows, check):
    sets = sorted({r['set'] for r in rows})
    for label, _ in CONFIGS:
        print('\n== %s: conflicts of the solver (instances per bucket) ==' % label)
        print('%-12s' % 'set' + ''.join('%11s' % l for l in LABELS) + '%9s%9s%10s' % ('timeout', 'in range', 'max sec'))
        for name in sets + ['all']:
            sub = [r for r in rows if name in ('all', r['set'])]
            hist = [0] * len(BUCKETS)
            for r in sub:
                if r[label + '_conflicts'] is not None:
                    hist[bucket(r[label + '_conflicts'])] += 1
            timeouts = sum(r[label + '_verdict'] == 'TIMEOUT' for r in sub)
            print('%-12s' % name + ''.join('%11d' % h for h in hist) + '%9d%8.0f%%%10.1f' % (
                timeouts, 100.0 * (hist[2] + hist[3]) / len(sub), max(r[label + '_sec'] for r in sub)))
    if check:
        print('\n== proofs (default options, Lean checker) ==')
        for name in sets + ['all']:
            sub = [r for r in rows if name in ('all', r['set'])]
            counts = defaultdict(int)
            for r in sub:
                counts[r['proof']] += 1
            print('%-12s ' % name + ' '.join('%s %d' % kv for kv in sorted(counts.items())) +
                  '  accepted %.0f%%  max check %.1f s' % (100.0 * counts['ok'] / len(sub),
                                                         max(r['check_sec'] for r in sub)))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--tier', default='search')
    parser.add_argument('--first', type=int, default=1)
    parser.add_argument('--last', type=int, default=400)
    parser.add_argument('--solver', default='/home/ec2-user/miniqu-work/baseline/miniQU')
    parser.add_argument('--checker', default='/home/ec2-user/qu-check/.lake/build/bin/qlrup-check')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--check-timeout', type=int, default=120)
    parser.add_argument('--jobs', type=int, default=16)
    parser.add_argument('--timeout', type=int, default=20)
    parser.add_argument('--work', default='/home/ec2-user/miniqu-work/regress')
    parser.add_argument('--csv')
    args = parser.parse_args()
    os.makedirs(args.work, exist_ok=True)
    with ThreadPoolExecutor(args.jobs) as pool:
        rows = list(pool.map(lambda s: measure(args, s), range(args.first, args.last + 1)))
    if args.csv:
        with open(args.csv, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    report(rows, args.check)


if __name__ == '__main__':
    main()
