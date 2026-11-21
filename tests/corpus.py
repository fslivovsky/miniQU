#!/usr/bin/env python3
"""Deterministic test-instance generator for tests/regress.sh.

Usage: corpus.py --tier tiny|search --seed N --out FILE.qcir
       corpus.py --list-sets

The seed selects a parameter set round-robin and, within the set, the
instance. The parameters used are written as a "# corpus:" comment on the
second line of the file and on stderr, so that a failure can be reproduced
from the log alone.

tiny    small enough for the brute-force evaluator tests/qcir_eval.py; the
        parameter sets are those of tests/fuzz.sh. They need 0-5 conflicts and
        test parsing, encoding and the first conflict only.
search  larger instances (families of qcir_gen.py, random circuits of
        qcir_fuzz.py) for which the baseline needs 10^2 to 10^4 conflicts, so
        that restarts, clause reduction and garbage collection all happen.
        Measured with tests/corpus_stats.py; the numbers are in
        doc/rewrite/STATUS.md.
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import qcir_fuzz  # noqa: E402
import qcir_gen  # noqa: E402

# A parameter set is (name, generator, arguments after the seed). The
# generator is "gen" (qcir_gen.py FAMILY SEED SIZE PARAM) or "fuzz"
# (qcir_fuzz.py SEED --vars --gates --blocks [--cnf]).
TINY = [
    ('fuzz-small', 'fuzz', (12, 30, 6, False)),
    ('fuzz-cnf', 'fuzz', (12, 30, 6, True)),
    ('fuzz-deep', 'fuzz', (16, 60, 8, False)),
    ('qcnf-5', 'gen', ('qcnf', 5, 5)),
    ('qcnf-6', 'gen', ('qcnf', 6, 6)),
    ('qcnf-7', 'gen', ('qcnf', 7, 7)),
    ('reach-6', 'gen', ('reach', 6, 8)),
    ('reach-7', 'gen', ('reach', 7, 12)),
    ('reach-8', 'gen', ('reach', 8, 16)),
    ('game-5', 'gen', ('game', 5, None)),
    ('synth-8', 'gen', ('synth', 8, None)),
]

# Measured on seeds 1..400 (STATUS.md). The families game and synth of
# qcir_gen.py and larger qcir_fuzz.py instances are not used: the baseline
# solves nearly all of them in under 10 conflicts, or has no useful spread.
SEARCH = [
    ('qcnf-sat', 'gen', ('qcnf', 24, 5.5)),
    ('qcnf-mixed', 'gen', ('qcnf', 23, 7)),
    ('qcnf-unsat', 'gen', ('qcnf', 24, 8)),
    ('reach-48', 'gen', ('reach', 48, 80)),
    ('reach-44', 'gen', ('reach', 44, 70)),
]

TIERS = {'tiny': TINY, 'search': SEARCH}


def generate(tier, seed):
    """Return (name, parameter description, QCIR text) for the given seed."""
    sets = TIERS[tier]
    name, kind, args = sets[(seed - 1) % len(sets)]
    if kind == 'fuzz':
        nvars, ngates, nblocks, cnf = args
        rng = random.Random(seed)
        problem = qcir_fuzz.generate(rng, nvars, ngates, nblocks, cnf)
        expected = qcir_fuzz.evaluate(*problem) if tier == 'tiny' else None
        text = qcir_fuzz.write(*problem, expected)
        params = 'qcir_fuzz.py %d --vars %d --gates %d --blocks %d%s' % (
            seed, nvars, ngates, nblocks, ' --cnf' if cnf else '')
    else:
        family, size, param = args
        text = qcir_gen.render(family, seed, size, param)
        params = 'qcir_gen.py %s %d%s%s' % (family, seed,
                                            '' if size is None else ' %d' % size,
                                            '' if param is None else ' %s' % param)
    return name, params, text


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--tier', choices=sorted(TIERS))
    parser.add_argument('--seed', type=int)
    parser.add_argument('--out')
    parser.add_argument('--list-sets', action='store_true')
    args = parser.parse_args()
    if args.list_sets:
        for tier, sets in TIERS.items():
            for name, kind, params in sets:
                print(tier, name, kind, params)
        return
    if args.tier is None or args.seed is None or args.out is None:
        parser.error('--tier, --seed and --out are required')
    name, params, text = generate(args.tier, args.seed)
    comment = '# corpus: tier=%s seed=%d set=%s generator=%s' % (args.tier, args.seed, name, params)
    lines = text.split('\n', 1)  # the header line stays first
    with open(args.out, 'w') as f:
        f.write(lines[0] + '\n' + comment + '\n' + lines[1])
    print(comment, file=sys.stderr)


if __name__ == '__main__':
    main()
