#!/usr/bin/env python3
"""Random QCIR generator with a built-in truth-table evaluator.

Usage: qcir_fuzz.py SEED [--vars N] [--gates N] [--blocks N] [--cnf]

Writes the instance to stdout. The first line is a comment of the form
"# expected: SAT" or "# expected: UNSAT", computed by brute force, so that
the output of a solver can be checked without a reference solver.
"""
import argparse
import random


def generate(rng, nvars, ngates, nblocks, cnf):
    nvars = rng.randint(2, nvars)
    nblocks = rng.randint(1, min(nblocks, nvars))
    # Split variables into quantifier blocks of alternating type.
    cuts = sorted(rng.sample(range(1, nvars), nblocks - 1))
    bounds = [0] + cuts + [nvars]
    first_existential = rng.random() < 0.5
    blocks = []
    for i in range(nblocks):
        existential = first_existential ^ (i % 2 == 1)
        blocks.append((existential, list(range(bounds[i] + 1, bounds[i + 1] + 1))))
    gates = []  # (name, type, inputs); inputs are signed indices into "nodes"
    nnodes = nvars
    if cnf:
        nclauses = rng.randint(1, ngates)
        for _ in range(nclauses):
            width = rng.randint(1, min(5, nvars))
            ins = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, nvars + 1), width)]
            nnodes += 1
            gates.append((nnodes, 'or', ins))
        nnodes += 1
        gates.append((nnodes, 'and', list(range(nvars + 1, nnodes))))
        output = nnodes
    else:
        ngates = rng.randint(1, ngates)
        for _ in range(ngates):
            width = rng.choice([0, 1, 2, 2, 2, 3, 3, 4])
            # Bias inputs towards recent nodes to obtain deeper circuits.
            ins = []
            for _ in range(width):
                if rng.random() < 0.5 and nnodes > nvars:
                    n = rng.randint(max(1, nnodes - 6), nnodes)
                else:
                    n = rng.randint(1, nnodes)
                ins.append(n if rng.random() < 0.5 else -n)
            nnodes += 1
            kind = rng.choice(['and', 'or'])
            if width in (2, 3) and rng.random() < 0.2:
                kind = 'xor' if width == 2 else 'ite'
            gates.append((nnodes, kind, ins))
        output = nnodes if rng.random() < 0.7 else -nnodes
    return nvars, blocks, gates, output


def evaluate(nvars, blocks, gates, output):
    size = 1 << nvars
    full = (1 << size) - 1
    table = {}
    for v in range(1, nvars + 1):
        # Bit a of the table is set iff variable v is true in assignment a.
        period = 1 << (v - 1)
        chunk = ((1 << period) - 1) << period
        t = 0
        for start in range(0, size, 2 * period):
            t |= chunk << start
        table[v] = t

    def lit(l):
        return table[l] if l > 0 else full & ~table[-l]

    for name, kind, ins in gates:
        if kind == 'and':
            t = full
            for l in ins:
                t &= lit(l)
        elif kind == 'or':
            t = 0
            for l in ins:
                t |= lit(l)
        elif kind == 'xor':
            t = lit(ins[0]) ^ lit(ins[1])
        else:
            t = (lit(ins[0]) & lit(ins[1])) | (lit(-ins[0]) & lit(ins[2]))
        table[name] = t
    t = lit(output)
    # Eliminate quantifiers from the innermost block outwards.
    for existential, variables in reversed(blocks):
        for v in variables:
            period = 1 << (v - 1)
            low_mask = full & ~table[v]
            lo = t & low_mask
            hi = (t >> period) & low_mask
            r = (lo | hi) if existential else (lo & hi)
            t = r | (r << period)
    return bool(t & 1)


def write(nvars, blocks, gates, output, expected):
    def name(n):
        return ('v%d' % n) if n <= nvars else ('g%d' % n)

    def lit(l):
        return name(l) if l > 0 else '-' + name(-l)

    lines = ['#QCIR-G14', '# expected: %s' % ('SAT' if expected else 'UNSAT')]
    for existential, variables in blocks:
        lines.append('%s(%s)' % ('exists' if existential else 'forall', ', '.join(name(v) for v in variables)))
    lines.append('output(%s)' % lit(output))
    for n, kind, ins in gates:
        lines.append('%s = %s(%s)' % (name(n), kind, ', '.join(lit(l) for l in ins)))
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('seed', type=int)
    parser.add_argument('--vars', type=int, default=12)
    parser.add_argument('--gates', type=int, default=30)
    parser.add_argument('--blocks', type=int, default=6)
    parser.add_argument('--cnf', action='store_true', help='generate a CNF matrix')
    args = parser.parse_args()
    rng = random.Random(args.seed)
    instance = generate(rng, args.vars, args.gates, args.blocks, args.cnf)
    print(write(*instance, evaluate(*instance)), end='')


if __name__ == '__main__':
    main()
