#!/usr/bin/env python3
"""Evaluate a small prenex QCIR instance by brute force (truth tables).

Usage: qcir_eval.py FILE

Prints SAT or UNSAT. Only practical for up to about 22 variables.
"""
import re
import sys


def main():
    blocks, gates, output = [], [], None
    with open(sys.argv[1]) as f:
        for line in f:
            line = re.sub(r'\s', '', line).lower()
            if not line or line.startswith('#'):
                continue
            head, args = line[:-1].split('(', 1)
            args = [a for a in args.split(',') if a]
            if head in ('exists', 'forall', 'free'):  # free variables are outermost existential
                blocks.append((head != 'forall', args))
            elif head == 'output':
                output = args[0]
            else:
                name, kind = head.split('=')
                gates.append((name, kind, args))
    variables = [v for _, vs in blocks for v in vs]
    n = len(variables)
    size = 1 << n
    full = (1 << size) - 1
    table, period = {}, {}
    for i, v in enumerate(variables):
        p = 1 << i
        chunk = ((1 << p) - 1) << p
        t = 0
        for start in range(0, size, 2 * p):
            t |= chunk << start
        table[v], period[v] = t, p

    def lit(l):
        return full & ~table[l[1:]] if l.startswith('-') else table[l]

    for name, kind, args in gates:
        if kind == 'ite':
            c, a, b = (lit(l) for l in args)
            t = (c & a) | (full & ~c & b)
        elif kind == 'xor':
            t = 0
            for l in args:
                t ^= lit(l)
        else:
            t = full if kind == 'and' else 0
            for l in args:
                t = (t & lit(l)) if kind == 'and' else (t | lit(l))
        table[name] = t
    t = lit(output)
    for existential, vs in reversed(blocks):
        for v in vs:
            mask = full & ~table[v]
            lo, hi = t & mask, (t >> period[v]) & mask
            r = (lo | hi) if existential else (lo & hi)
            t = r | (r << period[v])
    print('SAT' if t & 1 else 'UNSAT')


if __name__ == '__main__':
    main()
