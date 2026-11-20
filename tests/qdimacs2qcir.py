#!/usr/bin/env python3
"""Convert a prenex CNF QBF in QDIMACS format to QCIR.

Usage: qdimacs2qcir.py INPUT.qdimacs > OUTPUT.qcir

Variables that are not bound by the prefix are existentially quantified in
an outermost block.
"""
import sys


def main():
    blocks, clauses, bound = [], [], set()
    with open(sys.argv[1]) as f:
        for line in f:
            tokens = line.split()
            if not tokens or tokens[0] in ('c', 'p'):
                continue
            if tokens[0] in ('a', 'e'):
                variables = [int(t) for t in tokens[1:-1]]
                bound.update(variables)
                if variables:
                    blocks.append((tokens[0], variables))
            else:
                clauses.append([int(t) for t in tokens[:-1]])
    free = sorted({abs(l) for c in clauses for l in c} - bound)
    if free:
        blocks.insert(0, ('e', free))
    print('#QCIR-G14')
    for kind, variables in blocks:
        print('%s(%s)' % ('exists' if kind == 'e' else 'forall', ', '.join('v%d' % v for v in variables)))
    print('output(g)')
    for i, clause in enumerate(clauses):
        print('c%d = or(%s)' % (i, ', '.join(('-v%d' % -l) if l < 0 else ('v%d' % l) for l in clause)))
    print('g = and(%s)' % ', '.join('c%d' % i for i in range(len(clauses))))


if __name__ == '__main__':
    main()
