#!/usr/bin/env python3
"""Generators for larger QCIR instances (too big for brute force).

Usage: qcir_gen.py FAMILY SEED [SIZE [PARAM]]

PARAM is the clause/variable ratio for 'qcnf', the number of states for
'reach', and the number of gates per unit of SIZE for 'game' and 'synth'.

Families:
  qcnf    random prenex CNF with a fixed number of universal and existential
          literals per clause (Chen-Interian style), three quantifier blocks
  synth   exists K forall X: C(X, K) == S(X) for random circuits C and S;
          with probability 1/2, S is C with a hidden key (hence true)
  game    random and/or circuit with many quantifier alternations
  reach   two-player reachability game on a random graph with SIZE rounds:
          the existential player wins by reaching a goal state while
          avoiding bad states
"""
import random
import sys


RATIO = 2.4  # Clauses per existential variable of the outer block in 'qcnf'.
STATES = 24  # Number of states in 'reach'.
GATES = None  # Gates per unit of SIZE in 'game' (default 6) and 'synth' (default 3).


class Circuit:
    def __init__(self):
        self.lines = []
        self.count = 0

    def gate(self, kind, inputs):
        self.count += 1
        name = 'g%d' % self.count
        self.lines.append('%s = %s(%s)' % (name, kind, ', '.join(inputs)))
        return name

    def xor(self, a, b):
        return self.gate('or', [self.gate('and', [a, neg(b)]), self.gate('and', [neg(a), b])])


def neg(l):
    return l[1:] if l.startswith('-') else '-' + l


def rlit(rng, names):
    l = rng.choice(names)
    return l if rng.random() < 0.5 else neg(l)


def qcnf(rng, n):
    xs = ['x%d' % i for i in range(n)]
    us = ['u%d' % i for i in range(max(1, n // 2))]
    ys = ['y%d' % i for i in range(n)]
    c = Circuit()
    clauses = []
    for _ in range(int(RATIO * n)):
        lits = [rlit(rng, us), rlit(rng, xs + ys), rlit(rng, ys), rlit(rng, ys)]
        clauses.append(c.gate('or', lits))
    out = c.gate('and', clauses)
    return [('exists', xs), ('forall', us), ('exists', ys)], out, c


def random_circuit(rng, c, inputs, ngates):
    nodes = list(inputs)
    for _ in range(ngates):
        pool = nodes[-8:] if rng.random() < 0.6 else nodes
        a, b = rlit(rng, pool), rlit(rng, nodes)
        kind = rng.choice(['and', 'or', 'xor'])
        nodes.append(c.xor(a, b) if kind == 'xor' else c.gate(kind, [a, b]))
    return nodes[-1]


def synth(rng, n):
    ks = ['k%d' % i for i in range(n)]
    xs = ['x%d' % i for i in range(n)]
    c = Circuit()
    state = random.Random(rng.random())
    seed = rng.random()
    ngates = int((GATES or 3) * n)
    lhs = random_circuit(random.Random(seed), c, xs + ks, ngates)
    if rng.random() < 0.5:
        # Hidden key: replace key inputs by constants in an identical circuit.
        true, false = c.gate('and', []), c.gate('or', [])
        consts = [state.choice([true, false]) for _ in ks]
        rhs = random_circuit(random.Random(seed), c, xs + consts, ngates)
    else:
        rhs = random_circuit(state, c, xs, ngates)
    out = neg(c.xor(lhs, rhs))
    return [('exists', ks), ('forall', xs)], out, c


def game(rng, n):
    blocks, names = [], []
    for i in range(n):
        vs = ['v%d_%d' % (i, j) for j in range(3)]
        blocks.append(('exists' if i % 2 == 0 else 'forall', vs))
        names += vs
    c = Circuit()
    out = random_circuit(rng, c, names, int((GATES or 6) * n))
    return blocks, out, c


def reach(rng, rounds, bits=2):
    states = int(STATES)
    c = Circuit()
    moves = 1 << bits
    succ = [[rng.randrange(states) for _ in range(moves)] for _ in range(states)]
    goal = set(rng.sample(range(1, states), rng.randint(2, 5)))
    bad = set(rng.sample(sorted(set(range(1, states)) - goal), rng.randint(states // 8, states // 3)))
    blocks = []
    true, false = c.gate('and', []), c.gate('or', [])
    current = [true if i == 0 else false for i in range(states)]
    alive = true  # No bad state visited so far.
    wins = []
    for t in range(rounds):
        vs = ['m%d_%d' % (t, j) for j in range(bits)]
        blocks.append(('exists' if t % 2 == 0 else 'forall', vs))
        choice = [c.gate('and', [vs[j] if (m >> j) & 1 else neg(vs[j]) for j in range(bits)]) for m in range(moves)]
        incoming = [[] for _ in range(states)]
        for i in range(states):
            for m in range(moves):
                incoming[succ[i][m]].append(c.gate('and', [current[i], choice[m]]))
        current = [c.gate('or', incoming[i]) for i in range(states)]
        alive = c.gate('and', [alive] + [neg(current[i]) for i in sorted(bad)])
        wins.append(c.gate('and', [alive, c.gate('or', [current[i] for i in sorted(goal)])]))
    return blocks, c.gate('or', wins), c


def render(family, seed, size=None, param=None):
    """Return the QCIR text of one instance (the same as the command line gives)."""
    global RATIO, STATES, GATES
    rng = random.Random('%s-%d' % (family, seed))
    defaults = {'qcnf': 40, 'synth': 12, 'game': 12, 'reach': 10}
    if param is not None:  # each family reads only its own knob
        RATIO = STATES = GATES = float(param)
    size = defaults[family] if size is None else size
    blocks, out, c = {'qcnf': qcnf, 'synth': synth, 'game': game, 'reach': reach}[family](rng, size)
    lines = ['#QCIR-G14']
    lines += ['%s(%s)' % (kind, ', '.join(vs)) for kind, vs in blocks]
    lines.append('output(%s)' % out)
    lines += c.lines
    return '\n'.join(lines) + '\n'


def main():
    family, seed = sys.argv[1], int(sys.argv[2])
    size = int(sys.argv[3]) if len(sys.argv) > 3 else None
    param = sys.argv[4] if len(sys.argv) > 4 else None
    print(render(family, seed, size, param), end='')


if __name__ == '__main__':
    main()
