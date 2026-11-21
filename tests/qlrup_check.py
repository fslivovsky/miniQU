#!/usr/bin/env python3
"""Reference checker for QLRUP proofs of the miniQU QBF solver.

Usage: qlrup_check.py [--stats] FORMULA.qcir PROOF

FORMULA.qcir is the QCIR input (prenex; free/exists/forall, and/or/xor/ite
gates, output).  PROOF is a QLRUP proof in text format, or in binary format if
it starts with the 8 bytes "QLRUPb1\\n" (see doc/proof-format.md, which is the
specification implemented here).

Prints exactly one line on stdout:
  s VERIFIED TRUE          the proof derives the empty term
  s VERIFIED FALSE         the proof derives the empty clause
  s NOT VERIFIED: <reason> otherwise (reason names the line/step and the id)
Exit code 0 if verified, 1 otherwise.  The check stops at the first derived
constraint without literals.  With --stats, the number of original, derived
and deleted steps processed is printed to stderr.

The checker favours obvious correctness over speed.
"""
import re
import sys

MAGIC = b'QLRUPb1\n'


class Fail(Exception):
    pass


# --------------------------------------------------------------------------
# QCIR
# --------------------------------------------------------------------------

class Formula:
    """Variables 1..n are quantified, n+1..n+m are gates."""

    def __init__(self, path):
        self.n = 0
        self.nblocks = -1
        self.names = {}          # name -> variable number
        self.qtype = {}          # quantified var -> 'e' / 'a'
        self.block = {}          # quantified var -> block index
        self.depth = {}          # gate var -> depth (-1 if none)
        self.gates = {}          # gate var -> (kind 'and'/'or', [signed lits])
        self.num_gates = 0
        self.output = None       # signed literal
        self._parse(path)
        self.nvars = self.n + self.num_gates

    def _parse(self, path):
        last_q = None
        in_gates = False
        with open(path) as f:
            lines = f.read().split('\n')
        for ln, line in enumerate(lines, 1):
            line = re.sub(r'\s', '', line)
            if not line or line.startswith('#'):
                continue
            where = '%s line %d' % (path, ln)
            m = re.fullmatch(r'(exists|forall|free)\((.*)\)', line, re.I)
            if m:
                if in_gates:
                    raise Fail('%s: quantifier statement after gate definition' % where)
                kind = 'a' if m.group(1).lower() == 'forall' else 'e'
                args = m.group(2)
                for name in (args.split(',') if args else []):
                    if not name:
                        raise Fail('%s: empty variable name' % where)
                    if name in self.names:
                        raise Fail('%s: name %r defined twice' % (where, name))
                    self.n += 1
                    self.names[name] = self.n
                    self.qtype[self.n] = kind
                    if kind != last_q:
                        self.nblocks += 1
                        last_q = kind
                    self.block[self.n] = self.nblocks
                continue
            m = re.fullmatch(r'output\((.*)\)', line, re.I)
            if m:
                if self.output is not None:
                    raise Fail('%s: more than one output statement' % where)
                self.output = ('out', m.group(1), where)
                continue
            m = re.fullmatch(r'([^=()]+)=(and|or|xor|ite)\((.*)\)', line, re.I)
            if m:
                in_gates = True
                name, kind = m.group(1), m.group(2).lower()
                args = m.group(3)
                args = args.split(',') if args else []
                lits = [self._lit(a, where) for a in args]
                if name in self.names:
                    raise Fail('%s: name %r defined twice' % (where, name))
                if kind in ('and', 'or'):
                    self._new_gate(kind, lits, name)
                elif kind == 'xor':
                    if len(lits) != 2:
                        raise Fail('%s: xor needs exactly 2 inputs' % where)
                    a, b = lits
                    g1 = self._new_gate('and', [a, -b], None)
                    g2 = self._new_gate('and', [-a, b], None)
                    self._new_gate('or', [g1, g2], name)
                else:
                    if len(lits) != 3:
                        raise Fail('%s: ite needs exactly 3 inputs' % where)
                    c, a, b = lits
                    g1 = self._new_gate('and', [c, a], None)
                    g2 = self._new_gate('and', [-c, b], None)
                    self._new_gate('or', [g1, g2], name)
                continue
            raise Fail('%s: cannot parse %r' % (where, line))
        if self.output is None:
            raise Fail('%s: no output statement' % path)
        _, text, where = self.output
        self.output = self._lit(text, where)

    def _lit(self, text, where):
        neg = text.startswith('-')
        name = text[1:] if neg else text
        if name not in self.names:
            raise Fail('%s: %r is not defined (yet)' % (where, name))
        v = self.names[name]
        return -v if neg else v

    def _new_gate(self, kind, lits, name):
        self.num_gates += 1
        g = self.n + self.num_gates
        if name is not None:
            self.names[name] = g
        self.gates[g] = (kind, lits)
        d = -1
        for l in lits:
            v = abs(l)
            d = max(d, self.block[v] if v <= self.n else self.depth[v])
        self.depth[g] = d
        return g

    # -- prefix --------------------------------------------------------

    def rank(self, v):
        if v <= self.n:
            return 2 * self.block[v]
        return 2 * self.depth[v] + 1

    def before(self, a, b):
        return self.rank(a) < self.rank(b)

    def orig_universal(self, v):
        return v <= self.n and self.qtype[v] == 'a'

    def orig_existential(self, v):
        return v <= self.n and self.qtype[v] == 'e'

    def gate_clauses(self, g):
        kind, ins = self.gates[g]
        if kind == 'and':
            return [{-g, l} for l in ins] + [{g} | {-l for l in ins}]
        return [{g, -l} for l in ins] + [{-g} | set(ins)]


# --------------------------------------------------------------------------
# Proof parsing: yields (location, step) with step one of
#   ('o', id, type, gate, lits)   ('a', id, type, lits, ants)   ('d', ids)
# --------------------------------------------------------------------------

def parse_text(path):
    with open(path, 'r') as f:
        data = f.read()
    for ln, line in enumerate(data.split('\n'), 1):
        s = line.strip()
        if not s or s.startswith('#'):
            continue
        where = 'line %d' % ln
        toks = s.split()
        try:
            yield where, _text_step(toks)
        except ValueError:
            raise Fail('%s: malformed line (non-integer token?)' % where)
        except Fail as e:
            raise Fail('%s: %s' % (where, e))


def _ints_to_zero(toks, pos):
    """Integers from toks[pos:] up to a 0; returns (list, next position)."""
    out = []
    while pos < len(toks):
        x = int(toks[pos])
        pos += 1
        if x == 0:
            return out, pos
        out.append(x)
    raise Fail('missing terminating 0')


def _ctype(tok):
    if tok == 'c':
        return 'c'
    if tok == 't':
        return 't'
    raise Fail('bad constraint type %r' % tok)


def _text_step(toks):
    if toks[0] == 'o':
        if len(toks) < 5:
            raise Fail('truncated original step')
        cid, t, gate = int(toks[1]), _ctype(toks[2]), int(toks[3])
        lits, pos = _ints_to_zero(toks, 4)
        if pos != len(toks):
            raise Fail('trailing tokens after final 0')
        return ('o', cid, t, gate, lits)
    if toks[0] == 'd':
        ids, pos = _ints_to_zero(toks, 1)
        if pos != len(toks):
            raise Fail('trailing tokens after final 0')
        return ('d', ids)
    if len(toks) < 3:
        raise Fail('truncated step')
    cid, t = int(toks[0]), _ctype(toks[1])
    lits, pos = _ints_to_zero(toks, 2)
    ants, pos = _ints_to_zero(toks, pos)
    if pos != len(toks):
        raise Fail('trailing tokens after final 0')
    return ('a', cid, t, lits, ants)


class _Bin:
    def __init__(self, data):
        self.d = data
        self.p = len(MAGIC)

    def eof(self):
        return self.p >= len(self.d)

    def byte(self):
        if self.p >= len(self.d):
            raise Fail('unexpected end of file')
        b = self.d[self.p]
        self.p += 1
        return b

    def num(self):
        x, shift = 0, 0
        while True:
            b = self.byte()
            x |= (b & 0x7f) << shift
            shift += 7
            if not b & 0x80:
                return x

    def lit(self):
        x = self.num()
        if x == 0:
            return 0
        if x < 2:
            raise Fail('literal encoding %d denotes variable 0' % x)
        return -(x >> 1) if x & 1 else x >> 1

    def lits(self):
        out = []
        while True:
            l = self.lit()
            if l == 0:
                return out
            out.append(l)

    def nums(self):
        out = []
        while True:
            x = self.num()
            if x == 0:
                return out
            out.append(x)

    def ctype(self):
        t = self.num()
        if t == 0:
            return 'c'
        if t == 1:
            return 't'
        raise Fail('bad constraint type %d' % t)


def parse_binary(data):
    r = _Bin(data)
    k = 0
    while not r.eof():
        k += 1
        start = r.p
        where = 'step %d (byte offset %d)' % (k, start)
        try:
            tag = r.byte()
            if tag == ord('o'):
                cid = r.num()
                t = r.ctype()
                gate = r.num()
                yield where, ('o', cid, t, gate, r.lits())
            elif tag == ord('a'):
                cid = r.num()
                t = r.ctype()
                lits = r.lits()
                yield where, ('a', cid, t, lits, r.nums())
            elif tag == ord('d'):
                yield where, ('d', r.nums())
            else:
                raise Fail('unknown step tag byte %d' % tag)
        except Fail as e:
            raise Fail('%s: %s' % (where, e))


# --------------------------------------------------------------------------
# Checking
# --------------------------------------------------------------------------

class Checker:
    def __init__(self, formula):
        self.f = formula
        self.cons = {}           # id -> (type, frozenset of literals)
        self.stats = {'o': 0, 'a': 0, 'd': 0}

    def check_lits(self, lits):
        for l in lits:
            if l == 0 or abs(l) > self.f.nvars:
                raise Fail('literal %d out of range (variables are 1..%d)'
                           % (l, self.f.nvars))
            if -l in lits:
                raise Fail('complementary literals %d and %d' % (l, -l))
        return set(lits)

    def check_new_id(self, cid):
        if cid <= 0:
            raise Fail('identifier %d is not positive' % cid)
        if cid in self.cons:
            raise Fail('identifier %d is already in use' % cid)

    def original(self, cid, t, gate, lits):
        f = self.f
        self.check_new_id(cid)
        C = self.check_lits(lits)
        if gate == 0:
            if f.output not in C:
                raise Fail('id %d: %s does not contain the output literal %d'
                           % (cid, 'clause' if t == 'c' else 'term', f.output))
        else:
            if not f.n < gate <= f.nvars:
                raise Fail('id %d: gate %d is not a gate (gates are %d..%d)'
                           % (cid, gate, f.n + 1, f.nvars))
            S = C if t == 'c' else {-l for l in C}
            if not any(cl <= S for cl in f.gate_clauses(gate)):
                raise Fail('id %d: %s does not follow from gate %d'
                           % (cid, 'clause' if t == 'c' else 'term', gate))
        self.cons[cid] = (t, frozenset(C))

    def reduce(self, R, t):
        """Reduction of the set R (modified copy returned)."""
        f = self.f
        if t == 'c':
            removable, blocking = f.orig_universal, (lambda v: not f.orig_universal(v))
        else:
            removable, blocking = f.orig_existential, (lambda v: not f.orig_existential(v))
        bvars = [abs(l) for l in R if blocking(abs(l))]
        out = set(R)
        for u in R:
            v = abs(u)
            if removable(v) and -u not in R and all(f.before(b, v) for b in bvars):
                out.discard(u)
        return out

    def derived(self, cid, t, lits, ants):
        self.check_new_id(cid)
        C = self.check_lits(lits)
        if not ants:
            raise Fail('id %d: no antecedents' % cid)
        for a in ants:
            if a not in self.cons:
                raise Fail('id %d: antecedent %d does not exist (or was deleted)'
                           % (cid, a))
            if self.cons[a][0] != t:
                raise Fail('id %d: antecedent %d has a different type' % (cid, a))
        # Reducing only at the end is cheaper and is tried first; reducing after
        # every step can succeed where that fails.
        try:
            R = self.chain(cid, t, ants, eager=False)
            if R - C:
                raise Fail('retry')
        except Fail:
            R = self.chain(cid, t, ants, eager=True)
        missing = sorted(R - C)
        if missing:
            raise Fail('id %d: derived literals %s are not in the stated '
                       'constraint' % (cid, missing))
        self.cons[cid] = (t, frozenset(C))

    def chain(self, cid, t, ants, eager):
        """The result of resolving the antecedents in order, reduced."""
        R = set(self.cons[ants[0]][1])
        if eager:
            R = self.reduce(R, t)
        for a in ants[1:]:
            A = self.cons[a][1]
            clash = [p for p in A if -p in R]
            if len(clash) > 1:
                raise Fail('id %d: antecedent %d clashes on several literals %s'
                           % (cid, a, sorted(clash)))
            if clash:
                p = clash[0]
                R = (R - {-p}) | (set(A) - {p})
                if eager:
                    R = self.reduce(R, t)
        return self.reduce(R, t)

    def delete(self, ids):
        for i in ids:
            if i not in self.cons:
                raise Fail('deleting unknown identifier %d' % i)
            del self.cons[i]

    def run(self, steps):
        for where, step in steps:
            try:
                if step[0] == 'o':
                    self.stats['o'] += 1
                    self.original(*step[1:])
                elif step[0] == 'a':
                    self.stats['a'] += 1
                    self.derived(*step[1:])
                    if not step[3]:
                        return 'TRUE' if step[2] == 't' else 'FALSE'
                else:
                    self.stats['d'] += 1
                    self.delete(step[1])
            except Fail as e:
                raise Fail('%s: %s' % (where, e))
        raise Fail('proof ends without deriving an empty clause or term')


def main(argv):
    args = argv[1:]
    stats = False
    if args and args[0] == '--stats':
        stats = True
        args = args[1:]
    if len(args) != 2:
        sys.stderr.write(__doc__)
        return 2
    chk = None
    try:
        chk = Checker(Formula(args[0]))
        try:
            with open(args[1], 'rb') as f:
                head = f.read(len(MAGIC))
                if head == MAGIC:
                    steps = parse_binary(head + f.read())
                else:
                    steps = parse_text(args[1])
        except OSError as e:
            raise Fail('cannot read proof: %s' % e)
        verdict = chk.run(steps)
    except Fail as e:
        print('s NOT VERIFIED: %s' % e)
        code = 1
    else:
        print('s VERIFIED %s' % verdict)
        code = 0
    if stats and chk is not None:
        sys.stderr.write('original %d derived %d deleted %d\n'
                         % (chk.stats['o'], chk.stats['a'], chk.stats['d']))
    return code


if __name__ == '__main__':
    sys.exit(main(sys.argv))
