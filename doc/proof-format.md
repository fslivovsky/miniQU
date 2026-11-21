# QLRUP: the miniQU proof format

miniQU can write a proof of its result for QCIR input (`-proof=<file>`). The
proof lists the clauses and terms (cubes) the solver starts from and learns,
each learnt constraint together with the identifiers of the constraints it was
derived from, in the style of LRAT/LRUP. A proof that derives the empty clause
shows that the formula is false, and a proof that derives the empty term shows
that it is true.

Proofs are supported in modes 0 and 1 (Q-resolution and QU-resolution, with or
without dependency learning), but not in mode 2 (long-distance resolution).

## Variables

The proof refers to the variables and gates of the QCIR file by number:

- The quantified variables are numbered `1, ..., n` in the order in which they
  appear in the quantifier statements (`free`, `exists`, `forall`) of the file.
- The gates are numbered `n+1, n+2, ...` in the order of their definitions in
  the file. A gate `g = xor(a, b)` stands for three gates, in this order:
  `and(a, -b)`, `and(-a, b)`, and `g = or(...)` of the two. Likewise,
  `g = ite(c, a, b)` stands for `and(c, a)`, `and(-c, b)`, and `g = or(...)`
  of the two.

A literal is a nonzero integer `v` or `-v`. The number of a gate denotes the
variable representing the gate. A clause can only contain the existential
variable of a gate and a term only the universal one (see below), so the type
of the constraint determines which of the two is meant.

## Semantics

A proof is a sequence of steps that maintain a set of clauses and a set of
terms, each constraint with a unique positive identifier.

Clauses are interpreted with respect to the prefix of the QCIR file extended by
an existential variable for every gate, and terms with respect to the prefix
extended by a universal variable for every gate. In both cases, the variable of
a gate is placed after the variables and gates the gate (transitively) depends
on, and before every variable quantified later than those: if the innermost
quantifier block containing a variable the gate depends on is block `d`, the
gate variable is placed between blocks `d` and `d+1` (gates that do not depend
on any variable are placed before the first block). The relative order of gate
variables placed between the same two blocks does not matter.

### Original constraints

    o <id> <c|t> <gate> <lit> ... <lit> 0

adds a clause (`c`) or term (`t`) that follows from the definition of a gate,
or from the output statement if `<gate>` is `0`.

Let `g` be a gate with inputs `l_1, ..., l_k`. The clauses of `g` are

| gate | clauses |
|---|---|
| `and` | `(-g, l_i)` for each `i`, and `(g, -l_1, ..., -l_k)` |
| `or`  | `(g, -l_i)` for each `i`, and `(-g, l_1, ..., l_k)` |

and the clause of the output statement `output(l)` is `(l)`. An original clause
is valid if it contains all literals of one of these clauses. An original term
is valid if the negations of its literals contain all literals of a clause of
the gate, or, for `<gate>` `0`, if it contains the output literal `l`. (For
example, the terms of `g = and(l_1, l_2)` are `(g, -l_1)`, `(g, -l_2)`, and
`(-g, l_1, l_2)`: no assignment that is consistent with the gate satisfies any
of them. The term `(l)` of the output is satisfied only if the formula is.)

### Derived constraints

    <id> <c|t> <lit> ... <lit> 0 <id_1> ... <id_m> 0

adds a clause or term `C` derived from the constraints `id_1, ..., id_m`, which
must be of the same type and `m >= 1`. For clauses, the derivation is checked
as follows (QU-resolution with universal reduction):

1. Let `R` be the clause `id_1`, after reduction (see below).
2. For `j = 2, ..., m`, let `A` be the clause `id_j`. If there is exactly one
   literal `p` in `A` such that `-p` is in `R`, replace `R` by the resolvent
   `(R \ {-p}) ∪ (A \ {p})`, followed by reduction. If there is no such
   literal, `R` stays the same. If there are several, the step is invalid.
3. Every literal of `R` must occur in `C`.

Reduction removes each universal literal `u` from `R` such that `-u` is not in
`R` and every existential variable in `R` comes before the variable of `u` in
the extended prefix. Note that the pivot of a resolution step can be universal.

Terms are checked in the same way with the roles of existential and universal
variables exchanged (so reduction removes existential literals).

A derived constraint without literals ends the proof: the empty clause means
that the formula is false, and the empty term means that it is true.

### Deletion

    d <id> ... <id> 0

removes constraints. Identifiers of removed constraints must not be used later.

## Binary format

A binary proof starts with the eight bytes `QLRUPb1\n`. It is followed by the
same steps, where each number is written as a variable-length unsigned integer
(seven bits per byte, least significant group first, the high bit set on all
but the last byte), a literal `l` is written as the number `2*|l| + (l < 0)`,
and

    o <id> <c|t> <gate> <lits> 0     is   'o' <id> <type> <gate> <lits> 0
    <id> <c|t> <lits> 0 <ids> 0      is   'a' <id> <type> <lits> 0 <ids> 0
    d <ids> 0                        is   'd' <ids> 0

with `'o'`, `'a'`, `'d'` single bytes and `<type>` the number `0` for a clause
and `1` for a term.

## Text format details

Steps are separated by newlines and tokens by spaces. Lines that are empty or
start with `#` are ignored.
