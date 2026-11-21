# miniQU rewrite: architecture

Status: target design, written before any code exists. Owner: coordinator.
Workers implement it; if the design turns out to be wrong somewhere, record the
deviation and the reason in `STATUS.md` (and fix this file in the same commit).

Reading order for a new agent: sections 1-3 (what and where), then the section
of the module being worked on, then section 12 (style). `ROADMAP.md` says
*when* things are built and what the acceptance gates are.

Terminology: a **constraint** is a clause or a cube. "Cube" is what the old
code and the proof format call a "term"; the new code says `Cube` everywhere,
the proof format keeps the letter `t`. For a constraint kind, the **primary**
variables are the ones it can be resolved on and that it propagates
(existential for clauses, universal for cubes); the others are **secondary**
and are the ones removed by reduction. "Old code" means `minisat/core/Solver.cc`
at commit c39005a (the baseline binary).

---------------------------------------------------------------------------

## 1. Goals and non-goals

Goals, in priority order:

1. Correctness. Every answer agrees with the baseline, and every proof is
   accepted by the verified Lean checker `qlrup-check`.
2. A code base in which one technique lives in one translation unit, shared
   state is explicit, and each technique states its QBF side conditions and
   its proof steps next to the code.
3. Performance at least as good as the baseline after M1, and measurably
   better after M2-M4 (see ROADMAP for the measurement protocol).

Retained from MiniSat/miniQU on purpose (owner requirement):

- the region **arena** for constraints with 32-bit references and a copying
  garbage collector (section 5);
- MiniSat-style **watcher lists** with blocker literals and lazy cleaning, and
  a garbage collector that lays constraints out in the order in which the
  watcher lists access them (section 6).

Non-goals: incremental solving (assumptions, freeze/melt reference counting,
clause restore), IPASIR, multi-threading, local search, DQBF, non-prenex
input. The dead MiniSat code in the old tree (`SimpSolver`, `toDimacs`,
`implies`, `releaseVar`, user polarities, random decisions, the unused
`addInitialTerms`/`updateDecisionVars`) is not ported.

---------------------------------------------------------------------------

## 2. Repository layout and build

```
CMakeLists.txt          root project: new solver, tools, tests (rewritten in M1)
CMakePresets.json       release / debug / asan / log presets
src/                    the new solver (this document)
test/unit/              unit tests (one executable per module, run by ctest)
tests/                  system tests: fuzzers, regress.sh, evaluators, cert check
tools/                  qlrup-trim
bench/                  benchmark harness and small result files
doc/rewrite/            ARCHITECTURE.md, ROADMAP.md, STATUS.md, reviews/
minisat/                old solver, frozen; never edited, removed only when the
                        owner says so (the baseline binary is built from it)
```

Build rules:

- C++20 as supported by GCC 11.5 and Clang 15 (both are installed): concepts,
  `std::span`, `<bit>`, designated initialisers, `[[likely]]`, `constexpr`
  are available; `std::format`, modules and ranges pipelines are **not** to be
  used. No dependencies besides zlib and the standard library.
- Flags for `src/` and `test/unit/`: `-Wall -Wextra -Wpedantic -Wshadow
  -Wconversion -Wsign-conversion -Werror` (the one accepted exception, the
  flexible array member of `Constraint`, is silenced locally with a pragma,
  not globally). The code must compile warning-free with both compilers; the
  regular build uses GCC.
- Presets (build trees live outside the repo, `binaryDir` =
  `${sourceParentDir}/miniqu-work/build/${presetName}`):

  | preset    | flags                                                        | purpose |
  |-----------|--------------------------------------------------------------|---------|
  | `release` | `-O3 -DNDEBUG`, LTO                                          | benchmarks; no assertions, no logging code |
  | `debug`   | `-O0 -g`, assertions, `MINIQU_LOGGING`, internal checker      | development |
  | `asan`    | `-O1 -g -fsanitize=address,undefined -fno-sanitize-recover`, assertions | fuzzing |
  | `log`     | `-O2 -g -DNDEBUG` + `MINIQU_LOGGING`                         | tracing a long run |

  Usage: `taskset -c 0-63 cmake --preset release && taskset -c 0-63 cmake
  --build --preset release -j16`. Targets: `miniQU` (binary), `miniqu`
  (static library), `qlrup-trim`, `unit-tests` (all unit test executables),
  and `ctest --preset <p>` runs them plus a 20-seed fuzz.
- The old solver stays buildable only through its own `Makefile`; the root
  `CMakeLists.txt` no longer references `minisat/`.

---------------------------------------------------------------------------

## 3. Module map

One namespace, `miniqu`. Three layers, each depending only on the ones below:

```
 app        app.cpp  signal.cpp  resources.cpp
              |            (owns: argv, files, names of QCIR identifiers, output)
 frontend   parse_qcir.cpp  parse_qdimacs.cpp  circuit.{hpp,cpp}  encode.cpp
              |            (owns: the circuit, gate numbers, polarities, depths)
 API        miniqu.hpp  solver.cpp           class Solver (pimpl, contracts)
              |
 external   external.{hpp,cpp}  extend.cpp   user variables <-> internal
              |                              variables, extension stack
 internal   internal.hpp + one .cpp per technique (below)
              |
 base       arena  constraint  watch  heap  ema  options  stats  profile
            limit  logging  message  file  util  random  contract
```

`struct Internal` (`internal.hpp`) holds the whole solver state as plain data
members; the technique files implement its member functions. This is CaDiCaL's
structure and the reason it works is discipline, not encapsulation: a
technique file may *read* everything but *writes* only the state it owns or
state it changes through the owner's functions (e.g. constraints are created
and deleted only through `constraint.cpp`, assignments only through
`assign`/`backtrack`). The table lists owners.

### 3.1 Base

| file | contents |
|---|---|
| `lit.hpp` | `Var`, `Lit`, `Kind`, `Quant`; conversions; no solver state |
| `arena.{hpp,cpp}` | `Arena`: region of 32-bit words, `Ref`, alloc/free accounting, `moveTo` |
| `constraint.hpp` | `Constraint` header layout and accessors (section 5.2) |
| `watch.hpp` | `Watch`, `Watches` (lists per literal and kind, dirty flags, lazy cleaning) |
| `heap.hpp` | indexed binary max-heap on variable scores |
| `ema.hpp` | exponential moving average with bias correction |
| `options.{hpp,cpp}` | X-macro option table (section 9.1) |
| `stats.{hpp,cpp}` | counters and their printing (9.2) |
| `profile.{hpp,cpp}` | `START`/`STOP` timers (9.3) |
| `limit.hpp` | `Limit` (next-event thresholds), `Inc` (increments), `Last` (9.4) |
| `logging.{hpp,cpp}`, `message.{hpp,cpp}` | `LOG`, `PHASE`, `VERBOSE`, `MSG`, `fatal` (9.5) |
| `contract.hpp` | `REQUIRE` for API misuse (9.6) |
| `file.{hpp,cpp}` | buffered input (plain/gzip via zlib), buffered output |
| `util.hpp`, `random.hpp` | small helpers; PRNG |

### 3.2 Internal: search

| file | owns / implements |
|---|---|
| `internal.{hpp,cpp}` | `Internal` state, construction, `solve ()`, the CDCL loop (section 7.1) |
| `prefix.{hpp,cpp}` | quantifier blocks, per-variable `Quant`/depth/flags, `qreduce` (4.2, 4.6) |
| `constraint.cpp` | `new_constraint`, `mark_garbage`, `shrink_constraint`, attach/detach, the constraint lists |
| `assign.cpp` | `assign`, `Var` data (level, reason, trail position) |
| `propagate.cpp` | propagation for modes 0 and 1, both kinds (7.2) |
| `propagate_ldq.cpp` | propagation for mode 2 (7.2) |
| `backtrack.cpp` | `backtrack (level)`, phase saving, heap re-insertion |
| `decide.cpp` | block selection, eligibility, `decide ()` (7.3) |
| `depend.cpp` | dependency learning: dependency lists, their watches, reset (7.4) |
| `analyze.cpp` | Q-resolution analysis (mode 0, default) (7.5) |
| `analyze_qu.cpp` | the older level-by-level analysis: mode 1, and mode 0 with `--legacyanalyze` |
| `analyze_ldq.cpp` | long-distance analysis (mode 2) |
| `learn.cpp` | common tail of the analyses: minimise, reduce, backjump level, glue, proof step, attach, assign; learning a dependency; the final empty constraint |
| `minimize.cpp` | learnt-constraint minimisation (`ccminmode` 1-3) |
| `model.cpp` | initial cube from a satisfying assignment (4.5) |
| `bump.cpp` | variable scores (EVSIDS), constraint `used`/glue update |
| `restart.cpp` | Luby and (M2) EMA restarts, trail reuse |
| `reduce.cpp` | learnt-database reduction (the *database* sense of "reduce") |
| `tier.cpp` | (M2) glue tiers, usage histogram, tier limit recomputation |
| `rephase.cpp`, `mode.cpp` | (M2) rephasing; stable/focused switching |
| `collect.cpp` | root-level simplification of the databases, arena garbage collection (5.3) |
| `report.cpp` | progress lines |
| `certificate.cpp` | outermost-block assignment for `--cert` |

### 3.3 Internal: proofs

| file | contents |
|---|---|
| `tracer.hpp` | abstract `Tracer` (section 8) |
| `proof.{hpp,cpp}` | `Proof`: the one object the solver talks to; id allocation, literal translation, fan-out to tracers |
| `qlrup_tracer.{hpp,cpp}` | QLRUP text and binary writer |
| `trace_tracer.{hpp,cpp}` | the older `-trace` format (also works for QDIMACS) |
| `checker.{hpp,cpp}` | online checker of derived steps, for debug/asan builds and `--check` |

### 3.4 Internal: inprocessing (M3 and later)

| file | contents |
|---|---|
| `inprocess.cpp` | scheduling of passes, effort budgets, entering/leaving "occurrence mode" (10.1) |
| `flags.hpp` | per-variable status (active/fixed/eliminated/...) and scheduling marks |
| `occs.{hpp,cpp}` | full occurrence lists per literal and kind (10.2) |
| `elim.cpp` | bounded variable elimination (clause and cube distribution) |
| `subsume.cpp` | subsumption and strengthening |
| `vivify.cpp` | vivification of clauses and cubes |
| later: `block.cpp`, `probe.cpp`, `decompose.cpp`, `gates.cpp`, `expand.cpp` | see ROADMAP M5+ |

### 3.5 External, API, frontend, app

| file | contents |
|---|---|
| `external.{hpp,cpp}` | user variable numbers <-> internal variables; building the prefix; frozen marks; `val` of user variables |
| `extend.cpp` | extension stack and reconstruction of eliminated outermost variables (10.4) |
| `miniqu.hpp`, `solver.cpp` | public `class Solver`; checks contracts and forwards to `External` |
| `circuit.{hpp,cpp}` | prenex circuit: variables, blocks, AND/OR gates (xor/ite expanded), cone-of-influence removal, polarities, gate depths |
| `parse_qcir.cpp`, `parse_qdimacs.cpp` | parsers; report errors with line numbers |
| `encode.cpp` | dual Plaisted-Greenbaum encoding of a `Circuit` into a `Solver` (4.4) |
| `app.cpp` | `main`: options, parsing, limits, signals, result line, exit code, `V` line |

The public API (`miniqu.hpp`) is small and single-shot. User variables and
literals are nonzero `int`s as in DIMACS:

```cpp
class Solver {
public:
  Solver ();  ~Solver ();
  bool set (std::string_view option, int value);       // before the first add_var
  // Formula, in this order: all variables (prefix order), then constraints.
  void add_var (int var, Quant, bool decision = true, int proof_number = 0);
  void add_original (Kind, std::span<const int> lits, int proof_gate = 0);
  void freeze (int var);                                // never eliminate
  void connect_tracer (std::unique_ptr<Tracer>);        // before add_original
  int solve ();                                         // 10 true, 20 false, 0 unknown
  int val (int var) const;                              // certificate block only; 0 = unassigned
  std::vector<int> certificate () const;
  void terminate ();                                    // async-signal-safe
  void statistics () const;
private:
  std::unique_ptr<External> external;
};
```

Consecutive `add_var` calls with the same quantifier form one block. QDIMACS
uses `add_var` + `add_original (Kind::Clause, ...)` only; the QCIR encoder
uses everything.

Dependency rules: nothing below `app` prints to stdout except through
`message.cpp`; nothing below `frontend` knows about identifiers or files
(the proof *file* is opened by the app and handed to a tracer); `Internal`
never sees user variable numbers; the frontend uses only `miniqu.hpp`.

---------------------------------------------------------------------------

## 4. The QBF data model

### 4.1 Literals, kinds, values

```cpp
using Var = uint32_t;                       // 0 .. vars-1, in prefix order (4.2)
struct Lit { uint32_t x; };                 // 2*var + sign; sign 1 = negated
constexpr Lit mk_lit (Var v, bool neg);     // var (l), sign (l), ~l, index (l)
enum class Kind  : uint8_t { Clause = 0, Cube = 1 };
enum class Quant : uint8_t { Exists = 0, Forall = 1 };
constexpr Quant primary (Kind k);           // Clause -> Exists, Cube -> Forall
```

`Lit` stays MiniSat-encoded (not CaDiCaL's signed `int`) because literals
index the watch and occurrence arrays directly and are stored in arena words.
`Lit` and `Ref` are distinct types so that they cannot be mixed up with
integers, ids or each other.

Values are stored per *literal* as `int8_t` (`vals[index (lit)]` is `1`,
`-1` or `0`), as in CaDiCaL, so the inner loops are one load and one
comparison. Clauses and cubes are treated uniformly through the **kind value**
of a literal:

    kval (Clause, l) = val (l)        kval (Cube, l) = -val (l) = val (~l)

For either kind: a literal with `kval > 0` **disables** (satisfies) the
constraint; a literal with `kval < 0` has **vanished**; a constraint all of
whose literals vanished is a conflict (a falsified clause, or a satisfied
cube, i.e. a "solution"); a constraint with exactly one non-vanished literal
`l` forces `kval (l) > 0`, that is, assigns `l` for a clause and `~l` for a
cube. All kind-generic code is written once as a function template over
`Kind` (or takes `Kind` as a parameter where it is not hot) and never spells
out the two cases separately.

### 4.2 Prefix

Internal variables are numbered **in prefix order**: if `u < v` as integers
then `u` is quantified no later than `v`. This is how the old code compares
variables (`v > rightmost_primary`, `pivot < blocked`, `sort (lits)` before
reduction) and it is kept as an invariant because it makes the hot comparisons
integer comparisons. Consequences:

- a quantifier block is a contiguous range of variables:
  `struct Block { Quant quant; Var begin, end; int unassigned; }`
  (`unassigned` = number of unassigned *active decision* variables, used to
  find the current decision block without dependency learning);
- adjacent blocks have different quantifiers (the builder merges);
- `depth (v)` is the block index; for variables of different quantifier,
  comparing indices and comparing depths is the same thing;
- variables are created only while the formula is being added. A later
  technique that needs fresh variables has to renumber (a `compact` pass);
  nothing in M1-M4 does.

Per-variable static data (`prefix.hpp`): `Quant`, depth, and flags
`decision` (input variable, may be decided), `gate` (Tseitin variable,
never decided, never printed). Per-variable dynamic status lives in
`flags.hpp` (section 10.3).

### 4.3 Constraint databases

All constraints live in one arena and are referenced by `Ref`. There are two
lists of references per kind: `irredundant[kind]` (original, or derived and
required to keep the formula equivalent, e.g. BVE resolvents) and
`redundant[kind]` (learnt; may be deleted at any time). The bit in the
constraint header is authoritative; the lists exist for iteration.

Unit constraints are allocated like any other constraint (size 1, never
watched) and serve as the reason of their root-level assignment, so that
reasons and proof ids are uniform. The empty constraint is never allocated;
deriving it ends the search.

Invariants (checked by `check_invariants ()` in debug builds, at root level):

- **INV-ORDER**: internal variable order is a linearisation of the prefix.
- **INV-REDUCED**: every stored constraint is reduced: it contains no
  secondary literal to the right of all its primary literals. (Mode 2 learnt
  constraints may contain complementary secondary literals; they are still
  reduced.) No stored constraint contains duplicate literals; outside mode 2
  none contains complementary literals.
- **INV-DERIVED**: every stored constraint is either an original constraint
  of the encoding, or was derived from stored constraints of the *same kind*
  by resolution and reduction, in a way that is expressible as one QLRUP step.
  This holds whether or not a proof is being written; with a proof, the step
  has been emitted. The only exceptions are initial cubes from satisfying
  assignments (4.5) and mode 2. In particular a literal is never removed from
  a constraint because of an assignment whose reason has the other kind.
- **INV-WATCH**: outside occurrence mode and outside propagation, every
  non-garbage constraint of size >= 2 has watches on its literals 0 and 1
  (plus possibly stale watches, see 6.3 for mode 2), and both watch lists are
  consistent with the watch invariant of the mode.
- **INV-COMPLETE** (QCIR input): if all decision variables are assigned and
  propagation ran to completion, at least one of the two kinds has a conflict.
  It holds for the encoding (4.4) and must be preserved by every transformation
  of the irredundant databases (section 11 explains which ones do).

### 4.4 QCIR: the dual encoding

The frontend turns a QCIR file into a `Circuit` (variables in blocks; AND/OR
gates; `xor (a,b)` and `ite (c,a,b)` expanded into three gates each exactly
as the proof format prescribes; gates not in the cone of the output removed;
each remaining gate labelled with the polarities in which the output depends
on it) and then encodes it twice:

- as **clauses** over the input variables and one *existential* variable per
  gate, with the unit clause `(out)`;
- as **cubes** over the input variables and one *universal* variable per
  gate, with the unit cube `(out)`.

Both use the Plaisted-Greenbaum encoding: only the implications needed for the
gate's polarity are generated. The cube side is the clause encoding of the
negated circuit with every clause negated, so "the circuit is true under this
assignment" shows up as a satisfied cube exactly like "the circuit is false"
shows up as a falsified clause. Gate variables are not decision variables.
With `--earlytseitin` (default) the two variables of a gate are placed right
after the innermost block `d` containing a variable the gate depends on: the
gate variable whose quantifier is that of block `d` extends block `d`, the
other one follows and merges with block `d+1`. Gates that depend on no
variable come before the first block; without the option all gate variables
are innermost. The exact group order is the old `QCIRParser::initSolver` and
must be reproduced: the Lean checker places each gate variable between blocks
`d` and `d+1` of its own extended prefix, and the solver's reduction must
never be stronger than the checker's.

The frontend also gives every variable its **proof number** (inputs
`1..n` in file order, then gates in definition order; both variables of a gate
share the gate's number) and passes, with every original constraint, the
number of the gate whose definition it belongs to (0 for the output).

Input variables therefore occur in both databases, while every gate variable
occurs in constraints of one kind only. This is what makes gate variables the
candidates for elimination (ROADMAP M3).

### 4.5 QDIMACS and initial cubes

QDIMACS input has clauses only. When every decision variable is assigned
without conflict, `model.cpp` computes an **initial cube**: for each
*irredundant* clause one true literal (preferring literals already chosen),
followed by existential reduction; analysis then proceeds as for any satisfied
cube. The cube is written into a preallocated buffer constraint of capacity
`vars` (as in the old code), so that it has a `Ref` and can be the starting
point of analysis without being stored.

Rules that later techniques rely on:

- the hitting set ranges over the *current irredundant* clauses. Any pass that
  changes the irredundant clause set must keep it truth-equivalent to the
  input in the sense of section 11.1; then the cube is an implicant of the
  current matrix and all reasoning stays sound;
- such a cube is not derivable in QLRUP (no proof for QDIMACS, as in the old
  solver). The `-trace` format records it as a step without premises;
- for QCIR input, INV-COMPLETE says this code is never reached. It is kept as
  a fallback when no proof is written (the hitting-set cube is valid for the
  clause encoding) and counted in `stats.modelcubes`; when a proof is written
  it is a fatal internal error (old behaviour), and a nonzero count on a QCIR
  run is to be reported in `STATUS.md` as a bug in whatever broke the
  invariant.

### 4.6 Reduction

`qreduce (lits, kind)` removes every secondary literal whose variable is
greater than the greatest primary variable in `lits` (all of them if there is
no primary literal). Applied: to every original constraint when it is added
(with a proof: the original is logged as given, the reduced constraint is
derived from it, the original is deleted), at the end of every analysis, and
to every resolvent or strengthened constraint produced by inprocessing.

Naming: the word "reduce" alone always means reduction of the learnt
database (`reduce.cpp`, as in CaDiCaL); universal/existential reduction is
`qreduce`.

### 4.7 The three modes

`--mode` selects propagation and learning; one value for the whole run.

| mode | propagation | conflict | analysis | proofs |
|---|---|---|---|---|
| 0 Q-resolution | a constraint with a single non-vanished literal propagates it if it is primary; the prefix is ignored (no reduction during propagation) | all literals vanished, **or** the single remaining literal is secondary; in the second case that literal is then assigned its vanishing value without a reason ("conflict completion"), so that every literal of the conflict is assigned | `analyze.cpp`: one pass over the trail, first-UIP with the extra condition that every *blocked* secondary literal can be reduced | yes |
| 1 QU-resolution | as mode 0, but a single remaining secondary literal is propagated as well (its reason is the constraint) | all literals vanished | `analyze_qu.cpp`; pivots may be secondary; switches kind when it meets a reason of the other kind | yes |
| 2 long-distance | prefix-aware: a constraint is unit when one primary literal is left and every unassigned secondary literal is to its right | no primary literal left non-vanished | `analyze_ldq.cpp`; resolvents may contain complementary secondary literals | no (not expressible) |

The three analyses share nothing but the tail in `learn.cpp`; they are ported
as they are in M1. Do not try to merge them.

---------------------------------------------------------------------------

## 5. Arena

### 5.1 Region allocator

`Arena` is MiniSat's `RegionAllocator<uint32_t>`: one contiguous buffer of
32-bit words, bump allocation, `Ref` = word offset (`enum class Ref :
uint32_t`, `Ref::none = UINT32_MAX`), growth by the factor 13/8 with overflow
check (out of memory is a fatal error, not an exception that is swallowed),
`free (words)` only adds to a `wasted` counter. References stay valid until
the next garbage collection; pointers into the arena (`Constraint &`) are
invalidated by *any* allocation, because the buffer may be reallocated. Rule:
never hold a `Constraint &` or a literal pointer across a call that can
allocate (`new_constraint`); hold the `Ref` and re-derive.

Why keep it instead of CaDiCaL's individually allocated clauses: constraints
that are visited together are adjacent in memory (5.3), references are four
bytes (so a watch is eight), and a full database scan is a linear walk. The
price, the 16 GB limit of 32-bit word offsets, is not a concern for this
benchmark set.

### 5.2 Constraint layout

```
word 0      size                         number of literals
word 1      bit field:
              kind       1   Clause / Cube
              redundant  1   learnt; may be deleted
              garbage    1   deleted, memory not yet reclaimed
              moved      1   relocated during GC; lits[0] holds the new Ref
              reason     1   protected in reduce (set only inside reduce)
              used       2   recently used in analysis (M2 tiers)
              keep       1   (M2) never reduce
              subsume    1   \
              vivify     1    > scheduling marks for inprocessing (M3+)
              vivified   1   /
              gate       1   belongs to a gate definition (M3+)
              glue      20   LBD, saturating
word 2,3    id                           64-bit proof id (two words)
word 4...   lits[size]
```

Sixteen bytes of header for every constraint. The id is stored inline and
always present: the old solver kept ids in a hash map keyed by `CRef`, which
has to be rebuilt at every garbage collection and costs a hash lookup per
antecedent during analysis; ids are also what makes log output and sort
orders stable across garbage collections. MiniSat's per-clause `activity`
float and the `abstraction` word are not kept (database reduction sorts by
glue and size; subsumption computes signatures in the occurrence pass).

`Constraint` is a non-copyable view type with accessors (`size ()`,
`lits ()` returning `std::span<Lit>`, `begin ()/end ()`, flag getters and
setters); nothing outside `constraint.hpp` does word arithmetic. Shrinking a
constraint in place (`shrink_constraint`) lowers `size` and accounts the
freed words as wasted. Because of that the arena cannot be walked linearly;
all iteration over constraints goes through the reference lists (4.3).

### 5.3 Garbage collection ordered by access

Deleting a constraint (`mark_garbage`) sets the bit, reports the deletion to
the proof, adds its words to `wasted`, and smudges its two watch lists
(section 6.2). Memory is reclaimed when `wasted > gcfrac% * size` at one of
the safe points (after `reduce`, after `collect`, at the end of an
inprocessing pass), never inside propagation or analysis.

`garbage_collect ()` copies the live constraints into a fresh arena of the
right size in this order:

1. all watch lists are cleaned (garbage entries dropped);
2. for every variable in order, for both signs, for both kinds, for every
   watch in the list: relocate the watched constraint if it has not moved yet
   (set `moved`, store the new `Ref` in the old `lits[0]`), and rewrite the
   watch's `Ref`;
3. reasons of the assigned variables;
4. the reference lists (`irredundant`, `redundant`, per kind), dropping
   garbage, relocating whatever has not been reached yet (unit constraints,
   the initial-cube buffer);
5. any `Ref` held by an inprocessing pass must not exist at this point:
   passes do not call the collector while they hold references (occurrence
   lists are rebuilt, not relocated).

Step 2 is the point of the design: the first time propagation walks the watch
list of a literal after a collection, the constraints it has to dereference
lie next to each other in memory, in list order. This is MiniSat's
`relocAll`, kept as it is. The variable order of step 2 is an option
(`--arenasort`: 0 = variable index as in miniQU, default in M1; 1 = decision
order, i.e. descending score, saved phase first, which is CaDiCaL's
`arenatype=3` idea and an M2 experiment).

---------------------------------------------------------------------------

## 6. Watches

### 6.1 Layout

```cpp
struct Watch { Ref ref; Lit blocker; };          // 8 bytes
```

`Watches` holds, for each kind, a vector of watch lists indexed by literal
(`std::vector<Watch>` per literal), a dirty flag per list, and the list of
dirty literals. `watches (kind, p)` is the list of constraints of that kind
to visit **when `p` becomes true**: clauses watching `~p`, cubes watching `p`
(in terms of 4.1: constraints in which a watched literal just vanished). A
constraint of size >= 2 watches its literals at positions 0 and 1, and each of
the two watches carries the other literal as blocker.

Clause and cube lists are separate arrays (as in miniQU) rather than one
interleaved list per literal: a propagated literal visits the clause list and
then the cube list, and each loop is specialised for its kind.

### 6.2 Blockers and lazy cleaning

Propagation of a watch first tests the blocker: if `kval (blocker) > 0` the
constraint is disabled and is not dereferenced. Otherwise the constraint is
loaded, the vanished literal is moved to position 1, position 0 is tested the
same way, and then positions 2.. are searched for a non-vanished replacement;
the watch is moved to the replacement's list, or the constraint is unit or
conflicting. This is the MiniSat loop, including copying the remaining
watches when a conflict stops the scan.

Detaching is lazy: deleting a constraint only marks the two lists it is
watched in as dirty ("smudge"). `watches.lookup (kind, p)`, the accessor
used by propagation, removes garbage entries from a dirty list before
returning it; `clean_all ()` does so for every dirty list and is called
before garbage collection. Garbage constraints keep their memory until
collection, so a stale watch can always be dereferenced safely. Strict
detaching (searching the list) exists for the rare case that a watched
literal of a live constraint changes outside propagation (strengthening in
watch mode); inprocessing passes that rewrite many constraints instead drop
all watches and reconnect (section 10.2).

### 6.3 Mode 2

Mode 2 keeps watches on a primary literal and on either another primary
literal or a secondary literal *to the left of* the watched primary (the
literals that can block it), and it moves watches of position 0 as well. It
therefore tolerates stale watch entries (a list entry whose constraint no
longer has that literal at position 0 or 1) and skips them. This is the old
`propagateLDQ` and is ported unchanged; the stale-entry tolerance is confined
to `propagate_ldq.cpp`.

---------------------------------------------------------------------------

## 7. Search

### 7.1 Loop

```
solve ():
  init limits, heaps, initial-cube buffer; if the input already decided it, done
  (M3+) preprocess ()
  loop:
    if      conflict = propagate ()           analyze (conflict)   // may end the search
    else if terminated or limit hit           return unknown
    else if restarting ()                     restart ()
    else if (M2) rephasing () / switching ()  rephase () / switch_mode ()
    else if reducing ()                       reduce ()
    else if (M3) inprocessing ()              inprocess ()
    else if !decide ()                        // no eligible decision variable
        conflict = initial_cube ()            // 4.5; then analyze
```

Each `...ing ()` predicate compares a counter with a threshold in `lim`
(9.4); each action updates its threshold. `analyze` dispatches on the mode,
and ends in `learn.cpp` with one of: a learnt constraint (backjump, attach,
assign the asserting literal with the new constraint as reason), a learnt
dependency (backtrack, record), or the empty constraint (`Clause` kind:
false, `Cube` kind: true).

### 7.2 Assignment and propagation

`Var` data: `level`, `reason` (`Ref::none` for decisions and completed
conflicts), `trail` position. The kind of a reason is read from the
constraint. The trail is one vector with `control` entries per decision
level. `propagated` is the trail index up to which both kinds have been
propagated; vivification (which propagates one kind only) saves and restores
it explicitly.

`propagate ()` returns a conflict as `Ref` (kind read from the constraint).
For each trail literal it runs the clause loop and then the cube loop, as
described in 6.2 and 4.7. Counting: `stats.propagations` per trail literal,
and `stats.ticks` approximating cache lines touched (one per watch list, one
per dereferenced constraint), which is the unit in which inprocessing effort
is budgeted (10.1).

### 7.3 Decisions

Without dependency learning decisions follow the prefix: the current block is
the first one with `unassigned > 0`, and there is one score heap per block
(a variable becomes eligible when all decision variables of earlier blocks of
the other quantifier are assigned; since blocks are filled in order this is
automatic, but the eligibility test is kept as an assertion). With dependency
learning there is a single heap and a variable is eligible when its watched
dependency (7.4) is assigned. Gate variables, fixed and eliminated variables
are never in a heap and are not counted in `unassigned`.

Scores are EVSIDS (`bump.cpp`): bump by an increment that grows by
`1/decay` per conflict, rescale on overflow. Phase: saved phase, initial
phase false (the old default). M2 may add a VMTF queue per block and
alternative phases; `decide.cpp` is the only place that reads them.

### 7.4 Dependency learning

`--dl`: decisions may be made in any order. `depend.cpp` owns, per variable,
the list of variables it has been learnt to depend on, with the first entry
acting as a watch: the variable is eligible for decision only when the watched
dependency is assigned; when a watched variable gets assigned the list is
searched for another unassigned dependency (two-watched-literal style, one
watch), processed lazily from a second trail head before each decision. When
analysis has to resolve away a decision (a variable decided too early), it
reports a dependency instead of a constraint; `learn.cpp` records it and
backtracks below that decision. Dependencies are reset periodically (old
schedule: every 20th restart) and must be reset whenever a decision variable
is eliminated or fixed by inprocessing. They are heuristic information only:
soundness never rests on them.

### 7.5 Analysis and learning

`analyze.cpp` (mode 0) is the algorithm documented in `README.md`
("Conflict analysis") and in the old `Solver::analyzeQ`: resolve primary
literals in reverse trail order until one is alone on its level and to the
left of every blocked secondary literal, then keep resolving the primary
literals to the right of the leftmost blocked literal; a decision in the way
becomes a learnt dependency. The antecedent ids are collected in resolution
order in `chain` (only when a tracer is connected); that order is what the
QLRUP checker replays.

`learn.cpp`: minimisation (if enabled), `qreduce`, placing the asserting
literal at position 0 and a literal of the backjump level at position 1,
glue, proof step, allocation, watches, backjump, assignment, score decay.
The old code disabled minimisation when writing proofs because the chain did
not cover the removed literals; M2 fixes that (ROADMAP).

Root-level literals are kept in learnt constraints in M1 as in the old code.
M2 may resolve them away when their reason has the same kind (adding the unit
ids to the chain); a root literal whose reason has the other kind must stay
(INV-DERIVED).

---------------------------------------------------------------------------

## 8. Proofs

### 8.1 Interface

```cpp
class Tracer {                       // all literals are signed proof numbers
public:
  virtual ~Tracer () = default;
  virtual void add_original (uint64_t id, Kind, int gate, std::span<const int> lits) = 0;
  virtual void add_derived  (uint64_t id, Kind, std::span<const int> lits,
                             std::span<const uint64_t> chain) = 0;
  virtual void delete_constraint (uint64_t id, Kind, std::span<const int> lits) = 0;
  virtual void conclude (Kind empty_kind, uint64_t id) {}
  virtual void flush () {}
};
```

`Proof` is the single object `Internal` holds (`Proof *proof`, null when
nothing is connected; the call sites are `if (proof) proof->...`). It
translates internal literals to proof numbers, forwards to every connected
tracer, and offers the composite operations the solver needs so that call
sites stay one line:

- `add_original (c, gate)`; `add_derived (c, chain)`;
  `add_derived_empty (kind, chain)`
- `delete_constraint (c)`
- `strengthen (c, new_lits, chain)`: derive the shortened constraint under a
  fresh id, delete the old id, store the new id in `c`
- `flush ()`, `conclude (kind)`

Ids are allocated by `Internal` (`next_id`, starting at 1) for every
constraint whether or not a proof is written. Tracers shipped: `QlrupTracer`
(text/binary, `doc/proof-format.md`), `TraceTracer` (old `-trace` format),
`Checker`.

`Checker` replays every derived step exactly as the format defines it (chain
of resolutions with at most one clashing literal, then reduction; on failure
the variant with reduction after every step), checks that every referenced id
is live and of the right kind, and aborts with the offending step. It cannot
validate original steps against the circuit (the Lean checker does). It is on
by default in `debug`/`asan` builds whenever no QLRUP file is requested, so
that every fuzz run exercises proof generation, and is available as `--check`
in all builds.

### 8.2 Where steps are logged

| event | file | step |
|---|---|---|
| original constraint added | `constraint.cpp` via `External::add_original` | `o id kind gate lits` exactly as given by the encoder (duplicates removed); tautological clauses / contradictory cubes are skipped without a step |
| reduction of an original | same | derived from the original's id alone; original deleted |
| two complementary unit originals | same | empty constraint from the two ids |
| learnt constraint | `learn.cpp` | derived, chain = conflict id, then reason ids in resolution order (plus, from M2, the reasons used by minimisation) |
| final empty constraint | `learn.cpp` | derived with empty literal list |
| initial cube from a model | `model.cpp` | not expressible: fatal error if a QLRUP tracer is connected; `TraceTracer` gets a step with an empty chain |
| learnt constraint deleted | `reduce.cpp` -> `mark_garbage` | `d id` |
| satisfied constraint removed at root | `collect.cpp` -> `mark_garbage` | `d id` |
| root-vanished literals removed | `collect.cpp` | `strengthen`, chain = constraint id, then the unit ids (only literals whose root reason has the same kind) |
| BVE resolvent | `elim.cpp` | derived, chain = the two parent ids |
| BVE parents removed | `elim.cpp` | `d` |
| subsumed constraint removed | `subsume.cpp` | `d` |
| strengthening by self-subsumption | `subsume.cpp` | `strengthen`, chain = strengthened id, subsuming id |
| vivified constraint | `vivify.cpp` | `strengthen`, chain = the constraint/conflict id and the reason ids in reverse trail order |

`mark_garbage` is the only function that emits deletions, so no deletion can
be forgotten. Proof files are written through a 1 MiB buffer and flushed at
`conclude` and on termination signals.

Proof support matrix: QCIR input, modes 0 and 1, with or without `--dl`.
Requests outside it (QDIMACS input, mode 2) are rejected at start-up with the
old error message.

---------------------------------------------------------------------------

## 9. Options, statistics, limits, messages

### 9.1 Options

All solver options are integers in one X-macro table, as in CaDiCaL:

```cpp
// name, default, low, high, description
#define OPTIONS \
OPTION (mode,        0, 0, 2,   "0=Q-resolution, 1=QU-resolution, 2=long-distance") \
OPTION (dl,          0, 0, 1,   "dependency learning") \
OPTION (ccminmode,   0, 0, 3,   "learnt constraint minimisation") \
...
```

`options.hpp` expands it into `struct Options { int mode; ... }`, a table
for parsing and `--help`, and range checks. Fractions are integers in percent
or per mille (`vardecay=950`). Every heuristic constant is an option; no
magic numbers in technique files.

Command line: `--name=value`, `--name` (set to 1), `--no-name` (set to 0);
for compatibility with the old binary and the existing scripts a single
leading dash is accepted and hyphens inside a name are ignored, so
`-proof-binary`, `-no-dl`, `-ccmin-mode=3`, `-early-tseitin`, `-verb=0`
keep working. Non-integer arguments are application arguments, not options:
`--proof=FILE`, `--trace=FILE`, the input file. Unknown options are errors.

Options that exist from M1 (old names; defaults as in the old solver):
`mode dl cert qcir earlytseitin verb ccminmode legacyanalyze phasesaving
luby rfirst rinc vardecay gcfrac minlearnts proofbinary cpulim memlim`, plus
`check`, `log`, `arenasort`, `seed`. The old `cla-decay`, `rnd-freq`,
`rnd-init` are dropped (constraint activities and random decisions are not
ported).

### 9.2 Statistics

`struct Stats` contains plain `int64_t` counters grouped by technique
(`conflicts`, `decisions`, `propagations`, `ticks`, `restarts`,
`learned[kind]`, `learnedlits[kind]`, `minimized`, `dependencies`,
`reductions`, `reduced[kind]`, `collections`, `modelcubes`, and per pass:
rounds, tried, successful, removed literals...). They are incremented
directly (`stats.conflicts++`) and printed in one place (`stats.cpp`) at
verbosity >= 1, each line prefixed with `c `. Current database sizes are
maintained in `constraint.cpp`.

### 9.3 Profiling

`START (name)` / `STOP (name)` around phases (`parse`, `search`,
`propagate`, `analyze`, `reduce`, `collect`, `elim`, `subsume`, `vivify`),
defined by an X-macro list with a level per profile; active profiles at or
below `--profile=<level>` are timed (process CPU time), nested as in CaDiCaL,
and printed with the statistics. Level 0 costs nothing in the inner loop.

### 9.4 Limits

`struct Limit` holds the conflict (or tick) count at which each scheduled
event fires next (`restart`, `reduce`, `rephase`, `stabilize`, `inprocess`,
per-pass thresholds), plus user limits (`conflicts`, `decisions`, time via an
alarm flag). `struct Inc` holds the growing intervals. `struct Last` records
counters at the last run of each pass (to compute "effort since then").
Events are only ever triggered by comparing `stats` with `lim` in the loop of
7.1; no technique schedules itself from inside another.

### 9.5 Messages and logging

- stdout carries only: comment lines prefixed `c `, the result line
  (`SATISFIABLE` / `UNSATISFIABLE` / `INDETERMINATE`, as the old binary and
  the harness expect), and the `V ... 0` line of `--cert`. Exit code 10 /
  20 / 0. Errors go to stderr with exit code 1.
- `MSG`, `VERBOSE (level, ...)`, `PHASE (name, count, ...)` for progress
  output controlled by `--verb`.
- `LOG (...)` and `LOG (ref, ...)` (prints the constraint with id, kind,
  and every literal as quantifier, user number, value and level) exist only
  when compiled with `MINIQU_LOGGING` and print when `--log` is set. They
  replace the old `#ifndef NDEBUG printf` blocks, which made debug builds
  unusable. A debug build is silent unless `--log` is given.

### 9.6 Contracts and assertions

`REQUIRE (cond, message)` guards every public API function (state, argument
ranges, prefix order of declarations) and is active in all builds: a
violation is the caller's bug and aborts with the message. `assert` guards
internal invariants and is compiled out in `release`. Heavier checks
(`check_invariants ()`, watch consistency, heap consistency, no garbage
referenced) run at root level in debug builds, after every pass.

---------------------------------------------------------------------------

## 10. Inprocessing framework (M3+)

### 10.1 Scheduling

Passes run only at decision level 0 with propagation complete. Two entry
points:

- `preprocess ()`: before search, up to `--preprocessrounds` rounds of the
  enabled passes;
- `inprocess ()`: from the search loop when `stats.conflicts >=
  lim.inprocess`; the interval grows (arithmetically by default) so that the
  total inprocessing cost stays a bounded fraction of search.

Each pass has an **effort budget** in ticks: `effort = (search ticks since
the pass last ran) * <pass>effort / 1000`, clamped to `[mineffort,
maxeffort]`; the pass counts its own ticks (occurrence list traversals,
constraint visits, propagations) and stops when the budget is used up,
leaving its schedule marks in place so that the next round continues where it
stopped. A pass that achieved nothing delays its next run (CaDiCaL's `delay`).

A pass is a member function `bool Internal::<pass> ()` in its own file that:
(1) checks its option and preconditions, (2) `START`s its profile,
(3) enters occurrence mode if it needs it, (4) works within its budget,
(5) leaves occurrence mode, propagates new units to fixpoint, (6) updates
stats/limits, `STOP`s, runs `check_invariants ()`, and reports whether it
changed anything. `inprocess.cpp` only orders the passes; it contains no
technique logic.

### 10.2 Occurrence mode

Occurrence-based passes (elimination, subsumption, blocked constraints) do not
maintain watches. `enter_occurrence_mode ()` clears all watch lists and builds
`occs (kind, lit)`: the list of `Ref`s of the non-garbage irredundant
constraints of that kind containing the literal (redundant constraints are
connected only when the pass asks for them). `leave_occurrence_mode ()`
drops the occurrence lists, removes satisfied constraints and vanished
literals, and re-attaches watches for every live constraint; if a unit or an
empty constraint appeared it is handled there. Within occurrence mode, new
root units are propagated over occurrence lists (`propagate_occs`), not
watches. The arena may not be collected in occurrence mode.

Rebuilding the watches changes the order of the watch lists and therefore the
ideal arena layout, so `leave_occurrence_mode ()` triggers a garbage
collection (5.3) when the pass changed the database.

### 10.3 Variable status

`flags.hpp`: per variable a status `Active | Fixed | Eliminated |
Substituted | Pure` and scheduling marks (`elim`, `subsume`, ... : "some
constraint of this variable changed since the pass last looked"). Only
`Active` variables may occur in live constraints (after `collect`), be
decided, or be candidates. Leaving `Active` updates the block's `unassigned`
counter and the heaps in one function (`mark_eliminated` etc.); forgetting
this makes the solver wait forever for a variable that will never be
assigned.

**Frozen** variables are never eliminated or substituted. A variable is
frozen if the app says so through `Solver::freeze`. What is frozen by
default:

- nothing, in principle; the side conditions of each technique (ROADMAP)
  already exclude what must not be touched (for QCIR input they exclude all
  input variables, because those occur in both databases);
- outermost-block decision variables are frozen while `--cert` is given
  **until** the extension stack (10.4) has been validated by the certificate
  tests; after that the freeze is removed.

Gate variables are ordinary variables for inprocessing (they are the main
targets), with one privilege: they are never part of any output.

### 10.4 Extension stack and certificates

`--cert` prints the values of the decision variables of the outermost block
at the moment the search ended (for a true formula with an outermost
existential block this assignment satisfies the formula; dually for a false
formula with an outermost universal block). Derivation-based reasoning never
needs a full model, so the only thing reconstruction has to restore is this
one block. (Known wrinkle inherited from the old solver: with `--dl` the
block may be only partially assigned when the search ends, and the old binary
prints unassigned variables as positive literals. M1 keeps the output format
and adds a certificate test; see ROADMAP M1 for how the gap is handled.)

`External` keeps an **extension stack** as in CaDiCaL's `extend.cpp`,
generalised by kind: when a variable of the certificate block is eliminated,
the constraints containing it are pushed, each with its witness literal (the
literal of the eliminated variable). At the end, `extend ()` walks the stack
backwards over the certificate assignment: for a clause entry, if no literal
of the clause is true, the witness is set true; for a cube entry (an
eliminated universal variable), if no literal of the cube is false, the
witness is set false. The rightmost condition of elimination guarantees that
every other variable in a pushed constraint belongs to the same block, so its
value is known (already printed or reconstructed later in the backward walk).
Eliminated variables outside the certificate block push nothing. Variables
fixed at root keep their value on the trail and need no entry.

The same stack serves later techniques that remove variables (equivalent
literal substitution pushes the two binary constraints; blocked constraints
push themselves with the blocking literal).

### 10.5 Interaction with the rest of the solver

- Learnt constraints containing an eliminated variable are deleted by the
  pass (they are redundant). Learnt constraints never reintroduce an
  eliminated variable, because it is unassigned forever and occurs in no
  live constraint.
- Dependencies are reset when a decision variable leaves `Active`.
- The initial-cube buffer and `model.cpp` only look at live irredundant
  clauses, so they follow the database automatically.
- Mode 2 learnt constraints (with complementary literals) are never used as
  resolution partners by inprocessing; passes skip them.

---------------------------------------------------------------------------

## 11. Soundness framework for database transformations

Every technique in the ROADMAP is classified by what it does to the
databases, because that decides both its side conditions and its proof story.

### 11.1 What must be preserved

The solver's answer is justified by a derivation: the empty clause from the
clause database (false), or the empty cube from the cube database (true).

- For **QCIR** input the two databases are independent encodings of the same
  circuit; by INV-DERIVED every stored constraint has a QLRUP derivation from
  the original encoding of its kind. So *any* answer the solver gives is
  correct, whatever heuristics or simplifications ran. What a transformation
  can break is **termination** (INV-COMPLETE: the solver reaches a state with
  neither kind in conflict) and performance, never the verdict, as long as
  INV-DERIVED holds.
- For **QDIMACS** input, cubes start from satisfying assignments of the
  current irredundant clauses. A transformation of the irredundant clause set
  from `F` to `F'` (with the prefix restricted to the remaining variables) is
  admissible if (a) the two QBFs have the same truth value, (b) every stored
  cube remains an implicant of `F'` (or is deleted), and (c) every stored
  learnt clause is implied, in the QBF sense, by the new formula (or is
  deleted). Equivalence-preserving rewrites (subsumption, strengthening,
  vivification) satisfy this trivially; elimination satisfies it under its
  side conditions (ROADMAP M3 gives the argument).

### 11.2 Classes

- **(D) Derivational**: adds constraints that are resolvents (plus reduction)
  of stored constraints of the same kind, and/or deletes constraints. QLRUP
  expresses it today: derived steps and deletions. Examples: learning,
  minimisation, vivification, strengthening, BVE resolvents, failed-literal
  units.
- **(R) Removal**: deletes irredundant constraints that are not implied by the
  rest in the propositional sense (BVE parents, blocked constraints). In the
  proof a deletion is always legal. The obligations are 11.1(a)-(c) for
  QDIMACS and INV-COMPLETE for QCIR; they are side conditions of the solver,
  not of the proof.
- **(N) Non-derivational**: adds a constraint or an assignment that is not a
  resolvent (pure literals, universal expansion, definitions, anything that
  changes the prefix). Not expressible in QLRUP. Such a technique is either
  disabled when a proof is requested, or needs a checker extension approved by
  the coordinator (with complete Lean soundness proofs).

The header comment of every technique file states its class, its side
conditions, and its proof steps.

---------------------------------------------------------------------------

## 12. Style

"CaDiCaL style" here means:

- one technique per translation unit, named after the technique; `Internal`
  as the shared state; small functions with names that read as the algorithm
  (`restarting ()` / `restart ()`, `reducing ()` / `reduce ()`,
  `mark_garbage`, `protect_reasons`);
- `snake_case` for functions and variables, `CamelCase` for types,
  `UPPER_CASE` for macros and X-macro tables only; file names lower case;
- every `.cpp` starts with a comment block that explains the technique, its
  QBF side conditions, its soundness class (11.2) and its proof steps; inside,
  comments explain *why*, not what;
- options, statistics, profiles and limits are declared in their tables and
  nowhere else; scheduling is by limits compared in the main loop;
- cheap always-on statistics; `LOG` at every state change worth following;
  `PHASE` lines for every scheduled pass;
- assertions for internal invariants, `REQUIRE` for API misuse; internal
  checking (`Checker`, `check_invariants`) as first-class code.

"Modern C++" here means: strong types for `Lit`, `Ref`, `Kind`, `Quant`;
`enum class`; `std::span` for literal ranges and `std::vector` for all
containers outside the arena (no home-grown `vec`); `constexpr` instead of
macros for constants; RAII for files and timers; `[[nodiscard]]` on functions
whose result must be checked (`propagate`, `add_*`); no owning raw pointers,
no `new`/`delete` outside `arena.cpp`; no exceptions in the solver (fatal
errors terminate through `fatal ()`), no RTTI use, no iostreams in hot or
library code (the app may use them for parsing diagnostics); templates only
where they remove duplicated hot code (the kind-generic loops), not for
configurability.

Where **not** to imitate CaDiCaL:

- no individually allocated clauses, no pointer watches, no 16-byte watches:
  the arena and 8-byte watches stay (owner requirement);
- no signed-`int` literals inside the solver;
- no incremental machinery (assumptions, constraint, freeze/melt counting,
  restore, tainting), no `External` propagator, no IPASIR, no local search,
  no `mobical`; the `External` layer is deliberately thin;
- no several-thousand-line `internal.hpp` with inline everything: inline only
  what profiling shows hot (`val`, `kval`, `assign`, watch access);
- no macro-generated control flow beyond the tables and `LOG`/`START`
  families; no `goto` (the old analysis uses it; restructure when porting);
- CaDiCaL's GNU-style space before the call parenthesis is **not** adopted in
  code; `.clang-format` (LLVM base, 100 columns; `clang-format` 15 is
  installed) is the authority and a `ctest` test fails on unformatted files
  in `src/` and `test/unit/`. (The prose of these documents writes `f ()`
  only to mark something as a function.)

Process rules: no commented-out code; no dead options; every new technique
arrives with its option to switch it off, its statistics, its unit tests, a
fuzz configuration in `tests/regress.sh`, and a benchmark ablation.
