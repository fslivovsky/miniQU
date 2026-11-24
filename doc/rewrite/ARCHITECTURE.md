# miniQU rewrite: architecture

Status: target design, written before any code exists. Owner: coordinator.
Revision 2 (after review 00): section 13 lists what changed and why.
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

  Usage: `taskset -c 0-47 cmake --preset release && taskset -c 0-47 cmake
  --build --preset release -j16` (lower half of the cores, here 0-47 of 96;
  timed benchmarks use the upper half). Targets: `miniQU` (binary), `miniqu`
  (static library), `qlrup-trim`, `unit-tests` (all unit test executables),
  and `ctest --preset <p>` runs them plus a 20-seed fuzz (from M1-T05 on; in
  M1-T02 ctest runs the unit tests and the `format` test). Presets also
  include `release-clang` (release with `clang++`, to keep the code
  warning-free under both compilers). The asan preset links the sanitizer
  runtimes through a directory of soname symlinks that `CMakeLists.txt`
  creates in the build tree (GCC 11 on this machine installs
  `libasan.so.6.0.0` without the `libasan.so.6` link).
- Until the M1 parity gate the root `CMakeLists.txt` still builds the old
  solver, under the target name `miniQU-old` (its flags are untouched and
  `-Werror` does not apply to it); the last M1 task removes that target, after
  which the old tree is buildable only through its own `Makefile`. The frozen
  baseline binary in the work directory is the reference throughout.

---------------------------------------------------------------------------

## 3. Module map

One namespace, `miniqu`. Four layers above the base; each depends only on the
ones below it, and there is no pointer from a lower layer to a higher one:

```
 app        app.cpp  signal.cpp  resources.cpp
              |            (owns: argv, files, names of QCIR identifiers, output)
 frontend   parse_qcir.cpp  parse_qdimacs.cpp  circuit.{hpp,cpp}  encode.cpp
              |            (owns: the circuit, gate numbers, polarities, depths)
 API        miniqu.hpp  solver.cpp           class Solver (pimpl): contracts,
              |                              call-order state, user variable
              |                              numbers <-> internal variables
 internal   internal.hpp + one .cpp per technique (below)
              |
 base       arena  constraint  watch  heap  ema  options  stats  profile
            limit  logging  message  file  util  random  contract
```

There is **no `External` class** (CaDiCaL has one because of incremental
solving, compaction and the external propagator; none of that exists here).
What CaDiCaL's `External` would do is split as follows:

- `Solver` (`solver.cpp`) owns the two arrays that map user variable numbers
  to internal variables and back, checks the contracts, and translates
  literals on the way in (`add_var`, `add_original`, `freeze`) and on the way
  out (`val`, `certificate`). It contains no solver logic. Internal variables
  are created in the order of the `add_var` calls, which is prefix order
  (4.2), so the map is a renumbering and nothing else.
- Everything that needs solver state lives in `Internal` and is expressed in
  internal literals: the extension stack and reconstruction (`extend.cpp`,
  10.4), the certificate values (`certificate.cpp`), frozen marks
  (`flags.hpp`).
- The **proof number** of a variable (4.4) arrives through `add_var` and is
  stored with the per-variable static data in `prefix.hpp`. It is written
  once when the variable is created and read only by `Proof` (which holds a
  pointer to `Internal`, same layer) and by `LOG`.

`struct Internal` (`internal.hpp`) holds the whole solver state as plain data
members; the technique files implement its member functions. This is CaDiCaL's
structure and the reason it works is discipline, not encapsulation: a
technique file may *read* everything but *writes* only the state it owns or
state it changes through the owner's functions (e.g. constraints are created
and deleted only through `constraint.cpp`, assignments only through
`assign`/`backtrack`). The tables list owners; 3.6 says how the rule is kept.

### 3.1 Base

| file | contents |
|---|---|
| `lit.hpp` | `Var`, `Lit`, `Kind`, `Quant`; conversions; no solver state |
| `arena.{hpp,cpp}` | `Arena`: region of 32-bit words, `Ref`, alloc/free accounting, `moveTo` |
| `constraint.hpp` | `Constraint` header layout and accessors (section 5.2) |
| `watch.hpp` | `Watch`, `Watches` (lists per literal and kind, dirty flags, lazy cleaning) |
| `heap.hpp` | indexed binary max-heap on variable scores; a heap may start at a variable offset (one heap per block) |
| `ema.hpp` | exponential moving average with bias correction |
| `options.{hpp,cpp}` | X-macro option table (section 9.1) |
| `stats.{hpp,cpp}` | counters and their printing (9.2) |
| `profile.{hpp,cpp}` | `START`/`STOP` timers (9.3) |
| `limit.hpp` | `Limit` (next-event thresholds), `Inc` (increments); `Last` from the first package that reads it (9.4) |
| `logging.{hpp,cpp}`, `message.{hpp,cpp}` | `LOG`, `PHASE`, `VERBOSE`, `MSG`, `fatal` (9.5); `logging.cpp` also defines `Internal::log` (the one base file that includes `internal.hpp`, as in CaDiCaL, and only with `MINIQU_LOGGING`) |
| `contract.hpp` | `REQUIRE` for API misuse (9.6) |
| `file.{hpp,cpp}` | buffered input (plain/gzip via zlib), buffered output |
| `util.hpp`, `random.hpp` | small helpers; PRNG |

### 3.2 Internal: search

| file | owns / implements |
|---|---|
| `internal.{hpp,cpp}` | `Internal` state, construction, `solve ()`, the CDCL loop (section 7.1) |
| `prefix.{hpp,cpp}` | quantifier blocks, per-variable `Quant`/depth/flags/proof number, `qreduce` (4.2, 4.6) |
| `constraint.cpp` | `new_constraint`, `mark_garbage`, `shrink_constraint`, attach/detach, the constraint lists |
| `assign.cpp` | `assign`, `Var` data (level, reason, trail position) |
| `propagate.{hpp,cpp}` | the one watch loop (template) and its instances for modes 0 and 1 (7.2) |
| `propagate_ldq.cpp` | propagation for mode 2 (7.2) |
| `check.cpp` | `check_invariants ()` (4.3, 9.6) |
| `backtrack.cpp` | `backtrack (level)`, phase saving, heap re-insertion |
| `decide.cpp` | block selection, eligibility, `decide ()` (7.3) |
| `depend.cpp` | dependency learning: dependency lists, their watches, reset (7.4) |
| `analyze.cpp` | Q-resolution analysis (mode 0, default) (7.5) |
| `analyze_qu.cpp` | the older level-by-level analysis: mode 1, and mode 0 with `--legacyanalyze` |
| `analyze_ldq.cpp` | long-distance analysis (mode 2) |
| `learn.cpp` | common tail of the analyses: minimise, reduce, backjump level, glue (stamp table), proof step, attach, assign; learning a dependency; the final empty constraint |
| `minimize.cpp` | learnt-constraint minimisation (`ccminmode` 1-3) |
| `model.cpp` | initial cube from a satisfying assignment (4.5) |
| `bump.cpp` | variable scores (EVSIDS) |
| `restart.cpp` | Luby and (M2) EMA restarts, trail reuse |
| `reduce.cpp` | learnt-database reduction (the *database* sense of "reduce"): conflict and size triggers, tier-aware candidate selection |
| `tier.cpp` | `used` marks and glue update of learnt constraints bumped by an analysis (M2-T2); usage histogram and tier limit recomputation (M2-T3) |
| `rephase.cpp`, `mode.cpp` | not built; rephasing and stable/focused switching are deferred to M5+ (ROADMAP M2 execution plan) |
| `simplify.cpp` | root-level simplification of the databases (M2-T4, ROADMAP M2.1): units materialised, root-vanished literals removed, root-disabled constraints deleted, modes 0 and 1 |
| `collect.cpp` | arena garbage collection (5.3) |
| `report.cpp` | progress lines |
| `certificate.cpp` | values of the certificate block in internal variables, for `--cert` (10.4) |

### 3.3 Internal: proofs

| file | contents |
|---|---|
| `tracer.hpp` | abstract `Tracer` (section 8) |
| `proof.{hpp,cpp}` | `Proof`: the one object the solver talks to; literal translation to proof numbers, fan-out to tracers |
| `qlrup_tracer.{hpp,cpp}` | QLRUP text and binary writer |
| `trace_tracer.{hpp,cpp}` | the older `-trace` format (also works for QDIMACS) |
| `checker.{hpp,cpp}` | online checker of derived steps, for debug/asan builds and `--check` (8.1) |

### 3.4 Internal: inprocessing (M3 and later)

| file | contents |
|---|---|
| `inprocess.cpp` | scheduling of passes, effort budgets, entering/leaving "occurrence mode" (10.1) |
| `flags.hpp` | per-variable status (active/fixed/eliminated) and scheduling marks |
| `occs.{hpp,cpp}` | full occurrence lists per literal and kind (10.2) |
| `elim.cpp` | bounded variable elimination (clause and cube distribution) |
| `extend.cpp` | extension stack in internal literals and reconstruction (10.4); only built with QDIMACS elimination (ROADMAP M3.6) |
| `subsume.cpp` | subsumption and strengthening |
| `vivify.cpp` | vivification of clauses and cubes |
| later: `block.cpp`, `probe.cpp`, `decompose.cpp`, `gates.cpp`, `expand.cpp` | see ROADMAP M5+ |

### 3.5 API, frontend, app

| file | contents |
|---|---|
| `miniqu.hpp`, `solver.cpp` | public `class Solver`: contracts, user <-> internal variable map, forwarding to `Internal`; `tracer.hpp`: the abstract `Tracer` (8.1) |
| `circuit.{hpp,cpp}` | prenex circuit in proof numbers: variables, blocks (adjacent equal quantifiers merged), AND/OR gates in one flat input array (xor/ite expanded), forward references resolved, cone-of-influence removal, polarities, gate depths |
| `parse.hpp`, `parse_qcir.cpp`, `parse_qdimacs.cpp` | parsers (character by character through `InputFile`); report errors with file and line number |
| `encode.{hpp,cpp}` | dual Plaisted-Greenbaum encoding of a `Circuit` into a `Solver` (4.4), and `encode_qdimacs`; uses only `miniqu.hpp` |

The frontend sources are the CMake object library `miniqu-frontend`, kept apart from the static library
`miniqu` so that unit tests link them against `test/unit/fake_solver.cpp` (a recording substitute for
`Solver`) and the app against the real solver. `encoding-dump` (`test/tools/`) prints what the frontend
passes to the fake solver; `tests/encoding_diff.sh` compares it with the original constraints in the
baseline's proofs.
| `app.cpp` | `main`: options, parsing, limits, signals, result line, exit code, `V` line |
| `signal.{hpp,cpp}`, `resources.{hpp,cpp}` | termination signals (8.2); CPU/memory limits and peak RSS. With `app.cpp` they form the target `miniQU` and are not part of the library |

The public API (`miniqu.hpp`) is small and single-shot. User variables and
literals are nonzero `int`s as in DIMACS:

```cpp
class Solver {
public:
  Solver ();  ~Solver ();
  bool set (std::string_view option, int value);       // before the first add_var; unknown name: REQUIRE
  // Formula, in this order: all variables (prefix order), then constraints.
  void add_var (int var, Quant, bool decision = true, int proof_number = 0);
  void add_original (Kind, std::span<const int> lits, int proof_gate = 0);
  void freeze (int var);                                // never eliminate
  void connect_tracer (std::unique_ptr<Tracer>);        // before add_original
  int solve ();                                         // 10 true, 20 false, 0 unknown
  int val (int var) const;                              // 1/-1 in the certificate block (unassigned: 1), else 0
  std::vector<int> certificate () const;
  void terminate ();                                    // async-signal-safe: sets a flag
  void flush_proof ();                                  // not async-signal-safe (8.2)
  void statistics () const;
private:
  struct Impl;                       // user<->internal maps, state, Internal
  std::unique_ptr<Impl> impl;
};
```

The class also befriends `Internal &internal_of (Solver &)`, defined in
`solver.cpp` and used only by white-box unit tests (an end-to-end test
propagates the state the real frontend built).

Consecutive `add_var` calls with the same quantifier form one block. QDIMACS
uses `add_var` + `add_original (Kind::Clause, ...)` only; the QCIR encoder
uses everything.

Dependency rules: nothing below `app` prints to stdout except through
`message.cpp`; nothing below `frontend` knows about identifiers or files
(the proof *file* is opened by the app and handed to a tracer); `Internal`
never sees user variable numbers and never calls into `Solver`; the frontend
uses only `miniqu.hpp`.

### 3.6 What "one technique, one file" means in practice

`Internal` is a shared state, so a technique is not a plug-in: adding one
touches a known, short list of places, and nothing else.

| touch point | what is added |
|---|---|
| `<technique>.cpp` | all of its logic, with the header comment of section 12 |
| `internal.hpp` | declarations of its member functions and **one struct member** holding its private state (below) |
| `options.hpp`, `stats.hpp`, `profile.hpp`, `limit.hpp` | its rows in the tables |
| `inprocess.cpp` (pass) or the loop in `internal.cpp` (search heuristic) | one call under its `...ing ()` predicate |
| `constraint.hpp` | a header bit, only if it needs one (5.2) |
| `tests/matrix.txt`, `test/unit/` | its configurations (normal and stress) with the counters that must be nonzero; unit tests |

State that belongs to one technique is grouped in a small struct defined next
to its declarations and held as a single member of `Internal`: `Depend
depend` (dependency lists, their watches and trail head), `Eliminator elim`
(schedule, bound, resolvent buffer), `Vivifier vivify`, `Tiers tiers`,
`Averages averages`, and so on. Loose fields in `Internal` are for state
shared by the core only (values, trail, levels, databases, watches, heaps).

A technique that needs an edit in `propagate.{hpp,cpp}`, `propagate_ldq.cpp`,
`analyze*.cpp`, `learn.cpp` or `assign.cpp` is a **design change**: the
worker records it in `STATUS.md` (what was changed in the core and why the
technique could not do without it) and the reviewer looks at it. This is the
rule reviewers apply; the ownership tables above are otherwise enforced by
nothing.

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
- variables are created only while the formula is being added; nothing in
  M1-M4 creates a variable later.

Per-variable static data (`prefix.hpp`): `Quant`, depth, the proof number
(4.4; 0 if the input has none), and flags `decision` (input variable, may be
decided), `gate` (Tseitin variable, never decided, never printed).
Per-variable dynamic status lives in `flags.hpp` (section 10.3).

### 4.3 Constraint databases

All constraints live in one arena and are referenced by `Ref`. There are two
lists of references per kind: `irredundant[kind]` (original, or derived and
required to keep the formula equivalent, e.g. BVE resolvents) and
`redundant[kind]` (learnt; may be deleted at any time). The bit in the
constraint header is authoritative; the lists exist for iteration.

Unit constraints are allocated like any other constraint (size 1, never
watched) and serve as the reason of their root-level assignment, so that
reasons and proof ids are uniform. A unit constraint is always flagged
irredundant, whatever produced it, and is **never deleted**: section 11.1
uses stored units to justify deleting other constraints. The empty
constraint is never allocated; deriving it ends the search.

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
- **INV-SANDWICH** (QDIMACS input, modes 0 and 1): with `G` the irredundant
  clauses, `L` the learnt clauses and `T` the stored cubes, `Π.(G ∧ ⋀L)` and
  `Π.(G ∨ ⋁T)` both have the truth value of the input. Defined and argued
  in 11.1; it is a semantic invariant and cannot be checked at run time, but
  its consequence "an initial cube hits every irredundant clause" is (8.1).

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
point of analysis without being stored. The buffer is in no constraint
list and is not watched (`Constraint::set_size` rewrites its size in
place, possibly to 0 for the empty cube), so the garbage collector must
relocate `model_cube` explicitly.

Rules that later techniques rely on:

- the hitting set ranges over the *current irredundant* clauses, unit clauses
  included, so the cube is an implicant of the current irredundant clause set
  `G`. That is all the cube is: it need not imply the input matrix, and
  older stored cubes need not imply the current `G`. Soundness rests on
  INV-SANDWICH (11.1), and any pass that changes `G` must satisfy the
  admissibility criterion (LO)/(HI) given there;
- with `--check` and in debug/asan builds, `model.cpp` verifies every initial
  cube before reduction against all live irredundant clauses
  (`check_model_cube ()`, a linear scan; fatal on a miss). This catches a
  cube taken from a clause set that some pass made too weak, the one
  QDIMACS failure no proof checker sees;
- such a cube is not derivable in QLRUP (no proof for QDIMACS, as in the old
  solver). Tracers receive it through `add_model_cube` (8.1); the `-trace`
  format records it as a step without premises;
- for QCIR input, INV-COMPLETE says this code is never reached. In M1 it is
  kept as the old solver has it: a fallback when no proof is written (for the
  untouched encoding the hitting-set cube is valid), a fatal internal error
  when a proof is written. From the first package that changes irredundant
  constraints (ROADMAP M2.1) there is no argument that such a cube is still
  valid next to the cube encoding (section 11.1 argues QDIMACS only), so from
  then on reaching this code on QCIR input ends the run with the answer
  "unknown" and an error message, proof or not. Every occurrence is counted
  in `stats.modelcubes`, and a nonzero count on a QCIR run is reported in
  `STATUS.md` as a bug in whatever broke the invariant.

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
word 0      bits 0-5   kind        1   Clause / Cube
                       redundant   1   learnt; may be deleted
                       garbage     1   deleted, memory not yet reclaimed
                       moved       1   relocated during GC; lits[0] holds the new Ref
                       reason      1   protected in reduce (set only inside reduce)
                       has_id      1   two id words follow the literals
            bits 6-31  size       26   number of literals (at most 67108863, as
                                       in the old solver; a larger constraint
                                       is a fatal error)
word 1...   lits[size]
then, only if redundant, one word:
            bits 0-13  glue       14   LBD, saturating
            bits 14-15 used        2   M2 (task M2-T2): 2 or 1 when learnt or
                                       used in an analysis, decremented by
                                       every reduce; 0 = deletion candidate
                                       (`used ()`, `set_used ()`, 0 for
                                       irredundant constraints)
            bits 16-31 reserved   16   (scheduling marks for M3+. A bit gets its
                                       name and its accessors in the package
                                       that first uses it.)
then, only if has_id, two words: the 64-bit proof id, low word first
```

This is MiniSat's and the old solver's layout: four bytes of header, the
literals, and optional trailing words. An irredundant constraint without a
proof is exactly as large as in the old solver (a binary original: 12
bytes); a redundant one is 4 bytes smaller (the old solver: `activity` and
`lbd`). `has_id` is set for every constraint allocated while a tracer is
connected (`Internal::proof != nullptr`; tracers are connected before the
first original, so one solver run has ids on all constraints or on none),
which includes the default `Checker` of builds with assertions. Without a
tracer nothing reads an id: `id ()` asserts `has_id`.

History, because the layout was measured twice. The first layouts had a
uniform header in front of the literals with the id always inline (16 bytes,
then 12 bytes after the measurement of task T07). T07 compared propagation
speed on an idle machine and found no difference. Review M1-r1 (B1) then
showed that under the benchmark protocol (one process per core, eight cores
sharing a 32 MB L3 cache) the 12-byte header costs 8-25% CPU time on
identical searches: the working set of propagation is the constraints
themselves, and the eight extra bytes per original no longer fit the cache
share of one process. Prototypes measured under that load (STATUS.md,
"M1 round 2: diagnosis of B1"): 12-byte header 1.08 times the baseline's CPU
time, 8-byte header 1.00, 4-byte header 0.96. **Layout decisions are
measured under benchmark load (`bench/load_measure.py`), never on an idle
machine.** The old solver's hash map from `CRef` to id is still not used:
trailing id words need no rebuild at garbage collection and no lookup
during analysis. Orders that must be stable across garbage collections use
the position in the reference lists (4.3), which is creation order, not the
id. MiniSat's per-clause `activity` float and the `abstraction` word are
not kept (database reduction sorts by glue and size; subsumption computes
signatures in the occurrence pass).

`Constraint` is a non-copyable view type with accessors (`size ()`,
`lits ()` returning `std::span<Lit>`, `begin ()/end ()`, flag getters and
setters); nothing outside `constraint.hpp` does word arithmetic or knows
where the trailing words are. Shrinking a constraint in place
(`shrink_constraint`) lowers `size`, moves the trailing words down and
accounts the freed words as wasted; garbage collection copies a constraint
word by word (`copy_constraint`), so no caller lists the fields. Because `redundant` decides whether the glue word exists, the flag cannot be changed in place: promoting a learnt constraint to irredundant (subsumption, BVE in M3) allocates a new constraint and marks the old one garbage. Because of the optional words the arena cannot be walked linearly;
all iteration over constraints goes through the reference lists (4.3).

### 5.3 Garbage collection ordered by access

Deleting a constraint (`mark_garbage`) sets the bit, reports the deletion to
the proof, adds its words to `wasted`, and smudges its two watch lists
(section 6.2). Memory is reclaimed when `wasted > gcfrac% * size` at one of
the safe points (after `reduce`, after root simplification (`simplify_root`,
unless it returns a root conflict), at the end of an inprocessing pass), never inside propagation or analysis. `--gcfrac=0`
collects at **every** safe point, even when nothing is wasted; the stress
configurations of the test matrix use it so that relocation runs on tiny
instances (ROADMAP 0.1).

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
5. the buffer of the initial cube (`model.cpp`) is allocated afresh in the new
   arena: its contents are dead between two cubes, only its id (if ids are
   stored) is kept;
6. any `Ref` held by an inprocessing pass must not exist at this point:
   passes do not call the collector while they hold references (occurrence
   lists are rebuilt, not relocated).

Step 2 is the point of the design: the first time propagation walks the watch
list of a literal after a collection, the constraints it has to dereference
lie next to each other in memory, in list order. This is MiniSat's
`relocAll`, kept as it is. The variable order of step 2 is an option
(`--arenaorder`: 0 = variable index as in miniQU, default in M1; 1 = decision
order, i.e. descending score, saved phase first, which is the idea of
CaDiCaL's `arenatype=3` and an M2 experiment. The option is not called
`arenasort` because CaDiCaL uses that name for something else).

---------------------------------------------------------------------------

## 6. Watches

### 6.1 Layout

```cpp
struct Watch { Ref ref; Lit blocker; };          // 8 bytes
```

`WatchList` is MiniSat's `vec` for watches: a pointer and 32-bit size and
capacity, 16 bytes, growing by about 3/2 with `realloc` (a `Watch` is
trivially copyable). `Watches` holds one 32-byte-aligned record per literal
with the two lists of that literal (one per kind), so the four list headers
of a variable share one cache line; the dirty flags of lazy cleaning are a
separate dense array of two bytes per literal, and per kind there is the
list of dirty literals.

History, because this layout was measured three times. Until M1-R2-T2 the
lists and flags were four separate arrays per kind. Round 2 put two
`std::vector<Watch>` (24 bytes each) and the flags into one 64-byte record
per literal, which `bench/load_measure.py` reported as a gain. Review M1-r2
(B1) showed with the benchmark placement (eight instances of one family on
the eight cores of one L3 cache) that this record costs 20-30% CPU time on
the DW family: the list headers are touched once per propagated literal, so
they are hot, and 64 bytes per literal are twice the old solver's two
16-byte `vec` headers (DW-unsat-09-22-1: 148000 literals, 9.5 MB against
4.7 MB, with a 4-MB share of the L3 cache per process). A prototype with the
layout above brought the reviewer's reproducer from 1.24 to 1.02 times the
baseline's CPU time (STATUS.md, "M1 round 3: diagnosis of B1"). **The size
of everything that is touched per propagated literal is compared with the
old solver's before it is changed, and measured with the benchmark
placement (`bench/l3.sh`, `bench/load_measure.py` with L3 groups).** The
records are allocated in one step for all
variables when the first constraint is added (`size_watches`), not grown
variable by variable, which would raise the peak memory. `watches (kind, p)` is the list of constraints of that kind
to visit **when `p` becomes true**: clauses watching `~p`, cubes watching `p`
(in terms of 4.1: constraints in which a watched literal just vanished). A
constraint of size >= 2 watches its literals at positions 0 and 1, and each of
the two watches carries the other literal as blocker when it is attached;
after propagation has moved watches, a blocker is still a literal of the
constraint other than the watched one, but not necessarily the other
watched literal (MiniSat does not update the blocker of the watch that
stays).

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
`propagateLDQ` and is ported unchanged, with one exception (M1-T09): when
the old position 0 comes back as position 1 the old code pushed a second
entry into a list that still held one; the port does not. Originals are
watched by their two leftmost literals, as in the old solver, which may
both be secondary (or a primary one with a secondary one right of it);
until a watch moves this can miss a unit or a conflict, never cause a wrong
one. The stale-entry tolerance is confined to `propagate_ldq.cpp`, except
that in mode 2 garbage collection removes garbage from *every* watch list
(a stale entry of a deleted constraint can sit in a list that deleting did
not smudge) and `check_invariants ()` accepts such entries and checks the
long-distance unit rule for constraints whose watches are as above.

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
    else if simplifying ()                    simplify_root ()  // M2.1; may end the search,
                                                                // assign root literals or
                                                                // return a root conflict
                                                                // (then analyze); an
                                                                // iteration of its own
    else if (M5+) rephasing () / switching () rephase () / switch_mode ()  // deferred
    else
        if retiering ()                       retier ()      // M2.2: tier limits per kind
        if reducing ()                        reduce ()      // then go on:
        if (M3) inprocessing ()               inprocess ()   // not an iteration
        if !decide ()                         // no eligible decision variable
            conflict = initial_cube ()        // 4.5; then analyze
```

`restart ()` (7.1, `restart.cpp`) backtracks to `reuse_level ()` instead of 0
(M2.5): the largest `k` such that the decision of each level `i <= k` has a
score not lower than the best unassigned variable of its heap (the heap of
its block, or the single heap with `--dl`); 0 with `--no-reusetrail` or when
a dependency reset is due, since the reset needs level 0. The criterion is a
heuristic (every backtrack level is sound); in prefix order it approximates
"the search would decide the same variables again". `restarting ()` follows
`--restartmode` (9.4): the old interval, or the glue averages of the kind
learnt last (M2.4); neither has proof steps. Root simplification needs level
0, which with reuse is reached mostly after learnt units, as in CaDiCaL;
reduction and garbage collection do not.

`simplify_root` is an iteration of its own: the root literals it assigns
must be propagated before the next decision, and a root conflict it finds
goes to `analyze`. `simplifying ()` needs root literals that the last run
did not see, so the loop cannot simplify again without progress.

`reduce` does not end the iteration. The old size trigger (`#learnt -
#assigned >= max_learnts`, now `--reducesize`, off by default since M2.2) can
stay true after a reduction (reasons and the better half survive), and the old
`search` decides right after `reduceDB`; ending the iteration would reduce
again before the next decision, forever. The conflict trigger cannot, since
`reduce` moves `lim.reduce`.

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
propagated completely (after a conflict it stays at the literal whose
propagation found it: the scan stops at the first conflict, so the cube loop
of that literal does not run); vivification (which propagates one kind
only) saves and restores it explicitly.

`propagate ()` returns a conflict as `Ref` (kind read from the constraint).
For each trail literal it runs the clause loop and then the cube loop, as
described in 6.2 and 4.7. Counting: `stats.propagations` per trail literal,
and `stats.ticks` approximating cache lines touched (one per watch list, one
per dereferenced constraint), which is the unit in which inprocessing effort
is budgeted (10.1).

**Propagation variants.** By M4 the solver propagates in six situations.
They differ in two things only: which kinds take part, and what happens to a
constraint whose single non-vanished literal is *secondary* (the "lone
secondary" rule):

| variant | used by | kinds | lone secondary literal | code |
|---|---|---|---|---|
| search, mode 0 | `propagate ()` | both | conflict, completed after the loop (4.7) | watch loop, `Lone::Conflict` |
| search, mode 1 | `propagate ()` | both | propagated | watch loop, `Lone::Propagate` |
| vivify, mode 0 | `propagate_kind (K)` | `K` only | ignored (ROADMAP M4, V2) | watch loop, `Lone::Ignore` |
| vivify, mode 1 | `propagate_kind (K)` | `K` only | propagated | watch loop, `Lone::Propagate` |
| search, mode 2 | `propagate_ldq ()` | both | prefix-aware unit rule, other watch invariant (6.3) | its own loop in `propagate_ldq.cpp` |
| occurrence mode | `propagate_occs ()` | both | root units only, no watches (10.2) | `occs.cpp` |

The MiniSat watch loop of 6.2 therefore exists **once**, as

```cpp
enum class Lone : uint8_t { Conflict, Propagate, Ignore };           // internal.hpp
template <Kind K, Lone R> Ref Internal::propagate_watches (Lit p);   // propagate.hpp
template <Lone R> Ref Internal::propagate_trail ();                  // both kinds, clauses first
```

with kind and rule as compile-time parameters (`kval` and the rule fold to
straight code in each instance). The functions in the table are thin drivers
in `propagate.cpp`: they select the instance **outside** the loop over the
trail (one `switch` on the mode per call, never per watch) and own everything
that is not the loop: the trail heads, conflict completion for mode 0, the
`ticks` accounting. Mode 2 and occurrence propagation are not instances of
the template, because their data structures differ; they must not grow a
third and fourth copy of the mode-0/1 logic either. A new variant is a new
row of this table and at most a new enumerator, and is a design change in the
sense of 3.6.

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
`1/decay` per conflict, rescale on overflow. Initial scores are 0 with
`--seed=0` (the default: the run is deterministic; equal scores are ordered
by the heap operations alone, exactly as the baseline's MiniSat heap with
its strict score comparison, so that an unseeded run follows the baseline's
search as far as the port is faithful: decision after M1 round 1, replacing
"ties are broken by variable index"); with `--seed=s`, `s > 0`, every variable starts with a
score drawn uniformly from `[0, 1e-5)` by the PRNG seeded with `s`. This is
the baseline's `-rnd-init -rnd-seed=s` and is the **only** thing the seed
changes: it perturbs the first decisions and thereby the whole search, which
is how the benchmark protocol measures search variance (ROADMAP 0.3). Phase:
saved phase, initial phase false (the old default). M2 may add a VMTF queue per block and
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
`analyze_ldq` places positions 0 and 1 itself and enters at
`learn_watched`; long-distance resolvents are never minimised (the old code
called minimisation only from the other two analyses), so `--ccminmode` has
no effect in mode 2.
The old code disabled minimisation when writing proofs because the chain did
not cover the removed literals. As built in M2-T5, minimisation runs alike
with and without a proof: with one, `minimize.cpp` appends to the chain of
the analysis the reasons of every variable it resolves away (the removed
literals and, transitively, the literals of their reasons that are neither
in the learnt constraint nor, with `ccminmode=3`, secondary), in reverse
trail order, found by a marking pass from the removed literals after the
decision (the argument that this is one QLRUP step, in either variant of
the format, is in the header of `minimize.cpp`). In mode 1, if minimisation
would remove every primary literal right of a secondary asserting literal,
the constraint is learnt unminimised (the reduction would drop the
asserting literal; the M1 port failed there, the old code kept the literal
unreduced). `stats.minimized` counts the literals minimisation removes
beyond those the following `qreduce` removes anyway, which is what the old
`conflict literals ... deleted` line measures; `stats.minimizedchain`
counts the reason ids appended.

Root-level literals are kept in learnt constraints in M1 as in the old code.
With `ccminmode >= 1` minimisation resolves them away when their reason is a
unit of the same kind (the unit id is appended like any reason); a root
literal whose reason has the other kind must stay (INV-DERIVED). As built in M2-T4, `simplify.cpp` removes root literals with
a same-kind unit from stored constraints at the next root simplification;
it replaces the reason of a root variable by the unit derived for it
(`replace_reason` in `assign.cpp`), which the analyses read like any other
reason.

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
  virtual void add_model_cube (uint64_t id, std::span<const int> lits) = 0;   // 4.5
  virtual void conclude (Kind empty_kind, uint64_t id) {}
  virtual void flush () {}
};
```

`Proof` is the single object `Internal` holds (`Proof *proof`, null when
nothing is connected; the call sites are `if (proof) proof->...`). It
translates internal literals to proof numbers, forwards to every connected
tracer, and offers the composite operations the solver needs so that call
sites stay one line:

- `add_original (id, kind, gate, lits)` (an original is logged as given,
  before reduction, so it is never a stored `Constraint`)
- `add_derived (c, chain)`, and `add_derived (id, kind, lits, chain)` for
  steps whose constraint is not stored: the reduction of an original and
  the empty constraint (empty `lits`)
- `delete_constraint (c)`, and the same with `(id, kind, lits)` for the
  original replaced by its reduction
- `strengthen (c, new_lits, chain)`: derive the shortened constraint under a
  fresh id (`next_id++`), delete the old id, store the new id in `c`; the
  M2 caller renumbers `c` the same way when no proof is written
- `add_model_cube (c)`, `flush ()`, `conclude (kind)` (called by
  `found_empty`; passes the id of the last empty constraint logged and
  flushes every tracer)

Ids are allocated by `Internal` (`next_id`, starting at 1) for every
constraint whether or not a proof is written; `new_constraint` takes the
id as an argument, and every initial cube gets a fresh one.  Literals are
proof numbers; a QDIMACS variable (`add_var` with proof number 0) has its
own number, so the trace and the `Checker` work for QDIMACS too. Tracers shipped: `QlrupTracer`
(text/binary, `doc/proof-format.md`), `TraceTracer` (old `-trace` format),
`Checker`.

`Checker` replays every derived step exactly as the format defines it (chain
of resolutions with at most one clashing literal, then reduction; on failure
the variant with reduction after every step), checks that every referenced id
is live and of the right kind, and aborts with the offending step. It cannot
validate original steps against the circuit (the Lean checker does). It is on
by default in `debug`/`asan` builds whenever the caller connected no tracer
(as built: "no QLRUP file" became "no tracer at all", since `Solver` cannot
tell tracers apart; `--check` adds it to any), so that every fuzz run
exercises proof generation, and is available as `--check` in all builds.
`Solver` connects it with the first original, when the prefix is complete;
it counts replayed steps in `stats.checked`. Since M2-T5 it is connected
whatever `ccminmode` is, and minimisation does not depend on it (7.5). Its scope by input and mode:

| | modes 0 and 1 | mode 2 |
|---|---|---|
| QCIR | every derived step replayed | `Checker` not connected (long-distance steps are not replayable); `--check` still runs `check_invariants ()` |
| QDIMACS | every derived step of both kinds replayed; an initial cube arrives through `add_model_cube`, is accepted as a premise-free cube and from then on is an ordinary live cube; that it hits every irredundant clause is verified by `model.cpp` (4.5), which has the clause lists | as QCIR mode 2, plus the initial-cube check of 4.5 |

`add_model_cube`: `QlrupTracer` reports a fatal error (not expressible),
`TraceTracer` writes a step without premises, `Checker` as in the table.
`TraceTracer` also writes original constraints as premise-free steps (the
old trace wrote none and numbered QDIMACS clauses by file position, which
the proof ids do not reproduce) and writes no deletions
(`trace_tracer.cpp`).

### 8.2 Where steps are logged

| event | file | step |
|---|---|---|
| original constraint added | `constraint.cpp` via `Solver::add_original` | `o id kind gate lits` exactly as given by the encoder (duplicates removed); tautological clauses / contradictory cubes are skipped without a step |
| reduction of an original | same | derived from the original's id alone; original deleted |
| two complementary unit originals | same | empty constraint from the two ids |
| learnt constraint | `learn.cpp`, `minimize.cpp` | derived, chain = conflict id, then reason ids in resolution order, then the reasons of the variables minimisation resolves away (including same-kind root units) in reverse trail order |
| final empty constraint | `learn.cpp` | derived with empty literal list |
| initial cube from a model | `model.cpp` | `add_model_cube`: fatal error if a QLRUP tracer is connected; `TraceTracer` writes a step without premises |
| root unit materialised (M2.1) | `simplify.cpp` | derived unit, chain = the non-unit reason id, then the same-kind unit ids of its other literals (in the order of the reason's literals); a secondary unit (mode 1) is the empty constraint |
| learnt constraint deleted | `reduce.cpp` -> `mark_garbage` | `d id` |
| satisfied constraint removed at root | `simplify.cpp` -> `mark_garbage` | `d id` (only under a literal with a unit of either kind) |
| root-vanished literals removed | `simplify.cpp` | `strengthen`, chain = constraint id, then the unit ids (only literals whose root reason is a unit of the same kind); a result of one literal is derived under a fresh id and the old id deleted by `mark_garbage` (one `a`, one `d`), an empty one is derived and ends the proof |
| BVE resolvent | `elim.cpp` | derived, chain = the two parent ids |
| BVE parents removed | `elim.cpp` | `d` |
| subsumed constraint removed | `subsume.cpp` | `d` |
| strengthening by self-subsumption | `subsume.cpp` | `strengthen`, chain = strengthened id, subsuming id |
| vivified constraint | `vivify.cpp` | `strengthen`, chain = the constraint/conflict id and the reason ids in reverse trail order |

`mark_garbage` is the only function that emits deletions, so no deletion can
be forgotten. Proof files are written through a 1 MiB buffer and flushed at
`conclude`. **Signal handlers write nothing**: the handler in `signal.cpp`
only calls `Solver::terminate ()`, which sets an atomic flag; the search loop
sees the flag and returns "unknown"; `app.cpp` then calls
`Solver::flush_proof ()`, prints statistics and exits. A second signal while
this is in progress terminates the process at once, without flushing (a
truncated proof of an unfinished run is worthless either way).

Proof support matrix: QCIR input, modes 0 and 1, with or without `--dl`.
Requests outside it (QDIMACS input, mode 2) are rejected at start-up with the
old error message. `--trace` in mode 2 is rejected too (M1-T09; the old
solver accepted it but traced no learnt constraint there, so the trace was
incomplete), and `Solver` refuses any tracer in mode 2 (`REQUIRE`).

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
or per mille (`vardecay=950`). Every heuristic constant that a milestone
tunes or ablates is an option; a constant ported unchanged from the old
solver and not yet touched (M1: the learnt-limit schedule in `reduce.cpp`,
the rescale threshold in `bump.cpp`) is a named `constexpr` at the top of
its technique file and becomes an option in the package that first changes
it (M2.2 for the reduce schedule). No unnamed magic numbers in technique
files.

Command line: `--name=value`, `--name` (set to 1), `--no-name` (set to 0);
for compatibility with the old binary and the existing scripts a single
leading dash is accepted and hyphens inside a name are ignored, so
`-proof-binary`, `-no-dl`, `-ccmin-mode=3`, `-early-tseitin`, `-verb=0`
keep working. Non-integer arguments are application arguments, not options:
`--proof=FILE`, `--trace=FILE`, the input file. Unknown options are errors.

Options that exist from M1 (old names; defaults as in the old solver):
`mode dl cert qcir earlytseitin verb ccminmode legacyanalyze phasesaving
luby rfirst rinc vardecay gcfrac minlearnts proofbinary cpulim memlim`, plus
`check`, `log`, `seed` (7.3); `arenaorder` arrives with its M2 experiment
(an option with a single legal value would be a dead option). The old `cla-decay` and
`rnd-freq` are dropped (constraint activities and random decisions are not
ported); `-rnd-init -rnd-seed=s` is `--seed=s`.

**Ranges must allow stress testing.** Every scheduled event has to be able to
fire on an instance with a few hundred conflicts, otherwise the fuzz corpus
never reaches it (ROADMAP 0.1). So the low end of every interval, limit and
threshold option is the smallest value the code can run with, not the
smallest sensible one, and where the old solver had no knob at all one is
added. From M1:

| option | default (M1) | range | stress value | meaning |
|---|---|---|---|---|
| `gcfrac` | 20 | 0..100 | 0 | percent of wasted arena that triggers a collection; 0 = collect at every safe point (5.3) |
| `reduceint` | 0 (M1), 300 (M2) | 0..1e9 | 2 | if nonzero: reduce when `conflicts >= lim.reduce`, then `lim.reduce = conflicts + reduceint * reductions` (`reductions` counts this one; the base is the current conflict count so that a burst of conflicts does not cause a burst of reductions). M1: a second trigger beside the size limit; M2.2: the schedule, with the size trigger behind `--reducesize` (default off); 0 = no conflict trigger |
| `reducesize` | 1 (M1, implicit), 0 (M2) | 0..1 | 1 | MiniSat's size trigger `#learnt - #assigned >= max_learnts` (`lim.max_learnts` and its growth stay named constants in `reduce.cpp`) |
| `reducetarget` | 50 (M1, implicit), 75 (M2) | 10..100 | 100 | percent of the reduction candidates deleted, worst glue and size first; `candidates * reducetarget / 100` in integers, so 50 is the old half |
| `tiers` | 1 | 0..1 | 0 | learnt constraints carrying a nonzero `used` mark are not reduction candidates (5.2; `tier.cpp`) |
| `glueupdate` | 1 | 0..1 | 0 | recompute the glue of a learnt constraint above tier 1 when an analysis uses it, keep it if lower |
| `tier1glue` | 2 | 0..1e9 | 0 | tier 1: learnt constraints with glue up to this value are never reduced (the old hard-wired "glue > 2"); with `--recomputetier` the start value of the per-kind limit |
| `tier2glue` | 6 | 0..1e9 | 0 | tier 2: a learnt constraint with glue up to this value gets `used = 2` when learnt or used, the others `used = 1`, so it survives two reductions without use instead of one; with `--recomputetier` the start value of the per-kind limit |
| `recomputetier` | 0 | 0..1 | 1 | M2-T3: recompute the tier limits of each kind from the histogram of glues of the analysis uses (`Tiers::usage`, 64 buckets, the last "that glue or more"), on the schedule `lim.retier` (9.4); readers use `tiers.tier1[kind]` / `tiers.tier2[kind]`, which equal `tier1glue` / `tier2glue` without the option. Glue recomputation in analysis then starts above `(tier1 + 1) / 2` (CaDiCaL) |
| `tier1limit`, `tier2limit` | 50, 90 | 0..100 | - | percent of the uses that tier 1 and tier 2 cover: the limit is the smallest glue (at least 1) whose cumulative uses reach that share |
| `tier1minglue`, `tier2minglue` | 0, 0 | 0..100 | - | lowest values of the recomputed limits (tier 2 is then forced above tier 1) |
| `luby`, `rfirst`, `rinc` | 1, 100, 200 (%) | `rfirst` 1.., `rinc` 100.. | `--no-luby --rfirst=1 --rinc=100` | restart after every conflict |
| `depreset` | 20 | 1..1e9 | 1 | reset dependencies every n-th restart (`--restartmode=0`) |
| `restartmode` | 0 | 0..1 | - | M2-T6: 0 = the schedule of `luby`/`rfirst`/`rinc`, 1 = glue averages per kind (CaDiCaL `restarting`); heuristic, no proof steps |
| `restartint` | 2 | 1..1e9 | 1 | mode 1: minimum conflicts between two restarts |
| `restartmargin` | 10 | 0..100 | 0 | mode 1: restart when `fast > (1 + margin/100) * slow` for the kind learnt last |
| `emagluefast`, `emaglueslow` | 33, 100000 | 1..1e9 | 1, 2 | mode 1: window lengths of the two glue averages (`alpha = 1/window`, `Ema` of `ema.hpp`) |
| `depresetint` | 5000 | 1..1e9 | 1 | mode 1: reset dependencies when `conflicts >= lim.depreset`, then `lim.depreset = conflicts + depresetint` (same "learnt since the last reset" guard as mode 0) |
| `reusetrail` | 1 | 0..1 | - | M2-T6: restart to `reuse_level ()` instead of 0 (`restart.cpp`); counter `reused` |
| `rootsimp` | 1 | 0..1 | - | M2-T4: root-level simplification (`simplify.cpp`) when root literals are new; modes 0 and 1 only (off in mode 2 whatever the option says) |
| `rootsimpdelay` | 1 | 0..1 | 0 | wait until `propagations >= lim.simplify`, where each run sets `lim.simplify = propagations + literals in all stored constraints` (MiniSat's `simpDB_props`); 0 = simplify after every complete propagation that brought new root literals |

| `ccminmode` | 0 | 0..3 | 3 | M2-T5: learnt-constraint minimisation (0 none, 1 basic, 2 deep, 3 deep with reduction); with a proof the removed literals are resolved away by a chain of reason ids (7.5, 8.2) |

**Defaults as shipped after M2-T7.** The adopt items are on (`tiers`,
`glueupdate`, `reduceint=300`, `reducetarget=75`, `rootsimp`, `reusetrail`);
the experiment items are off (`recomputetier=0`, `ccminmode=0`,
`restartmode=0`). The screening of M2-T7 (60 s, seed 4, one run per arm; STATUS
"M2-T7") found no measurable difference for `--ccminmode=3` in either
configuration (PAR2 +1.26 s default, +0.40 s `-dl`) and for `--restartmode=1`
in the default configuration (+0.84 s); `--restartmode=1` with `-dl`,
`--recomputetier` and `--ccminmode=2` were not run (time cap), so they keep
their shipped values. One seed at 60 s resolves only large effects: "off" here
means "not shown to help", not "shown not to help".

The M1-equivalent configuration is `--no-tiers --no-glueupdate
--reducetarget=50 --reducesize --reduceint=0 --no-recomputetier
--no-rootsimp --ccminmode=0 --restartmode=0 --no-reusetrail`
(`tests/m1_equiv.sh`).

The arithmetic growth of the `reduceint` schedule is deliberate: a fixed tiny
interval would keep the learnt database at constant size, and together with
restarts that can cost termination. Later milestones add their own rows
(`restartint` from 1, `inprocessint` from 1, effort
options up to "unbounded", occurrence and size limits from 0); ROADMAP names
them with each package. Stress values are for tests only and are never
benchmarked.

### 9.2 Statistics

`struct Stats` contains plain `int64_t` counters grouped by technique
(`conflicts`, `decisions`, `propagations`, `ticks`, `restarts`,
`learned[kind]`, `learnedlits[kind]`, `minimized`, `minimizedchain`, `dependencies`,
`reductions`, `reduced[kind]`, `used[kind]`, `glueupdates[kind]`,
`promoted[kind]`, `rootsimps`, `rootunits`, `rootstrengthened`,
`rootlits`, `rootdeleted`, `collections`, `modelcubes`, and per pass:
rounds, tried, successful, removed literals...). They are incremented
directly (`stats.conflicts++`) and printed in one place (`stats.cpp`) at
verbosity >= 1, each line prefixed with `c `. Current database sizes are
maintained in `constraint.cpp`.

The statistics block is also a machine interface: every counter is printed,
zero or not, on a line of the fixed form `c stat <name> <integer>` (names as
in `stats.hpp`, per-kind counters as `<name>.clause` / `<name>.cube`),
followed by the human-readable table. `tests/regress.sh` sums these lines
over a fuzz run and fails when a counter that a configuration is meant to
exercise stays at zero (ROADMAP 0.1); `bench/run.py` stores them for the
port-fidelity and proof-overhead reports. Renaming a counter is therefore an
interface change (update `tests/matrix.txt` in the same commit).

### 9.3 Profiling

`START (name)` / `STOP (name)` around phases (`parse`, `search`,
`propagate`, `analyze`, `reduce`, `simplify`, `collect`, `elim`, `subsume`,
`vivify`),
defined by an X-macro list with a level per profile; active profiles at or
below `--profile=<level>` are timed (process CPU time), nested as in CaDiCaL,
and printed with the statistics. Level 0 costs nothing in the inner loop.

### 9.4 Limits

`struct Limit` holds the conflict (or tick) count at which each scheduled
event fires next (`restart`, `reduce`, `rephase`, `stabilize`, `inprocess`,
per-pass thresholds), plus user limits (`conflicts`, `decisions`, time via an
alarm flag). `struct Inc` holds the growing intervals. `struct Last` records
counters at the last run of each pass (to compute "effort since then"); it
is added by the first package that reads it (not present in M1: review
M1-r1).
`lim.retier` (M2-T3, only with `--recomputetier`): the first recomputation of
the tier limits after 2 conflicts, then `1 << min (retiered, 16)` conflicts
after the previous one (CaDiCaL's schedule).
`lim.restart` (M2-T6, mode 1): `restartint` after the last restart; `lim.depreset`
(mode 1): conflict count of the next dependency reset. `Internal::averages`
holds the glue averages per kind (`struct Averages { Ema fast, slow; }`).
`lim.simplify` (M2-T4, with `--rootsimpdelay`) is a *propagation* count:
root simplification waits until `stats.propagations` reaches it.
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
literals (by the rules of ROADMAP M2.1: only under stored units), and
re-attaches watches for every live constraint; if a unit or an
empty constraint appeared it is handled there. Within occurrence mode, new
root units are propagated over occurrence lists (`propagate_occs`), not
watches. The arena may not be collected in occurrence mode.

Rebuilding the watches changes the order of the watch lists and therefore the
ideal arena layout, so `leave_occurrence_mode ()` triggers a garbage
collection (5.3) when the pass changed the database.

### 10.3 Variable status

`flags.hpp`: per variable a status `Active | Fixed | Eliminated` and
scheduling marks (`elim`, `subsume`, ... : "some constraint of this variable
changed since the pass last looked"). Further statuses (`Substituted`,
`Pure`) are added by the package that implements the technique, not before.
Only `Active` variables may occur in live constraints (after `collect`), be
decided, or be candidates. Leaving `Active` updates the block's `unassigned`
counter and the heaps in one function (`mark_eliminated` etc.); forgetting
this makes the solver wait forever for a variable that will never be
assigned.

**Frozen** variables are never eliminated. A variable is frozen if the app
says so through `Solver::freeze`. What is frozen by default:

- nothing for QCIR input: the side conditions of elimination (ROADMAP M3)
  already exclude every input variable, because inputs occur in both
  databases, and gate variables are never part of any output;
- for QDIMACS input, elimination is off by default (`--elimqdimacs=0`,
  ROADMAP M3.6). When it is switched on together with `--cert`, the decision
  variables of the certificate block are frozen **until** the extension stack
  (10.4) has been validated by the certificate tests; after that the freeze
  is removed.

Gate variables are ordinary variables for inprocessing (they are the main
targets), with one privilege: they are never part of any output.

### 10.4 Extension stack and certificates

`--cert` prints the values of the decision variables of the **certificate
block**, the outermost block that has decision variables, at the moment the
search ended (for a true formula with an outermost existential block this
assignment satisfies the formula; dually for a false formula with an
outermost universal block). Derivation-based reasoning never needs a full
model, so the only thing reconstruction ever has to restore is this one
block.

Who does what (all in the internal layer, in internal literals):

- `certificate.cpp` computes the value of every decision variable of the
  certificate block: the value on the trail if it is assigned; a variable
  left unassigned is given the value the output will show for it (the old
  binary prints such variables as positive literals, which happens under
  `--dl`, where the block may be only partially assigned when the search
  ends). Whether a certificate completed in this way is valid at all is the
  open question that ROADMAP M1.8 measures; whatever the coordinator decides
  there (print only assigned variables, or complete the block by a final
  search), `certificate.cpp` is the one place that implements it, and it
  hands `extend ()` a **total** assignment of the non-eliminated variables of
  the block.
- `extend.cpp` then reconstructs the eliminated variables of the block.
- `Solver::val` and `Solver::certificate` only translate internal variables
  to user numbers.

For QCIR input the stack is always empty: the certificate block consists of
input variables, and inputs are never eliminated (E2). The stack is needed
only for QDIMACS elimination, so it is built in that package (ROADMAP M3.6)
and not earlier.

`Internal` keeps the **extension stack** as in CaDiCaL's `extend.cpp`: when
an (existential) variable `x` of the certificate block is eliminated, the
irredundant clauses containing it are pushed, each with its witness literal
(the literal of `x`). At the end `extend ()` walks the stack backwards over
the certificate assignment: if no literal of a clause entry is true, the
witness is set true.

Why every other variable of a pushed clause has a known value: E3 only says
that no other variable of the clause is *deeper* than `x`; since `x` is in
the certificate block, and for QDIMACS input (every variable is a decision
variable) that is the outermost block of the prefix, the others are in that
same block. Their values are either part of the total assignment handed over by
`certificate.cpp`, or they were eliminated *after* `x` and have already been
reconstructed by the backward walk. The argument rests on the certificate
block being outermost, not on E3 alone; a stack for inner blocks would need
values the solver does not have.

Only clause entries are implemented. An entry for an eliminated *universal*
variable cannot arise in M3: a universal variable of the certificate block is
an input, and inputs occur in clauses in both input formats, so E2 never
lets it go. `mark_eliminated` asserts this. Eliminated variables outside the
certificate block push nothing. Variables fixed at root keep their value on
the trail and need no entry.

Later techniques that remove certificate-block variables (equivalent-literal
substitution, blocked clauses) add their entry kinds when they are built.

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
- QDIMACS input: every change to the irredundant clauses obeys the rules at
  the end of 11.1 (promotion before removal, deletion only under a stored
  unit or an irredundant subsumer, no elimination in mode 2).

---------------------------------------------------------------------------

## 11. Soundness framework for database transformations

Every technique in the ROADMAP is classified by what it does to the
databases, because that decides both its side conditions and its proof story.

### 11.1 What must be preserved

The solver's answer is justified by a derivation: the empty clause from the
clause database (false), or the empty cube from the cube database (true).

**QCIR input.** The two databases are independent encodings of the same
circuit; by INV-DERIVED every stored constraint has a QLRUP derivation from
the original encoding of its kind. So *any* answer the solver gives is
correct, whatever heuristics or simplifications ran. What a transformation
can break is **termination** (INV-COMPLETE: the solver reaches a state with
neither kind in conflict) and performance, never the verdict, as long as
INV-DERIVED holds. In mode 2 "QLRUP derivation" reads "long-distance
derivation": inprocessing only ever adds plain resolvents of constraints
without complementary literals (10.5), so stored constraints stay
long-distance derivable from the encoding.

**QDIMACS input, modes 0 and 1.** There is no cube encoding; cubes start
from satisfying assignments of the irredundant clauses, so the cube side is
only as good as the clause set it was read off. Notation: `Π` the current
prefix (over the variables that are not eliminated), `G` the irredundant
clauses (unit clauses included), `L` the learnt clauses, `T` the stored
cubes (none of them original; unit cubes included), `v` the truth value of the input, and

    lo = value of Π.(G ∧ ⋀L)          hi = value of Π.(G ∨ ⋁T)

Because `G ∧ ⋀L ⊨ G ⊨ G ∨ ⋁T`, every state has `lo <= value of Π.G <= hi`
(false < true).

> **INV-SANDWICH**: `lo = hi = v`. (Hence also `Π.G` has the value `v`.)

It justifies both verdicts: an empty clause makes `lo` false, an empty cube
makes `hi` true. It does **not** say that stored cubes are implicants of `G`,
and they are not in general: learnt clauses are consequences in the QBF
sense, not propositional ones, so once an irredundant clause has been
strengthened with a learnt clause an older cube may fail to imply `G`. (The
first version of this section demanded exactly that; review 00, B4.)

**Admissibility criterion.** A step from `(Π, G, L, T)` to `(Π', G', L',
T')` is admissible if

- **(LO)** `lo' >= lo`: the lower value does not decrease, and
- **(HI)** `hi' <= hi`: the upper value does not increase.

Then `v = lo <= lo' <= hi' <= hi = v`. Each condition is one-sided, which is
what makes the per-technique arguments short: weakening anything satisfies
(LO) for free, strengthening anything satisfies (HI) for free.

Facts used below (`φ` is an arbitrary propositional formula, not necessarily
a CNF):

- **F1 (monotonicity)** if `ψ ⊨ ψ'` then `Π.ψ <= Π.ψ'`.
- **F2 (resolution)** a resolvent, on a pivot of either quantifier, is a
  propositional consequence of its parents; dually a cube resolvent implies
  the disjunction of its parents.
- **F3 (reduction in context)** if `u` is universal and no variable of the
  clause `C` is quantified after `u`, then `Π.(φ ∧ (C ∨ u))` and
  `Π.(φ ∧ (C ∨ u) ∧ C)` have the same value. (Take a winning existential
  strategy for the first formula and a play in which `C` is false; then `u`
  is true in it. Let the universal player deviate at `u` only: the variables
  of `C` were all played before, so `C ∨ u` is false in the new play, a
  contradiction.) Dually for an existential `e` rightmost in a cube:
  `Π.(φ ∨ (t ∧ e))` and `Π.(φ ∨ (t ∧ e) ∨ t)` have the same value.
- Consequently **F4**: adding to `L` a clause obtained by one QLRUP step
  (resolutions, then reduction) from clauses of `G ∪ L` leaves `lo`
  unchanged, and adding to `T` a cube obtained by one QLRUP step from cubes
  of `T` leaves `hi` unchanged.

The steps of M1-M4, each against (LO) and (HI):

| step | (LO) | (HI) |
|---|---|---|
| learn a clause from `G ∪ L` | F4 | `G`, `T` untouched |
| learn a cube from `T` | `G`, `L` untouched | F4 |
| initial cube `t` with `t ⊨ G` (4.5) | untouched | `G ∨ ⋁T ∨ t ≡ G ∨ ⋁T` |
| delete a learnt clause; delete a cube | F1 (weaker conjunction); untouched | untouched; F1 (weaker disjunction) |
| promote a learnt clause `D` to irredundant | `G ∧ ⋀L` unchanged | F1 (`G ∧ D ⊨ G`) |
| replace an irredundant `C` by `C' ⊂ C`, where `C'` comes from one QLRUP step over `G ∪ L` (root-literal removal, self-subsumption, vivification) | F4, since `G' ∧ ⋀L ≡ G ∧ ⋀L ∧ C'` | F1 (`G' ⊨ G`) |
| replace a cube `t` by `t' ⊂ t` derived from `T` | untouched | F4, then deletion |
| delete an irredundant `C` implied by the remaining irredundant clauses (subsumed by an irredundant clause; contains a literal `l` whose unit clause `(l)` is irredundant) | F1 | `G' ≡ G` |
| delete an irredundant `C` containing `¬u`, where the unit cube `(u)` is stored | F1 | `G' ∨ u ≡ G ∨ u`, and `(u)` is a disjunct of `⋁T` |
| eliminate an existential `x` under E1-E4 | ROADMAP M3.2 | ROADMAP M3.2 (this is where E2 and E3 are used) |

Rules that follow, and that the code must respect for QDIMACS input:

1. **Irredundant clauses may be strengthened using learnt clauses.** The
   strengthened clause must be a QLRUP step over stored clauses, which
   INV-DERIVED demands anyway.
2. **A learnt clause that justifies removing an irredundant one becomes
   irredundant first.** This covers subsumption by a learnt clause and unit
   clauses: unit constraints of either kind are flagged irredundant and are
   never deleted (4.3), so the unit clause `(l)` is in `G` and the unit cube
   `(u)` stays in `T` for as long as the deletions they justified matter.
3. **An irredundant clause is deleted only under one of the three deletion
   rows above.** In particular a clause that is disabled at root by a
   literal *without* a stored unit (a root assignment whose reason is a
   longer constraint that cannot be turned into a unit, ROADMAP M2.1) stays.
4. **Initial cubes hit the current `G`, including its unit clauses.** Root
   literals are therefore part of initial cubes unless existential reduction
   removes them; they are permanently vanished there and cost nothing.
5. Cubes and learnt clauses can always be deleted.

**QDIMACS input, mode 2.** Long-distance constraints (with complementary
secondary literals) have no clause-by-clause semantics, so INV-SANDWICH
cannot be stated for them. The argument is the baseline's: every stored
clause is long-distance derivable from the input, and every initial cube is
an implicant of the *input* matrix. To keep the second half true, `G` may
only be strengthened or shrunk equivalently in mode 2 (`G' ⊨ G`, with every
new clause derivable and every deleted clause implied by the remaining
irredundant ones): the last two rows of the table (deletion under a unit
cube, elimination) are **not applied to QDIMACS input in mode 2**.

### 11.2 Classes

- **(D) Derivational**: adds constraints that are resolvents (plus reduction)
  of stored constraints of the same kind, and/or deletes constraints. QLRUP
  expresses it today: derived steps and deletions. Examples: learning,
  minimisation, vivification, strengthening, BVE resolvents, failed-literal
  units.
- **(R) Removal**: deletes irredundant constraints that are not implied by the
  rest in the propositional sense (BVE parents, blocked constraints). In the
  proof a deletion is always legal. The obligations are condition (HI) of
  11.1 for QDIMACS (removal weakens `G`, so (LO) is free) and INV-COMPLETE
  for QCIR; they are side conditions of the solver, not of the proof.
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
  restore, tainting), no `External` class and no external propagator, no
  IPASIR, no local search, no `mobical`;
- no several-thousand-line `internal.hpp` with inline everything: inline only
  what profiling shows hot (`val`, `kval`, `assign`, watch access);
- no macro-generated control flow beyond the tables and `LOG`/`START`
  families; no `goto` (the old analysis uses it; restructure when porting);

Formatting **is** CaDiCaL's: the repository's `.clang-format` is a copy of
`~/cadical/.clang-format` (LLVM base, `ColumnLimit: 76`, `SpaceBeforeParens:
Always`, `SpaceAfterCStyleCast: true`, `AlignEscapedNewlines: DontAlign`), so
code is written `propagate ()`, `if (x)`, as in these documents.
`clang-format` 15 is installed and is the authority; a `ctest` test fails on
unformatted files in `src/` and `test/unit/`. (Revision 1 chose LLVM style at
100 columns; changed after review 00, S9, while no code exists. The owner can
reverse it by replacing one file and reformatting.)

Process rules: no commented-out code; no dead options (options that exist
for the stress configurations are not dead: the matrix uses them); every new
technique arrives with its option to switch it off, its statistics, its unit
tests, its normal and stress configurations in `tests/matrix.txt` with the
counters that must be nonzero, and a benchmark ablation.

---------------------------------------------------------------------------

## 13. Review responses

Review 00 (`reviews/00-architecture.md`) on revision 1 of this document and
of `ROADMAP.md`. All five blocking items are accepted; none is rebutted. The
table says where each one landed and where the response goes beyond or
departs from what the review asked.

| item | response | where |
|---|---|---|
| **B1** fuzz corpus does not reach the search machinery | Accepted. Two-tier corpus (search tier: 10^2-10^4 baseline conflicts with checkable proofs, histogram reported); stress configurations per milestone; options whose ranges allow them (`gcfrac=0`, `reduceint`, `tier1glue=0`, restart every conflict, `depreset=1`, later tier/inprocessing knobs); `c stat` lines; `regress.sh` fails when a required counter is nonzero on fewer than 10% of the search-tier instances. Added beyond the review: `gc` and `restart` stress are separate and `reduceint` grows arithmetically, because restarting every conflict while deleting nearly all learnt constraints need not terminate; stress timeouts above 2% fail | ROADMAP 0.1, P0.1; ARCH 9.1, 9.2, 5.3 |
| **B2** noise band measures the machine, not the search | Accepted. `--seed` = random initial scores (the baseline's `-rnd-init -rnd-seed`); run sets of 5 seeds (quick) and 3 fresh seeds (full) for both arms; paired per-instance comparison with a bootstrap interval on the PAR2 difference and a sign test; "better" / "not worse" defined once and used by every gate; experiment items must pass at the quick tier and again at the full tier. Limits fixed at 16 GB and 48 jobs, enforced by `compare.py`; the existing `baseline-t5` / `baseline-t180` runs are informational only | ROADMAP 0.3, P0.2, P0.4; ARCH 7.3 |
| **B3** proof-check coverage unspecified | Accepted. Coverage table in every report with non-accepted proofs by name; a proof attempted for every instance solved at the quick tier (routine: "on" arm, seed 1; gates: seed 0, default, `-dl`, `-mode=1`, 3600 s checker limit, `qlrup-trim` retry); no unexplained drop between gates; proof overhead per milestone | ROADMAP 0.3 and every milestone's acceptance |
| **B4** QDIMACS soundness criterion wrong | Accepted; the review's invariant is adopted in a slightly stronger and more convenient form. INV-SANDWICH: `Π.(G ∧ ⋀L)` and `Π.(G ∨ ⋁T)` both have the input's truth value (the review's `Π.G` then follows, and the learnt clauses are covered by the same statement instead of a separate condition). Admissibility is two one-sided conditions (LO)/(HI); every step of M1-M4 is argued against them, including the review's missing step (moving `∃x` innermost in `G ∨ ⋁T` under E2+E3). Answer to the review's question: **yes, irredundant constraints may be strengthened using redundant ones**; a redundant constraint that justifies *removing* an irredundant one is promoted first; units are irredundant and never deleted. Two things the review did not ask for: deletion of root-disabled constraints is tied to a stored unit (M2.1 step 3), and for QDIMACS in mode 2 the invariant cannot be stated, so only equivalent shrinking of `G` is allowed there | ARCH 11.1, 4.3, 4.5, 10.5; ROADMAP M2.1, M3.1-M3.3, M4 |
| **B5** layering claim false for the extension stack | Accepted, and taken one step further (with S10): there is no `External` class at all. `Solver` owns the variable maps and translates; the extension stack, reconstruction and certificate values live in `Internal` in internal literals; proof numbers are per-variable static data in `prefix.hpp`, read by `Proof`. No upward pointer exists | ARCH 3, 3.5, 10.4 |
| S1 measure BVE yield first | Accepted: P0.3 / M3.0 with a decision point before M3.2, and the statement that E3 is not a soundness condition for QCIR goes to the owner with the numbers | ROADMAP M3.0 |
| S2 QDIMACS elimination unverified | Accepted and strengthened: it is the optional package M3.6, off by default (`--elimqdimacs=0`); `check_model_cube ()` validates every initial cube; clause entries only on the extension stack | ROADMAP M3.4, M3.6; ARCH 4.5, 10.4 |
| S3 header size | Accepted: layout provisional, measurement in M1.3, 12-byte fallback; superseded after review M1-r1 by the 4-byte header with trailing words | ARCH 5.2; ROADMAP M1.3, M1 round 2 |
| S4 propagation variants | Accepted: table of six variants, one templated watch loop (`Kind`, `Lone`), dispatch outside the loop | ARCH 7.2 |
| S5 meaning of "pluggable" | Accepted: touch-point list, per-technique state structs, edits to the core are recorded design changes | ARCH 3.6 |
| S6 port-fidelity diagnostics | Accepted | ROADMAP M1.9 |
| S7 signals | Accepted: the handler sets a flag, the app flushes | ARCH 8.2, 3.5 |
| S8 scope of the internal `Checker` | Accepted: scope table; `add_model_cube` in the tracer interface | ARCH 8.1 |
| S9 formatting, `--arenasort` | Accepted and resolved rather than recorded as a deviation: the repository uses CaDiCaL's `.clang-format`; option renamed `--arenaorder` | ARCH 12, 5.3 |
| S10 things specified too early; three layers | Accepted: statuses and header bits arrive with their technique, the `compact` remark is gone, `External` is gone | ARCH 10.3, 5.2, 4.2, 3 |
| S11 extension stack wording | Accepted: the argument rests on the certificate block being outermost; `certificate.cpp` hands `extend ()` a total assignment and is the single place where the `-dl` wrinkle is resolved | ARCH 10.4 |
| S12 gate for modes 1 and 2 | Accepted | ROADMAP 0.3 |
| watcher interpretation | Recorded in `STATUS.md` as a decision the owner can veto | STATUS |
