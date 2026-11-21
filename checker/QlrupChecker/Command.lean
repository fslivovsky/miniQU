/-
# QlrupChecker.Command — proofs as Lean theorems, checked while streaming

    qlrup_true name "formula.qcir" "proof.qlrup"
    qlrup_false name "formula.qcir" "proof.qlrup"

register the theorem

    name : (Qlrup.parseQcir «contents of formula.qcir»).True        -- qlrup_true
    name : ¬ (Qlrup.parseQcir «contents of formula.qcir»).True      -- qlrup_false

by evaluating the verified checker `Qlrup.check` on the proof (`native_decide`). The contents
of the QCIR file are part of the statement, so the theorem says exactly what the file says.

## Streaming, and what is trusted

The proof is never stored in the Lean environment or held in memory as a whole. The steps are
pulled, block by block, from an `opaque` constant `name.feed : Nat → Option (Array Step)` whose
native implementation `proofFeedImpl` reads the proof file (or a FIFO connected to a running
solver or to `qlrup-trim`). Memory use is bounded by a block of steps plus the constraints that
have been added and not yet deleted.

This is the design of `LRATCatcher.StreamOracle` in lrat-catcher, and the same discussion
applies. The soundness theorems `Qlrup.true_of_check` and `Qlrup.false_of_check` hold for
*every* feed, so they are ordinary theorems. An opaque constant has no logical value, so
evaluating the check with one particular stream of blocks cannot make a false statement
provable: the constant could have been defined to return exactly those blocks. Each command
declares a feed of its own, so that several theorems in one environment do not constrain the
same constant.

The trusted base of a theorem produced this way is therefore: the Lean kernel and compiler
(one `native_decide` axiom per theorem), the definitions in `QlrupChecker/Qcir.lean` (which
give the statement its meaning), and the reader below in so far as it must not do anything
other than produce blocks of steps. It is *not* trusted to parse correctly: whatever blocks it
produces, the check is sound.

Do not replace the opaque feed by a definition with a different `implemented_by`: that would
make `native_decide` assert a statement that is provably false.
-/
import QlrupChecker.Reader
import Lean

open Lean Elab Command

namespace Qlrup

/-! ## The feed -/

private initialize feedReader : IO.Ref (Option Reader) ← IO.mkRef none

private initialize feedPath : IO.Ref (Option String) ← IO.mkRef none

private initialize feedIndex : IO.Ref Nat ← IO.mkRef 0

/-- Forgets the current stream and sets the path of the next one. -/
def feedReset (path? : Option String) : IO Unit := do
  feedReader.set none
  feedIndex.set 0
  feedPath.set path?

/-- The number of steps in a block. Any blocking is checked, so this does not affect
soundness. -/
def feedBlockSize : Nat := 4096

/-- Reads block `i` of the proof set by `feedReset`; `none` at the end of the proof and on any
error, in which case the check fails.

Blocks can only be read in order, and the guard on the index is what enforces this. It also
makes the body depend on its argument: an implementation that ignores `i` is a closed term,
which the compiler evaluates once, so that every call would return the first block. -/
unsafe def proofFeedImpl : Nat → Option (Array Step) := fun i =>
  match unsafeIO (do
    let expected ← feedIndex.get
    unless i == expected do
      throw (IO.userError s!"proof feed: block {i} requested, expected block {expected}")
    let reader ← do
      match ← feedReader.get with
      | some r => pure r
      | none =>
        let some path ← feedPath.get
          | throw (IO.userError "proof feed: no proof file set")
        let r ← Reader.open path
        feedReader.set (some r)
        pure r
    feedIndex.set (i + 1)
    match ← reader.nextBlock feedBlockSize with
    | .ok block => pure block
    | .error msg => throw (IO.userError msg)) with
  | .ok block => block
  | .error _ => none

/-! ## Commands -/

/-- Elaborates the theorem `n` about the formula in `qcirFile`, checking the proof in
`proofFile`. -/
def elabQlrup (expectTrue : Bool) (n : Ident) (qcirFile proofFile : String) :
    CommandElabM Unit := do
  let text ← IO.FS.readFile qcirFile
  let q ← `(Qlrup.parseQcir $(quote text))
  let feedId := mkIdent (n.getId ++ `feed)
  try
    feedReset (some proofFile)
    -- A feed of its own for this theorem (see the module docstring).
    elabCommand (← `(command|
      @[implemented_by Qlrup.proofFeedImpl]
      opaque $feedId : Nat → Option (Array Qlrup.Step)))
    -- The check has to run on this thread, while the stream is set, and may take long.
    if expectTrue then
      elabCommand (← `(command|
        set_option Elab.async false in
        set_option maxHeartbeats 0 in
        theorem $n : Qlrup.Qcir.True $q :=
          Qlrup.true_of_check $q $feedId Qlrup.streamFuel (by native_decide)))
    else
      elabCommand (← `(command|
        set_option Elab.async false in
        set_option maxHeartbeats 0 in
        theorem $n : ¬ Qlrup.Qcir.True $q :=
          Qlrup.false_of_check $q $feedId Qlrup.streamFuel (by native_decide)))
  finally
    feedReset none

/-- `qlrup_true name "formula.qcir" "proof"` registers `name : (parseQcir «formula»).True`,
checking the proof (which must derive the empty term) as it is read. -/
elab "qlrup_true " n:ident ppSpace qcir:str ppSpace proof:str : command =>
  elabQlrup true n qcir.getString proof.getString

/-- `qlrup_false name "formula.qcir" "proof"` registers `name : ¬ (parseQcir «formula»).True`,
checking the proof (which must derive the empty clause) as it is read. -/
elab "qlrup_false " n:ident ppSpace qcir:str ppSpace proof:str : command =>
  elabQlrup false n qcir.getString proof.getString

end Qlrup
