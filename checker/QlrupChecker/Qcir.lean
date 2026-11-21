/-
# QlrupChecker.Qcir — QCIR formulas and their semantics (trusted)

This file is part of the statement of the theorems the checker proves: it defines what a QCIR
file denotes (`parseQcir`), when the result is well-formed (`Qcir.wf`), and when the formula is
true (`Qcir.True`).

## Accepted input

Prenex QCIR-G14 as accepted by miniQU:

* Whitespace is ignored; empty lines and lines starting with `#` are skipped.
* `exists(v, ...)`, `forall(v, ...)`, `free(v, ...)` quantify variables. Free variables are
  treated as existential. Keywords are case-insensitive, identifiers are case-sensitive.
* `output(l)` names the output literal; a literal is an identifier, optionally preceded by `-`.
* `g = and(l, ...)`, `g = or(l, ...)`, `g = xor(l, l)`, `g = ite(l, l, l)` define gates. Every
  input must be a variable or a gate defined earlier in the file, and all quantifier statements
  must precede the first gate definition.

Anything else makes the result ill-formed (`ok = false`), which `wf` rejects.

## Numbering

Variables are numbered `1, ..., n` in the order in which they are quantified, and gates
`n+1, n+2, ...` in the order of their definitions. `g = xor(a, b)` stands for the three gates
`and(a, -b)`, `and(-a, b)`, `g = or(·, ·)` in this order, and `g = ite(c, a, b)` for
`and(c, a)`, `and(-c, b)`, `g = or(·, ·)`.
-/
import QbfLean.QRes
import Std.Data.HashMap

namespace Qlrup

open Qbf Std.Sat

/-- `omega`, after unfolding `Var` (which hides `Nat` from it). -/
macro "vomega" : tactic => `(tactic| ((try simp only [Qbf.Var] at *); omega))

/-- A literal: a variable or gate number together with its polarity (`true` = positive). -/
abbrev Lit := Literal Var

inductive GateKind where
  | and | or
  deriving DecidableEq, Repr, Inhabited

structure Gate where
  kind : GateKind
  inputs : List Lit
  deriving Repr, Inhabited

/-- A prenex QCIR formula. Variable `i + 1` is quantified by `quants[i]`, and `gates[k]` is the
gate with number `quants.size + 1 + k`. -/
structure Qcir where
  ok : Bool
  quants : Array Quant
  gates : Array Gate
  output : Lit
  deriving Inhabited

namespace Qcir

def numVars (q : Qcir) : Nat := q.quants.size

/-- The number of the gate at index `k`. -/
def gateNum (q : Qcir) (k : Nat) : Nat := q.numVars + 1 + k

/-- The largest number of a variable or gate. -/
def maxVar (q : Qcir) : Nat := q.numVars + q.gates.size

/-! ## Semantics -/

/-- The value of a literal under an assignment. -/
def litVal (σ : Assignment) (l : Lit) : Bool := σ l.1 == l.2

def _root_.Qlrup.Gate.eval (g : Gate) (σ : Assignment) : Bool :=
  match g.kind with
  | .and => g.inputs.all (litVal σ)
  | .or => g.inputs.any (litVal σ)

/-- Evaluates the gates in order, starting with the gate number `k`, and stores their values. -/
def extendFrom : Nat → List Gate → Assignment → Assignment
  | _, [], σ => σ
  | k, g :: gs, σ => extendFrom (k + 1) gs (σ[k ↦ g.eval σ])

/-- The assignment `σ` extended by the values of all gates. -/
def extend (q : Qcir) (σ : Assignment) : Assignment :=
  extendFrom (q.numVars + 1) q.gates.toList σ

/-- The value of the output under an assignment of the variables. -/
def matrix (q : Qcir) (σ : Assignment) : Bool := litVal (q.extend σ) q.output

/-- The quantifier prefix for variables `k, k+1, ...`. -/
def prefixFrom : Nat → List Quant → Prefix
  | _, [] => []
  | k, qt :: qs => (qt, k) :: prefixFrom (k + 1) qs

/-- The quantifier prefix of the formula, outermost variable first. -/
def pre (q : Qcir) : Prefix := prefixFrom 1 q.quants.toList

/-- Truth of a prenex formula with an arbitrary matrix (cf. `Qbf.evalPrefix` for CNF). -/
def evalPrefixF : Prefix → Assignment → (Assignment → Bool) → Prop
  | [], σ, f => f σ = true
  | (.ex, x) :: p, σ, f => ∃ b : Bool, evalPrefixF p σ[x ↦ b] f
  | (.all, x) :: p, σ, f => ∀ b : Bool, evalPrefixF p σ[x ↦ b] f

/-- The formula is true. -/
def True (q : Qcir) : Prop := evalPrefixF q.pre (fun _ => false) q.matrix

/-! ## Well-formedness -/

/-- The inputs of the gates starting at number `k` are variables or earlier gates. -/
def gatesWf : Nat → List Gate → Bool
  | _, [] => true
  | k, g :: gs => g.inputs.all (fun l => 1 ≤ l.1 && l.1 < k) && gatesWf (k + 1) gs

def wf (q : Qcir) : Bool :=
  q.ok && gatesWf (q.numVars + 1) q.gates.toList &&
    (1 ≤ q.output.1 && q.output.1 ≤ q.maxVar)

end Qcir

/-! ## Parser -/

namespace Parse

/-- Removes all whitespace from a line. -/
def strip (s : String) : List Char :=
  s.toList.filter fun c => !c.isWhitespace

/-- Splits a list at every occurrence of `sep`. -/
def splitAt (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitAt sep cs with
    | [] => [[]]
    | part :: parts => if c == sep then [] :: part :: parts else (c :: part) :: parts

def lower (s : List Char) : String := String.ofList (s.map Char.toLower)

structure State where
  ok : Bool := true
  /-- Numbers of variables and gates by name. -/
  names : Std.HashMap String Nat := {}
  quants : Array Quant := #[]
  gates : Array Gate := #[]
  /-- The output literal as written; it may refer to a gate that is defined later. -/
  output : Option (List Char) := none

/-- Looks up a literal; `none` if the name is unknown or empty. -/
def State.lit (st : State) (s : List Char) : Option Lit :=
  let (name, pol) := match s with
    | '-' :: rest => (rest, false)
    | _ => (s, true)
  if name.isEmpty then none else (st.names[String.ofList name]?).map fun v => (v, pol)

def State.fail (st : State) : State := { st with ok := false }

/-- Adds a gate with a fresh number and returns the number. -/
def State.addGate (st : State) (kind : GateKind) (inputs : List Lit) : State × Nat :=
  let num := st.quants.size + 1 + st.gates.size
  ({ st with gates := st.gates.push { kind, inputs } }, num)

/-- A name that can be given to a new variable or gate. -/
def State.fresh (st : State) (name : List Char) : Bool :=
  !name.isEmpty && name.head? != some '-' && !st.names.contains (String.ofList name)

def State.quantify (st : State) (qt : Quant) (args : List (List Char)) : State :=
  if st.gates.size > 0 then st.fail else
  args.foldl (init := st) fun st name =>
    if st.fresh name then
      { st with names := st.names.insert (String.ofList name) (st.quants.size + 1),
                quants := st.quants.push qt }
    else st.fail

def State.defineGate (st : State) (name : List Char) (kind : String) (args : List (List Char)) :
    State :=
  if !st.fresh name then st.fail else
  match args.mapM st.lit with
  | none => st.fail
  | some ls =>
    let name := String.ofList name
    let neg (l : Lit) : Lit := (l.1, !l.2)
    let simple (kind : GateKind) : State :=
      let (st, g) := st.addGate kind ls
      { st with names := st.names.insert name g }
    let twoLevel (a b : List Lit) : State :=
      let (st, x) := st.addGate .and a
      let (st, y) := st.addGate .and b
      let ins : List Lit := [(x, true), (y, true)]
      let (st, g) := st.addGate .or ins
      { st with names := st.names.insert name g }
    match kind, ls with
    | "and", _ => simple .and
    | "or", _ => simple .or
    | "xor", [a, b] => twoLevel ([a, neg b]) ([neg a, b])
    | "ite", [c, a, b] => twoLevel ([c, a]) ([neg c, b])
    | _, _ => st.fail

def State.line (st : State) (raw : String) : State :=
  let s := strip raw
  if s.isEmpty || s.head? == some '#' then st else
  if s.getLast? != some ')' then st.fail else
  match splitAt '(' s.dropLast with
  | [head, argStr] =>
    let args := if argStr.isEmpty then [] else splitAt ',' argStr
    match splitAt '=' head with
    | [kw] =>
      match lower kw with
      | "exists" => st.quantify .ex args
      | "free" => st.quantify .ex args
      | "forall" => st.quantify .all args
      | "output" =>
        match st.output, args with
        | none, [l] => { st with output := some l }
        | _, _ => st.fail
      | _ => st.fail
    | [name, kind] => st.defineGate name (lower kind) args
    | _ => st.fail
  | _ => st.fail

end Parse

/-- Parses the contents of a QCIR file. -/
def parseQcir (text : String) : Qcir :=
  let st := (text.splitOn "\n").foldl Parse.State.line {}
  match st.output.bind st.lit with
  | some out => { ok := st.ok, quants := st.quants, gates := st.gates, output := out }
  | none => { ok := false, quants := st.quants, gates := st.gates, output := (0, true) }

end Qlrup
