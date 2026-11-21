/-
# QlrupChecker.Ext — computing and validating the extended prefix (proved)

`mkCtx q` computes the extended prefix of `q`: the variable of each gate is placed right after
the innermost quantifier block containing a variable the gate depends on. The construction
itself is not verified. Instead, `ctxOk q c` tests that `c` describes a valid extended prefix,
and `ctxOk_sound` proves that the test is correct. So the placement of gate variables can be
changed (to any order in which gates come after their inputs) without touching the proofs.
-/
import QlrupChecker.Check

namespace Qlrup

open Qbf Std.Sat Qcir

/-! ## Construction (not verified) -/

/-- The index of the quantifier block of each variable (`blockOf[v]` for variable `v`; index
`0` is unused), and the number of blocks. -/
def blocks (q : Qcir) : Array Nat × Nat := Id.run do
  let mut blockOf : Array Nat := #[0]
  let mut count := 0
  let mut last : Option Quant := none
  for qt in q.quants do
    if last != some qt then
      count := count + 1
      last := some qt
    blockOf := blockOf.push (count - 1)
  return (blockOf, count)

def mkCtx (q : Qcir) : Ctx := Id.run do
  let n := q.numVars
  let (blockOf, nblocks) := blocks q
  -- `depth[k]`: one more than the innermost block gate `k` depends on (`0` if there is none).
  let mut depth : Array Nat := Array.emptyWithCapacity q.gates.size
  let mut buckets : Array (Array Nat) := Array.replicate (nblocks + 1) #[]
  for g in q.gates do
    let d := g.inputs.foldl (init := 0) fun d l =>
      max d (if l.1 ≤ n then blockOf.getD l.1 0 + 1 else depth.getD (l.1 - (n + 1)) 0)
    buckets := buckets.modify d fun b => b.push (n + 1 + depth.size)
    depth := depth.push d
  let mut pre : Array (Quant × Var) := Array.emptyWithCapacity (n + q.gates.size)
  for g in buckets.getD 0 #[] do
    pre := pre.push (Quant.ex, g)
  for i in [0:n] do
    pre := pre.push (q.quants.getD i Quant.ex, i + 1)
    -- After the last variable of a block, add the gates that depend on it.
    if i + 1 == n || blockOf.getD (i + 2) 0 != blockOf.getD (i + 1) 0 then
      for g in buckets.getD (blockOf.getD (i + 1) 0 + 1) #[] do
        pre := pre.push (Quant.ex, g)
  let mut pos : Array Nat := Array.replicate (n + q.gates.size + 1) 0
  for h : i in [0:pre.size] do
    pos := pos.setIfInBounds (pre[i]'h.2.1).2 i
  return { pre, pos }

/-! ## Validation -/

/-- The variable at position `posOf v` is `v`. -/
def Ctx.has (c : Ctx) (v : Nat) : Bool :=
  match c.pre[c.posOf v]? with
  | some (_, w) => w == v
  | none => false

/-- Every entry of the prefix is at the position recorded for its variable. -/
def posCheck (c : Ctx) : Bool :=
  (List.range c.pre.size).all fun i =>
    match c.pre[i]? with
    | some (_, v) => c.posOf v == i
    | none => false

/-- Every entry of the prefix that is not a variable of `q` is an existentially quantified
gate variable whose inputs come earlier. -/
def gateCheck (q : Qcir) (c : Ctx) : Bool :=
  (List.range c.pre.size).all fun i =>
    match c.pre[i]? with
    | some (qt, v) =>
      v ≤ q.numVars ||
        (qt == Quant.ex &&
          match q.gates[v - (q.numVars + 1)]? with
          | some g => g.inputs.all fun l => c.has l.1 && c.posOf l.1 < i
          | none => false)
    | none => false

/-- Every gate has a variable in the prefix. -/
def allCheck (q : Qcir) (c : Ctx) : Bool :=
  (List.range q.gates.size).all fun k => c.has (q.numVars + 1 + k)

def ctxOk (q : Qcir) (c : Ctx) : Bool :=
  posCheck c && gateCheck q c && allCheck q c &&
    decide (c.list.filter (fun qx => decide (qx.2 ≤ q.numVars)) = q.pre)

theorem pos_of_posCheck {c : Ctx} (h : posCheck c = true) :
    ∀ i (hi : i < c.pre.size), c.posOf (c.pre[i]).2 = i := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [Array.getElem?_eq_getElem hi] at this
  simpa using this

theorem vars_getElem (c : Ctx) (i : Nat) (hi : i < c.pre.size) :
    (Prefix.vars c.list)[i]'(by simpa [Prefix.vars, Ctx.list] using hi) = (c.pre[i]).2 := by
  simp [Prefix.vars, Ctx.list]

theorem valid_of_posCheck {c : Ctx} (h : posCheck c = true) : c.Valid := by
  have hpos := pos_of_posCheck h
  refine ⟨?_, hpos⟩
  have hlen : (Prefix.vars c.list).length = c.pre.size := by simp [Prefix.vars, Ctx.list]
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  rw [vars_getElem c i (hlen ▸ hi), vars_getElem c j (hlen ▸ hj)] at heq
  have h1 := hpos i (hlen ▸ hi)
  have h2 := hpos j (hlen ▸ hj)
  rw [heq] at h1
  omega

/-- A variable with `c.has v` at a position before `i` is among the first `i` entries. -/
theorem mem_vars_take {c : Ctx} {v i : Nat} (hhas : c.has v = true) (hlt : c.posOf v < i) :
    v ∈ Prefix.vars (c.list.take i) := by
  unfold Ctx.has at hhas
  split at hhas
  · rename_i qt w hw
    have hwv : w = v := by simpa using hhas
    subst hwv
    have hj : c.posOf w < c.pre.size := by
      rcases Array.getElem?_eq_some_iff.mp hw with ⟨hj, _⟩
      exact hj
    have hget : c.pre[c.posOf w] = (qt, w) := by
      rcases Array.getElem?_eq_some_iff.mp hw with ⟨_, hget⟩
      exact hget
    simp only [Prefix.vars, List.mem_map]
    refine ⟨(qt, w), ?_, rfl⟩
    rw [List.mem_take_iff_getElem]
    refine ⟨c.posOf w, ?_, ?_⟩
    · simp only [Ctx.list, Array.length_toList]; omega
    · simp [Ctx.list, hget]
  · cases hhas

theorem ctxOk_sound {q : Qcir} {c : Ctx} (h : ctxOk q c = true) :
    c.Valid ∧ ExtValid q c.list := by
  simp only [ctxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hpos, hgate⟩, hall⟩, hres⟩ := h
  have hvalid := valid_of_posCheck hpos
  refine ⟨hvalid, hvalid.nodup, hres, ?_, ?_⟩
  · intro P₁ qt v P₂ hP hv
    have hlen : c.pre.size = P₁.length + (P₂.length + 1) := by
      have := congrArg List.length hP
      simpa [Ctx.list] using this
    have hi : P₁.length < c.pre.size := by omega
    have hget : c.pre[P₁.length] = (qt, v) := by
      have : c.list[P₁.length]'(by simpa [Ctx.list] using hi) = (qt, v) := by
        simp [hP]
      simpa [Ctx.list] using this
    have := List.all_eq_true.mp hgate P₁.length (List.mem_range.mpr hi)
    rw [Array.getElem?_eq_getElem hi, hget] at this
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with hle | ⟨hqt, hg⟩
    · exact absurd hle (by vomega)
    · refine ⟨hqt, ?_⟩
      split at hg
      · rename_i g hgk
        refine ⟨g, by rw [Array.getElem?_toList]; exact hgk, fun l hl => ?_⟩
        have hl' := List.all_eq_true.mp hg l hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hl'
        have hmem := mem_vars_take hl'.1 hl'.2
        have htake : c.list.take P₁.length = P₁ := by simp [hP]
        rw [htake] at hmem
        exact hmem
      · cases hg
  · intro k hk
    have := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    have hmem := mem_vars_take this (Nat.lt_succ_self _)
    have hsub : ∀ x, x ∈ Prefix.vars (c.list.take (c.posOf (q.numVars + 1 + k) + 1)) →
        x ∈ Prefix.vars c.list := by
      intro x hx
      simp only [Prefix.vars, List.mem_map] at hx ⊢
      obtain ⟨qx, hqx, rfl⟩ := hx
      exact ⟨qx, List.mem_of_mem_take hqx, rfl⟩
    exact hsub _ hmem

end Qlrup
