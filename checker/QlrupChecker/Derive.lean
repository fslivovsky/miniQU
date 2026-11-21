/-
# QlrupChecker.Derive — resolution and universal reduction on literal sets (proved)

The two operations a derivation step is made of, on clauses represented as hash sets of
literals, with their soundness:

* `resolveStep R A` resolves `R` with the clause `A` if exactly one literal of `A` clashes with
  `R`; the result follows from `R` and `A` (`resolveStep_sat`).
* `reduceSet c R` removes the universal literals that come after all existential variables of
  `R` in the prefix described by `c`. If the clause `R` follows from a CNF that is true under
  the prefix, then the CNF remains true when the reduced clause is added
  (`reduceSet_sound`, by `Qbf.evalPrefix_reduce`).
-/
import QlrupChecker.Tseitin
import Std.Data.HashSet

namespace Qlrup

open Qbf Std.Sat Qcir

abbrev LitSet := Std.HashSet Lit

theorem negLit_negLit (l : Lit) : negLit (negLit l) = l := by
  obtain ⟨v, b⟩ := l; simp [negLit]

theorem negLit_ne (l : Lit) : negLit l ≠ l := by
  obtain ⟨v, b⟩ := l; cases b <;> simp [negLit]

/-- Some literal of `R` is true under `τ`. -/
def SatBy (τ : Assignment) (R : LitSet) : Prop := ∃ l, l ∈ R ∧ τ l.1 = l.2

/-- `R` does not contain complementary literals. -/
def NoTaut (R : LitSet) : Prop := ∀ l, l ∈ R → negLit l ∉ R

/-- The clause `A` does not contain complementary literals. -/
def NoTautL (A : List Lit) : Prop := ∀ l, l ∈ A → negLit l ∉ A

theorem not_taut_of_noTautL {A : List Lit} (h : NoTautL A) : ¬ Taut A := by
  rw [taut_iff]
  rintro ⟨l, hl, hl'⟩
  exact h l hl hl'

theorem satBy_ofList {τ : Assignment} {A : List Lit} :
    SatBy τ (Std.HashSet.ofList A) ↔ CNF.Clause.eval τ A = true := by
  rw [clause_eval_iff]
  constructor
  · rintro ⟨l, hl, hτ⟩
    exact ⟨l, by simpa using hl, hτ⟩
  · rintro ⟨l, hl, hτ⟩
    exact ⟨l, by simpa using hl, hτ⟩

theorem satBy_toList {τ : Assignment} {R : LitSet} :
    CNF.Clause.eval τ R.toList = true ↔ SatBy τ R := by
  rw [clause_eval_iff]
  constructor
  · rintro ⟨l, hl, hτ⟩
    exact ⟨l, by simpa using hl, hτ⟩
  · rintro ⟨l, hl, hτ⟩
    exact ⟨l, by simpa using hl, hτ⟩

/-! ## Resolution -/

/-- Resolves `R` with `A` on the unique literal of `A` whose negation is in `R`. Without such a
literal, `R` stays the same; with several, the step fails. -/
def resolveStep (R : LitSet) (A : List Lit) : Option LitSet :=
  match A.filter (fun l => R.contains (negLit l)) with
  | [] => some R
  | [p] => some ((R.erase (negLit p)).insertMany (A.filter (fun l => l != p)))
  | _ => none

theorem mem_resolvent {R : LitSet} {A : List Lit} {p l : Lit} :
    l ∈ (R.erase (negLit p)).insertMany (A.filter (fun l => l != p)) ↔
      (l ∈ R ∧ l ≠ negLit p) ∨ (l ∈ A ∧ l ≠ p) := by
  rw [Std.HashSet.mem_insertMany_list, Std.HashSet.mem_erase]
  simp only [List.contains_eq_mem, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq,
    beq_eq_false_iff_ne]
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inl ⟨h2, fun h => h1 h.symm⟩
    · exact Or.inr h
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inl ⟨fun h => h2 h.symm, h1⟩
    · exact Or.inr h

theorem resolveStep_sat {R R' : LitSet} {A : List Lit} {τ : Assignment}
    (h : resolveStep R A = some R') (hR : SatBy τ R) (hA : CNF.Clause.eval τ A = true) :
    SatBy τ R' := by
  unfold resolveStep at h
  split at h
  · cases h; exact hR
  · cases h
    obtain ⟨l, hl, hlτ⟩ := hR
    obtain ⟨a, ha, haτ⟩ := clause_eval_iff.mp hA
    rename_i p _
    by_cases hap : a = p
    · -- The pivot is true, so its negation in `R` is false, and `l` is another literal.
      refine ⟨l, mem_resolvent.mpr (Or.inl ⟨hl, ?_⟩), hlτ⟩
      rintro rfl
      subst hap
      obtain ⟨v, b⟩ := a
      simp only [negLit] at hlτ
      simp only at haτ
      rw [haτ] at hlτ
      cases b <;> simp at hlτ
    · exact ⟨a, mem_resolvent.mpr (Or.inr ⟨ha, hap⟩), haτ⟩
  · cases h

theorem resolveStep_noTaut {R R' : LitSet} {A : List Lit}
    (h : resolveStep R A = some R') (hR : NoTaut R) (hA : NoTautL A) : NoTaut R' := by
  unfold resolveStep at h
  split at h
  · cases h; exact hR
  · rename_i p hf
    cases h
    -- Every literal of `A` that clashes with `R` is the pivot.
    have clash : ∀ x, x ∈ A → negLit x ∈ R → x = p := by
      intro x hx hxR
      have : x ∈ A.filter (fun l => R.contains (negLit l)) :=
        List.mem_filter.mpr ⟨hx, Std.HashSet.mem_iff_contains.mp hxR⟩
      rw [hf] at this
      simpa using this
    intro l hl hl'
    rcases mem_resolvent.mp hl with ⟨h1, _⟩ | ⟨h1, h2⟩
    · rcases mem_resolvent.mp hl' with ⟨h3, _⟩ | ⟨h3, h4⟩
      · exact hR l h1 h3
      · exact h4 (clash _ h3 (by rw [negLit_negLit]; exact h1))
    · rcases mem_resolvent.mp hl' with ⟨h3, _⟩ | ⟨h3, _⟩
      · exact h2 (clash _ h1 h3)
      · exact hA l h1 h3
  · cases h

/-! ## The prefix, as used by reduction -/

/-- An extended prefix together with the position of each variable in it. -/
structure Ctx where
  pre : Array (Quant × Var)
  pos : Array Nat
  deriving Inhabited

namespace Ctx

/-- The prefix as a list. -/
def list (c : Ctx) : Prefix := c.pre.toList

def posOf (c : Ctx) (v : Nat) : Nat := c.pos.getD v 0

/-- The variable is universally quantified. -/
def isUniv (c : Ctx) (v : Nat) : Bool :=
  match c.pre[c.posOf v]? with
  | some (Quant.all, w) => w == v
  | _ => false

structure Valid (c : Ctx) : Prop where
  nodup : (Prefix.vars c.list).Nodup
  pos : ∀ i (h : i < c.pre.size), c.posOf (c.pre[i]).2 = i

theorem quantOf_of_isUniv {c : Ctx} (hc : c.Valid) {v : Nat} (h : c.isUniv v = true) :
    c.list.quantOf v = some Quant.all := by
  unfold isUniv at h
  split at h
  · rename_i w hw
    have hwv : w = v := by simpa using h
    subst hwv
    refine Prefix.quantOf_of_mem hc.nodup ?_
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw)
  · cases h

theorem level_eq {c : Ctx} (hc : c.Valid) {v : Nat} (h : v ∈ Prefix.vars c.list) :
    c.list.level v = c.posOf v := by
  unfold Prefix.level
  have hlt : (Prefix.vars c.list).findIdx (· == v) < (Prefix.vars c.list).length :=
    List.findIdx_lt_length_of_exists ⟨v, h, by simp⟩
  have hget := List.findIdx_getElem (w := hlt)
  simp only [beq_iff_eq] at hget
  have hlen : (Prefix.vars c.list).length = c.pre.size := by simp [Prefix.vars, list]
  generalize (Prefix.vars c.list).findIdx (· == v) = j at hlt hget
  have hjlt : j < c.pre.size := hlen ▸ hlt
  have hv : (c.pre[j]).2 = v := by
    have : (Prefix.vars c.list)[j] = (c.pre[j]).2 := by simp [Prefix.vars, list]
    rw [← this]; exact hget
  have hpos := hc.pos j hjlt
  rw [hv] at hpos
  exact hpos.symm

end Ctx

/-! ## Universal reduction -/

/-- One more than the largest position of a variable in `R` that is not universal. -/
def blockBound (c : Ctx) : List Lit → Nat
  | [] => 0
  | l :: R => if c.isUniv l.1 then blockBound c R else max (c.posOf l.1 + 1) (blockBound c R)

theorem lt_blockBound {c : Ctx} {R : List Lit} {l : Lit} (hl : l ∈ R)
    (hu : c.isUniv l.1 = false) : c.posOf l.1 < blockBound c R := by
  induction R with
  | nil => cases hl
  | cons x R ih =>
      rcases List.mem_cons.mp hl with rfl | hl
      · simp only [blockBound, hu, Bool.false_eq_true, if_false]; omega
      · have := ih hl
        simp only [blockBound]
        split <;> omega

/-- The literal is universal and comes after all variables that are not. -/
def removable (c : Ctx) (bound : Nat) (l : Lit) : Bool :=
  c.isUniv l.1 && decide (bound ≤ c.posOf l.1)

def reduceList (c : Ctx) (R : List Lit) : List Lit :=
  let bound := blockBound c R
  R.filter fun l => !removable c bound l

theorem mem_foldl_eraseVar {us : List Var} {C : CNF.Clause Var} {l : Lit} :
    l ∈ us.foldl eraseVar C ↔ l ∈ C ∧ l.1 ∉ us := by
  induction us generalizing C with
  | nil => simp
  | cons u us ih =>
      simp only [List.foldl_cons, ih, mem_eraseVar, List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- Reducing several universal variables, one after the other. -/
theorem evalPrefix_eraseVars {P : Prefix} (hnd : (Prefix.vars P).Nodup) {C₀ : CNF.Clause Var}
    (hnt : ¬ Taut C₀) (σ : Assignment) (Ψ : CNF Var) :
    ∀ (us : List Var) (C : CNF.Clause Var), C ⊆ C₀ →
      (∀ u ∈ us, P.quantOf u = some Quant.all ∧
        ∀ e ∈ clauseVars C₀, P.quantOf e = some Quant.ex → P.before e u) →
      evalPrefix P σ (Ψ.add C) → evalPrefix P σ (Ψ.add (us.foldl eraseVar C))
  | [], _, _, _, h => h
  | u :: us, C, hsub, hus, h => by
      have hu := hus u List.mem_cons_self
      have hC : ¬ Taut C := fun ht => hnt (ht.mono hsub)
      have hstep := evalPrefix_reduce hC P hnd hu.1
        (fun e he => hu.2 e (by
          obtain ⟨l, hl, rfl⟩ := mem_clauseVars.mp he
          exact mem_clauseVars.mpr ⟨l, hsub hl, rfl⟩)) σ Ψ h
      refine evalPrefix_eraseVars hnd hnt σ Ψ us (eraseVar C u) ?_ ?_ hstep
      · intro l hl; exact hsub (mem_eraseVar.mp hl).1
      · intro w hw; exact hus w (List.mem_cons_of_mem _ hw)

/-- Soundness of reduction for clauses given as lists. -/
theorem reduceList_sound {c : Ctx} (hc : c.Valid) {C : CNF.Clause Var} (hnt : ¬ Taut C)
    (σ : Assignment) (Ψ : CNF Var) (h : evalPrefix c.list σ (Ψ.add C)) :
    evalPrefix c.list σ (Ψ.add (reduceList c C)) := by
  let bound := blockBound c C
  let us : List Var := (C.filter fun l => removable c bound l).map Prod.fst
  have hus : ∀ u ∈ us, c.list.quantOf u = some Quant.all ∧
      ∀ e ∈ clauseVars C, c.list.quantOf e = some Quant.ex → c.list.before e u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    obtain ⟨_, hrem⟩ := List.mem_filter.mp hx
    simp only [removable, Bool.and_eq_true, decide_eq_true_eq] at hrem
    have hq := Ctx.quantOf_of_isUniv hc hrem.1
    refine ⟨hq, fun e he hex => ?_⟩
    obtain ⟨l, hl, rfl⟩ := mem_clauseVars.mp he
    have hnu : c.isUniv l.1 = false := by
      cases hiu : c.isUniv l.1
      · rfl
      · rw [Ctx.quantOf_of_isUniv hc hiu] at hex; cases hex
    have hlt := lt_blockBound hl hnu
    unfold Prefix.before
    rw [Ctx.level_eq hc (Prefix.mem_vars_of_quantOf hex),
      Ctx.level_eq hc (Prefix.mem_vars_of_quantOf hq)]
    omega
  have hstep := evalPrefix_eraseVars hc.nodup hnt σ Ψ us C (fun _ h => h) hus h
  refine evalPrefix_mono _ _ _ (fun τ hτ => ?_) σ hstep
  simp only [CNF.eval_add, Bool.and_eq_true] at hτ ⊢
  refine ⟨?_, hτ.2⟩
  obtain ⟨l, hl, hlτ⟩ := clause_eval_iff.mp hτ.1
  obtain ⟨hlC, hlus⟩ := mem_foldl_eraseVar.mp hl
  refine clause_eval_iff.mpr ⟨l, ?_, hlτ⟩
  refine List.mem_filter.mpr ⟨hlC, ?_⟩
  cases hrem : removable c (blockBound c C) l
  · rfl
  · exact absurd (List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hlC, hrem⟩, rfl⟩) hlus

/-- Removes the universal literals of `R` that come after all its existential variables. -/
def reduceSet (c : Ctx) (R : LitSet) : LitSet :=
  if (reduceList c R.toList).length == R.toList.length then R
  else Std.HashSet.ofList (reduceList c R.toList)

theorem mem_reduceSet {c : Ctx} {R : LitSet} {l : Lit} (h : l ∈ reduceSet c R) : l ∈ R := by
  unfold reduceSet at h
  split at h
  · exact h
  · have : l ∈ reduceList c R.toList := by simpa using h
    exact Std.HashSet.mem_toList.mp (List.mem_filter.mp this).1

theorem reduceSet_noTaut {c : Ctx} {R : LitSet} (h : NoTaut R) : NoTaut (reduceSet c R) :=
  fun l hl hl' => h l (mem_reduceSet hl) (mem_reduceSet hl')

theorem satBy_reduceSet {c : Ctx} {R : LitSet} {τ : Assignment}
    (h : CNF.Clause.eval τ (reduceList c R.toList) = true) : SatBy τ (reduceSet c R) := by
  obtain ⟨l, hl, hlτ⟩ := clause_eval_iff.mp h
  refine ⟨l, ?_, hlτ⟩
  unfold reduceSet
  split
  · exact Std.HashSet.mem_toList.mp (List.mem_filter.mp hl).1
  · simpa using hl

/-- If `R` follows from a CNF `Ψ` that is true under the prefix, then `Ψ` can be strengthened
to a true CNF from which the reduced clause follows. -/
theorem reduceSet_sound {c : Ctx} (hc : c.Valid) {R : LitSet} (hnt : NoTaut R)
    {σ : Assignment} {Ψ : CNF Var} (hΨ : evalPrefix c.list σ Ψ)
    (hR : ∀ τ, CNF.eval τ Ψ = true → SatBy τ R) :
    ∃ Ψ', evalPrefix c.list σ Ψ' ∧ (∀ τ, CNF.eval τ Ψ' = true → CNF.eval τ Ψ = true) ∧
      ∀ τ, CNF.eval τ Ψ' = true → SatBy τ (reduceSet c R) := by
  have hntL : ¬ Taut R.toList := not_taut_of_noTautL fun l hl hl' =>
    hnt l (Std.HashSet.mem_toList.mp hl) (Std.HashSet.mem_toList.mp hl')
  have h1 : evalPrefix c.list σ (Ψ.add R.toList) :=
    evalPrefix_mono _ _ _ (fun τ hτ => by
      simp only [CNF.eval_add, Bool.and_eq_true]
      exact ⟨satBy_toList.mpr (hR τ hτ), hτ⟩) σ hΨ
  refine ⟨Ψ.add (reduceList c R.toList), reduceList_sound hc hntL σ Ψ h1, ?_, ?_⟩
  · intro τ hτ
    simp only [CNF.eval_add, Bool.and_eq_true] at hτ
    exact hτ.2
  · intro τ hτ
    simp only [CNF.eval_add, Bool.and_eq_true] at hτ
    exact satBy_reduceSet hτ.1

end Qlrup
