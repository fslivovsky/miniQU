/-
# QlrupChecker.Check — checking proof steps (proved)

A database of clauses over the variables and gates of a formula `q`, the checks for original
and derived clauses, and the invariant they maintain: if the Tseitin encoding of `q` is true
under the extended prefix, then so is a CNF from which all clauses in the database follow
(`Inv`). In particular, the empty clause cannot be derived if `q` is true (`refuted_sound`).
-/
import QlrupChecker.Derive
import Std.Data.HashMap

namespace Qlrup

open Qbf Std.Sat Qcir

/-- The clauses that have been added and not deleted, by identifier. -/
abbrev Db := Std.HashMap Nat (List Lit)

/-- The clauses in the database do not contain complementary literals and follow from `Ψ`. -/
def DbOk (Ψ : CNF Var) (db : Db) : Prop :=
  ∀ (id : Nat) (C : List Lit), db[id]? = some C →
    NoTautL C ∧ ∀ τ, CNF.eval τ Ψ = true → CNF.Clause.eval τ C = true

theorem DbOk.mono {Ψ Ψ' : CNF Var} {db : Db} (h : DbOk Ψ db)
    (himp : ∀ τ, CNF.eval τ Ψ' = true → CNF.eval τ Ψ = true) : DbOk Ψ' db :=
  fun id C hC => ⟨(h id C hC).1, fun τ hτ => (h id C hC).2 τ (himp τ hτ)⟩

theorem DbOk.insert {Ψ : CNF Var} {db : Db} (h : DbOk Ψ db) {id : Nat} {C : List Lit}
    (hnt : NoTautL C) (hC : ∀ τ, CNF.eval τ Ψ = true → CNF.Clause.eval τ C = true) :
    DbOk Ψ (db.insert id C) := by
  intro id' C' hC'
  rw [Std.HashMap.getElem?_insert] at hC'
  split at hC'
  · cases hC'; exact ⟨hnt, hC⟩
  · exact h id' C' hC'

theorem DbOk.erase {Ψ : CNF Var} {db : Db} (h : DbOk Ψ db) (id : Nat) :
    DbOk Ψ (db.erase id) := by
  intro id' C' hC'
  rw [Std.HashMap.getElem?_erase] at hC'
  split at hC'
  · cases hC'
  · exact h id' C' hC'

theorem DbOk.eraseMany {Ψ : CNF Var} (ids : List Nat) :
    ∀ {db : Db}, DbOk Ψ db → DbOk Ψ (ids.foldl (fun db id => db.erase id) db) := by
  induction ids with
  | nil => intro db h; exact h
  | cons id ids ih => intro db h; exact ih (h.erase id)

/-! ## Derived clauses -/

/-- Resolves `R` with the clauses `as`, in this order, reducing after each step. -/
def chain (c : Ctx) (db : Db) : LitSet → List Nat → Option LitSet
  | R, [] => some R
  | R, a :: as =>
    match db[a]? with
    | none => none
    | some A =>
      match resolveStep R A with
      | none => none
      | some R' => chain c db (reduceSet c R') as

theorem chain_sound {c : Ctx} (hc : c.Valid) {db : Db} {σ : Assignment} :
    ∀ (as : List Nat) (R : LitSet) (Ψ : CNF Var) {R' : LitSet},
      evalPrefix c.list σ Ψ → DbOk Ψ db → NoTaut R →
      (∀ τ, CNF.eval τ Ψ = true → SatBy τ R) →
      chain c db R as = some R' →
      ∃ Ψ', evalPrefix c.list σ Ψ' ∧ (∀ τ, CNF.eval τ Ψ' = true → CNF.eval τ Ψ = true) ∧
        ∀ τ, CNF.eval τ Ψ' = true → SatBy τ R'
  | [], R, Ψ, R', hΨ, _, _, hR, h => by
      simp only [chain, Option.some.injEq] at h
      subst h
      exact ⟨Ψ, hΨ, fun _ h => h, hR⟩
  | a :: as, R, Ψ, R', hΨ, hdb, hnt, hR, h => by
      simp only [chain] at h
      split at h
      · cases h
      · rename_i A hA
        split at h
        · cases h
        · rename_i R₁ hres
          obtain ⟨hAnt, hAsat⟩ := hdb a A hA
          have hnt₁ : NoTaut R₁ := resolveStep_noTaut hres hnt hAnt
          have hR₁ : ∀ τ, CNF.eval τ Ψ = true → SatBy τ R₁ :=
            fun τ hτ => resolveStep_sat hres (hR τ hτ) (hAsat τ hτ)
          obtain ⟨Ψ₁, hΨ₁, himp₁, hred⟩ := reduceSet_sound hc hnt₁ hΨ hR₁
          obtain ⟨Ψ₂, hΨ₂, himp₂, hfin⟩ :=
            chain_sound hc as _ Ψ₁ hΨ₁ (hdb.mono himp₁) (reduceSet_noTaut hnt₁) hred h
          exact ⟨Ψ₂, hΨ₂, fun τ hτ => himp₁ τ (himp₂ τ hτ), hfin⟩

/-- The clause does not contain complementary literals; `cs` is its set of literals. -/
def noTautB (C : List Lit) (cs : LitSet) : Bool := C.all fun l => !cs.contains (negLit l)

theorem noTautL_of_noTautB {C : List Lit} (h : noTautB C (Std.HashSet.ofList C) = true) :
    NoTautL C := by
  intro l hl hl'
  have := List.all_eq_true.mp h l hl
  simp only [Bool.not_eq_true', Std.HashSet.contains_ofList, List.contains_eq_mem,
    decide_eq_false_iff_not] at this
  exact this hl'

/-- Checks that the clause `C` is derived from the clauses `ants`. -/
def derive (c : Ctx) (db : Db) (C : List Lit) (ants : List Nat) : Bool :=
  match ants with
  | [] => false
  | a :: as =>
    match db[a]? with
    | none => false
    | some A =>
      match chain c db (reduceSet c (Std.HashSet.ofList A)) as with
      | none => false
      | some R =>
        let cs := Std.HashSet.ofList C
        R.toList.all (fun l => cs.contains l) && noTautB C cs

theorem derive_sound {c : Ctx} (hc : c.Valid) {db : Db} {σ : Assignment} {Ψ : CNF Var}
    {C : List Lit} {ants : List Nat} (hΨ : evalPrefix c.list σ Ψ) (hdb : DbOk Ψ db)
    (h : derive c db C ants = true) :
    NoTautL C ∧ ∃ Ψ', evalPrefix c.list σ Ψ' ∧
      (∀ τ, CNF.eval τ Ψ' = true → CNF.eval τ Ψ = true) ∧
      ∀ τ, CNF.eval τ Ψ' = true → CNF.Clause.eval τ C = true := by
  unfold derive at h
  split at h
  · cases h
  · rename_i a as
    split at h
    · cases h
    · rename_i A hA
      split at h
      · cases h
      · rename_i R hchain
        simp only [Bool.and_eq_true] at h
        obtain ⟨hsub, hntC⟩ := h
        obtain ⟨hAnt, hAsat⟩ := hdb a A hA
        have hnt₀ : NoTaut (Std.HashSet.ofList A) := by
          intro l hl hl'
          exact hAnt l (by simpa using hl) (by simpa using hl')
        have hR₀ : ∀ τ, CNF.eval τ Ψ = true → SatBy τ (Std.HashSet.ofList A) :=
          fun τ hτ => satBy_ofList.mpr (hAsat τ hτ)
        obtain ⟨Ψ₁, hΨ₁, himp₁, hred⟩ := reduceSet_sound hc hnt₀ hΨ hR₀
        obtain ⟨Ψ₂, hΨ₂, himp₂, hfin⟩ :=
          chain_sound hc as _ Ψ₁ hΨ₁ (hdb.mono himp₁) (reduceSet_noTaut hnt₀) hred hchain
        refine ⟨noTautL_of_noTautB hntC, Ψ₂, hΨ₂, fun τ hτ => himp₁ τ (himp₂ τ hτ), ?_⟩
        intro τ hτ
        obtain ⟨l, hl, hlτ⟩ := hfin τ hτ
        have := List.all_eq_true.mp hsub l (Std.HashSet.mem_toList.mpr hl)
        simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq] at this
        exact clause_eval_iff.mpr ⟨l, this, hlτ⟩

/-! ## Original clauses -/

/-- The clause `C` contains a clause of the gate with number `gate`, or the output literal if
`gate` is `0`. -/
def origOk (q : Qcir) (gate : Nat) (C : List Lit) : Bool :=
  let cs := Std.HashSet.ofList C
  noTautB C cs &&
    if gate == 0 then cs.contains q.output
    else if gate ≤ q.numVars then false
    else
      match q.gates[gate - (q.numVars + 1)]? with
      | none => false
      | some g => (g.clauses gate).any fun D => D.all fun l => cs.contains l

theorem clause_eval_of_subset {τ : Assignment} {D C : List Lit}
    (hsub : D.all (fun l => (Std.HashSet.ofList C).contains l) = true)
    (hD : CNF.Clause.eval τ D = true) : CNF.Clause.eval τ C = true := by
  obtain ⟨l, hl, hlτ⟩ := clause_eval_iff.mp hD
  have := List.all_eq_true.mp hsub l hl
  simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq] at this
  exact clause_eval_iff.mpr ⟨l, this, hlτ⟩

theorem origOk_sound {q : Qcir} {gate : Nat} {C : List Lit} (h : origOk q gate C = true) :
    NoTautL C ∧ ∀ τ, CNF.eval τ q.tseitin = true → CNF.Clause.eval τ C = true := by
  simp only [origOk, Bool.and_eq_true] at h
  obtain ⟨hnt, h⟩ := h
  refine ⟨noTautL_of_noTautB hnt, fun τ hτ => ?_⟩
  have hT := cnf_eval_tseitin.mp hτ
  split at h
  · -- output
    have hout : CNF.Clause.eval τ ([q.output] : List Lit) = true := hT _ List.mem_cons_self
    refine clause_eval_of_subset (D := ([q.output] : List Lit)) ?_ hout
    simpa using h
  · split at h
    · cases h
    · rename_i hg0 hgn
      split at h
      · cases h
      · rename_i g hg
        obtain ⟨D, hD, hsub⟩ := List.any_eq_true.mp h
        refine clause_eval_of_subset hsub (hT D (List.mem_cons_of_mem _ ?_))
        have hg' : q.gates.toList[gate - (q.numVars + 1)]? = some g := by
          rw [Array.getElem?_toList]; exact hg
        have hmem := mem_tseitinFrom (k := q.numVars + 1) hg' D
        have hnum : q.numVars + 1 + (gate - (q.numVars + 1)) = gate := by omega
        rw [hnum] at hmem
        exact hmem hD

/-! ## The invariant -/

/-- If the encoding of `q` is true under the prefix `c`, then so is a CNF that implies the
encoding and all clauses in the database. -/
def Inv (q : Qcir) (c : Ctx) (db : Db) : Prop :=
  evalPrefix c.list (fun _ => false) q.tseitin →
    ∃ Ψ, evalPrefix c.list (fun _ => false) Ψ ∧
      (∀ τ, CNF.eval τ Ψ = true → CNF.eval τ q.tseitin = true) ∧ DbOk Ψ db

theorem Inv.empty (q : Qcir) (c : Ctx) : Inv q c ∅ :=
  fun h => ⟨q.tseitin, h, fun _ h => h, fun id C hC => by simp at hC⟩

theorem Inv.addOrig {q : Qcir} {c : Ctx} {db : Db} (hinv : Inv q c db) {gate : Nat}
    (id : Nat) {C : List Lit} (h : origOk q gate C = true) : Inv q c (db.insert id C) := by
  intro hT
  obtain ⟨Ψ, hΨ, himp, hdb⟩ := hinv hT
  obtain ⟨hnt, hC⟩ := origOk_sound h
  exact ⟨Ψ, hΨ, himp, hdb.insert hnt fun τ hτ => hC τ (himp τ hτ)⟩

theorem Inv.addDerived {q : Qcir} {c : Ctx} (hc : c.Valid) {db : Db} (hinv : Inv q c db)
    (id : Nat) {C : List Lit} {ants : List Nat} (h : derive c db C ants = true) :
    Inv q c (db.insert id C) := by
  intro hT
  obtain ⟨Ψ, hΨ, himp, hdb⟩ := hinv hT
  obtain ⟨hnt, Ψ', hΨ', himp', hC⟩ := derive_sound hc hΨ hdb h
  exact ⟨Ψ', hΨ', fun τ hτ => himp τ (himp' τ hτ), (hdb.mono himp').insert hnt hC⟩

theorem Inv.delete {q : Qcir} {c : Ctx} {db : Db} (hinv : Inv q c db) (ids : List Nat) :
    Inv q c (ids.foldl (fun db id => db.erase id) db) := by
  intro hT
  obtain ⟨Ψ, hΨ, himp, hdb⟩ := hinv hT
  exact ⟨Ψ, hΨ, himp, DbOk.eraseMany ids hdb⟩

/-- If the empty clause can be derived, the encoding of `q` is false under the prefix `c`. -/
theorem refuted_sound {q : Qcir} {c : Ctx} (hc : c.Valid) {db : Db} (hinv : Inv q c db)
    {ants : List Nat} (h : derive c db ([] : List Lit) ants = true) :
    ¬ evalPrefix c.list (fun _ => false) q.tseitin := by
  intro hT
  obtain ⟨Ψ, hΨ, _, hdb⟩ := hinv hT
  obtain ⟨_, Ψ', hΨ', _, hC⟩ := derive_sound hc hΨ hdb h
  refine not_evalPrefix_of_unsat _ _ Ψ' (fun τ => ?_) hΨ'
  cases hτ : CNF.eval τ Ψ'
  · rfl
  · have := hC τ hτ
    simp at this

end Qlrup
