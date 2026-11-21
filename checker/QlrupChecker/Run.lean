/-
# QlrupChecker.Run — checking a proof (proved)

`check q feed fuel` runs through the steps of a proof, delivered in blocks by `feed`, and
returns `some false` if the proof derives the empty clause, `some true` if it derives the empty
term, and `none` if the proof is rejected. The soundness theorems are

* `check_false_sound : check q feed fuel = some false → ¬ q.True`
* `check_true_sound : check q feed fuel = some true → q.True`

for every `feed`: nothing about the source of the steps is assumed.

Terms are handled by duality. A term of `q` is the negation of a clause of the dual formula
`q.dual` (quantifiers swapped, output negated), term resolution and existential reduction for
`q` are resolution and universal reduction for `q.dual`, and `q` is true iff `q.dual` is false
(`dual_true`). So the checker negates the literals of terms and checks them as clauses of
`q.dual`, in a database of their own.
-/
import QlrupChecker.Ext

namespace Qlrup

open Qbf Std.Sat Qcir

/-! ## The dual formula -/

/-- The negation of `q` in prenex form. -/
def Qcir.dual (q : Qcir) : Qcir :=
  { q with quants := q.quants.map Quant.dual, output := negLit q.output }

namespace Qcir

theorem dual_numVars (q : Qcir) : q.dual.numVars = q.numVars := by
  simp [dual, numVars]

theorem dual_wf (q : Qcir) : q.dual.wf = q.wf := by
  simp only [wf, dual, numVars, maxVar, negLit, Array.size_map]
  rfl

theorem dual_matrix (q : Qcir) (σ : Assignment) : q.dual.matrix σ = !q.matrix σ := by
  simp [matrix, extend, dual, numVars, litVal_negLit]

theorem prefixFrom_dual (k : Nat) (qs : List Quant) :
    prefixFrom k (qs.map Quant.dual) = Prefix.dual (prefixFrom k qs) := by
  induction qs generalizing k with
  | nil => rfl
  | cons qt qs ih => simp [prefixFrom, Prefix.dual, ih (k + 1)]

theorem dual_pre (q : Qcir) : q.dual.pre = Prefix.dual q.pre := by
  simp [pre, dual, prefixFrom_dual]

theorem evalPrefixF_dual (f : Assignment → Bool) :
    ∀ (p : Prefix) (σ : Assignment),
      evalPrefixF (Prefix.dual p) σ (fun τ => !f τ) ↔ ¬ evalPrefixF p σ f
  | [], σ => by simp [Prefix.dual, evalPrefixF]
  | (.ex, x) :: p, σ => by
      have ih := fun b => evalPrefixF_dual f p σ[x ↦ b]
      simp only [Prefix.dual, List.map_cons, Quant.dual, evalPrefixF, not_exists]
      exact forall_congr' ih
  | (.all, x) :: p, σ => by
      have ih := fun b => evalPrefixF_dual f p σ[x ↦ b]
      simp only [Prefix.dual, List.map_cons, Quant.dual, evalPrefixF, Classical.not_forall]
      exact exists_congr ih

/-- A formula is true iff its dual is false. -/
theorem dual_true (q : Qcir) : q.dual.True ↔ ¬ q.True := by
  have hm : q.dual.matrix = fun τ => !q.matrix τ := funext (dual_matrix q)
  unfold True
  rw [dual_pre, hm]
  exact evalPrefixF_dual _ _ _

end Qcir

/-! ## Proof steps -/

/-- A step of a proof (see `doc/proof-format.md`). -/
inductive Step where
  | orig (id : Nat) (term : Bool) (gate : Nat) (lits : List Lit)
  | derived (id : Nat) (term : Bool) (lits : List Lit) (ants : List Nat)
  | delete (ids : List Nat)
  deriving Inhabited

/-- A formula with extended prefixes for the formula and its dual. -/
structure Env where
  q : Qcir
  cC : Ctx
  cT : Ctx

def Env.ok (e : Env) : Bool := e.q.wf && ctxOk e.q e.cC && ctxOk e.q.dual e.cT

def mkEnv (q : Qcir) : Env := { q, cC := mkCtx q, cT := mkCtx q.dual }

/-- The clauses, and the negations of the terms, that have been added. -/
structure State where
  clauses : Db := ∅
  terms : Db := ∅

inductive Outcome where
  | more (st : State)
  | done (result : Bool)
  | fail

def eraseMany (db : Db) (ids : List Nat) : Db := ids.foldl (fun db id => db.erase id) db

def step (e : Env) (st : State) : Step → Outcome
  | .orig id term gate lits =>
    if st.clauses.contains id || st.terms.contains id then .fail
    else if term then
      let C := lits.map negLit
      if origOk e.q.dual gate C then .more { st with terms := st.terms.insert id C } else .fail
    else
      if origOk e.q gate lits then .more { st with clauses := st.clauses.insert id lits }
      else .fail
  | .derived id term lits ants =>
    if st.clauses.contains id || st.terms.contains id then .fail
    else if term then
      if derive e.cT st.terms (lits.map negLit) ants then
        if lits.isEmpty then .done true
        else .more { st with terms := st.terms.insert id (lits.map negLit) }
      else .fail
    else
      if derive e.cC st.clauses lits ants then
        if lits.isEmpty then .done false
        else .more { st with clauses := st.clauses.insert id lits }
      else .fail
  | .delete ids =>
    .more { clauses := eraseMany st.clauses ids, terms := eraseMany st.terms ids }

def runBlock (e : Env) : State → List Step → Outcome
  | st, [] => .more st
  | st, s :: ss =>
    match step e st s with
    | .more st' => runBlock e st' ss
    | .done r => .done r
    | .fail => .fail

/-- Checks the blocks `feed i`, `feed (i + 1)`, ... until an empty constraint is derived. -/
def run (e : Env) (feed : Nat → Option (Array Step)) : State → Nat → Nat → Option Bool
  | _, 0, _ => none
  | st, fuel + 1, i =>
    match feed i with
    | none => none
    | some block =>
      match runBlock e st block.toList with
      | .more st' => run e feed st' fuel (i + 1)
      | .done r => some r
      | .fail => none

/-- Checks a proof for `q`: `some false` if it shows that `q` is false, `some true` if it shows
that `q` is true, and `none` if it is rejected. -/
def check (q : Qcir) (feed : Nat → Option (Array Step)) (fuel : Nat) : Option Bool :=
  let e := mkEnv q
  if e.ok then run e feed {} fuel 0 else none

/-! ## Soundness -/

def State.Inv (e : Env) (st : State) : Prop :=
  Qlrup.Inv e.q e.cC st.clauses ∧ Qlrup.Inv e.q.dual e.cT st.terms

/-- What a result means. -/
def Meaning (q : Qcir) (r : Bool) : Prop := if r then q.True else ¬ q.True

theorem false_of_refuted {q : Qcir} {c : Ctx} (hwf : q.wf = true) (hok : ctxOk q c = true)
    {db : Db} (hinv : Inv q c db) {ants : List Nat}
    (h : derive c db ([] : List Lit) ants = true) : ¬ q.True := by
  obtain ⟨hvalid, hext⟩ := ctxOk_sound hok
  exact fun ht => refuted_sound hvalid hinv h (tseitin_evalPrefix hwf hext ht)

theorem step_sound {e : Env} (he : e.ok = true) {st : State} (hinv : st.Inv e) (s : Step) :
    (∀ st', step e st s = .more st' → st'.Inv e) ∧
      (∀ r, step e st s = .done r → Meaning e.q r) := by
  simp only [Env.ok, Bool.and_eq_true] at he
  obtain ⟨⟨hwf, hokC⟩, hokT⟩ := he
  obtain ⟨hC, hT⟩ := hinv
  cases s with
  | orig id term gate lits =>
      refine ⟨fun st' h => ?_, fun r h => ?_⟩
      · simp only [step] at h
        split at h
        · cases h
        · split at h
          · split at h
            · rename_i hok; cases h; exact ⟨hC, hT.addOrig id hok⟩
            · cases h
          · split at h
            · rename_i hok; cases h; exact ⟨hC.addOrig id hok, hT⟩
            · cases h
      · simp only [step] at h
        split at h
        · cases h
        · split at h
          · split at h <;> cases h
          · split at h <;> cases h
  | derived id term lits ants =>
      refine ⟨fun st' h => ?_, fun r h => ?_⟩
      · simp only [step] at h
        split at h
        · cases h
        · split at h
          · split at h
            · rename_i hok
              split at h
              · cases h
              · cases h; exact ⟨hC, hT.addDerived (ctxOk_sound hokT).1 id hok⟩
            · cases h
          · split at h
            · rename_i hok
              split at h
              · cases h
              · cases h; exact ⟨hC.addDerived (ctxOk_sound hokC).1 id hok, hT⟩
            · cases h
      · simp only [step] at h
        split at h
        · cases h
        · split at h
          · split at h
            · rename_i hok
              split at h
              · rename_i hemp
                cases h
                have hl : lits = [] := List.isEmpty_iff.mp hemp
                subst hl
                have hf := false_of_refuted (by rw [dual_wf]; exact hwf) hokT hT hok
                simp only [Meaning, if_true]
                exact Classical.not_not.mp fun hn => hf ((dual_true e.q).mpr hn)
              · cases h
            · cases h
          · split at h
            · rename_i hok
              split at h
              · rename_i hemp
                cases h
                have hl : lits = [] := List.isEmpty_iff.mp hemp
                subst hl
                simpa [Meaning] using false_of_refuted hwf hokC hC hok
              · cases h
            · cases h
  | delete ids =>
      refine ⟨fun st' h => ?_, fun r h => ?_⟩
      · simp only [step] at h
        cases h
        exact ⟨hC.delete ids, hT.delete ids⟩
      · simp only [step] at h
        cases h

theorem runBlock_sound {e : Env} (he : e.ok = true) :
    ∀ (ss : List Step) {st : State}, st.Inv e →
      (∀ st', runBlock e st ss = .more st' → st'.Inv e) ∧
        (∀ r, runBlock e st ss = .done r → Meaning e.q r)
  | [], st, hinv => by
      refine ⟨fun st' h => ?_, fun r h => ?_⟩
      · simp only [runBlock] at h; cases h; exact hinv
      · simp only [runBlock] at h; cases h
  | s :: ss, st, hinv => by
      obtain ⟨hmore, hdone⟩ := step_sound he hinv s
      refine ⟨fun st' h => ?_, fun r h => ?_⟩
      · simp only [runBlock] at h
        split at h
        · rename_i st₁ hst
          exact (runBlock_sound he ss (hmore st₁ hst)).1 st' h
        · cases h
        · cases h
      · simp only [runBlock] at h
        split at h
        · rename_i st₁ hst
          exact (runBlock_sound he ss (hmore st₁ hst)).2 r h
        · rename_i r' hst
          cases h
          exact hdone r hst
        · cases h

theorem run_sound {e : Env} (he : e.ok = true) (feed : Nat → Option (Array Step)) :
    ∀ (fuel : Nat) (st : State) (i : Nat) {r : Bool}, st.Inv e →
      run e feed st fuel i = some r → Meaning e.q r
  | 0, _, _, _, _, h => by simp [run] at h
  | fuel + 1, st, i, r, hinv, h => by
      simp only [run] at h
      split at h
      · cases h
      · rename_i block _
        obtain ⟨hmore, hdone⟩ := runBlock_sound he block.toList hinv
        split at h
        · rename_i st' hst
          exact run_sound he feed fuel st' (i + 1) (hmore st' hst) h
        · rename_i r' hst
          cases h
          exact hdone r hst
        · cases h

theorem check_sound {q : Qcir} {feed : Nat → Option (Array Step)} {fuel : Nat} {r : Bool}
    (h : check q feed fuel = some r) : Meaning q r := by
  simp only [check] at h
  split at h
  · rename_i he
    exact run_sound he feed fuel {} 0 ⟨Inv.empty _ _, Inv.empty _ _⟩ h
  · cases h

/-- A proof that derives the empty clause shows that the formula is false. -/
theorem check_false_sound {q : Qcir} {feed : Nat → Option (Array Step)} {fuel : Nat}
    (h : check q feed fuel = some false) : ¬ q.True := by
  simpa [Meaning] using check_sound h

/-- A proof that derives the empty term shows that the formula is true. -/
theorem check_true_sound {q : Qcir} {feed : Nat → Option (Array Step)} {fuel : Nat}
    (h : check q feed fuel = some true) : q.True := by
  simpa [Meaning] using check_sound h

/-! ## Reflection

The statements used by the `qlrup_true` and `qlrup_false` commands, with a Boolean hypothesis
that can be discharged by evaluating the checker. -/

/-- More blocks than any proof has. -/
def streamFuel : Nat := 1 <<< 40

theorem true_of_check (q : Qcir) (feed : Nat → Option (Array Step)) (fuel : Nat)
    (h : (check q feed fuel == some true) = true) : q.True :=
  check_true_sound (by simpa using h)

theorem false_of_check (q : Qcir) (feed : Nat → Option (Array Step)) (fuel : Nat)
    (h : (check q feed fuel == some false) = true) : ¬ q.True :=
  check_false_sound (by simpa using h)

end Qlrup
