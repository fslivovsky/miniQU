/-
# QlrupChecker.Tseitin — the Tseitin encoding and the prefix position of gate variables (proved)

For a formula `q`, `q.tseitin` is the CNF consisting of the output literal and the clauses that
define each gate, over the variables of `q` and one variable per gate.

An *extended prefix* `P` (`ExtValid q P`) quantifies the gate variables existentially, somewhere
after the variables and gates they depend on, and otherwise coincides with the prefix of `q`.
The main result, `tseitin_evalPrefix`, says that if `q` is true then so is the CNF `q.tseitin`
under any extended prefix: the existential player sets each gate variable to the value of the
gate, which is determined by the variables assigned so far.

`extOk` is an executable test for `ExtValid`.
-/
import QlrupChecker.Qcir

namespace Qlrup

open Qbf Std.Sat

namespace Qcir

/-! ## The encoding -/

def negLit (l : Lit) : Lit := (l.1, !l.2)

/-- The clauses defining gate number `num`. -/
def _root_.Qlrup.Gate.clauses (g : Gate) (num : Nat) : List (CNF.Clause Var) :=
  match g.kind with
  | .and => ((num, true) :: g.inputs.map negLit) :: g.inputs.map fun l => [(num, false), l]
  | .or => ((num, false) :: g.inputs) :: g.inputs.map fun l => [(num, true), negLit l]

def tseitinFrom : Nat → List Gate → List (CNF.Clause Var)
  | _, [] => []
  | k, g :: gs => g.clauses k ++ tseitinFrom (k + 1) gs

def tseitinClauses (q : Qcir) : List (CNF.Clause Var) :=
  [q.output] :: tseitinFrom (q.numVars + 1) q.gates.toList

def tseitin (q : Qcir) : CNF Var := { clauses := q.tseitinClauses.toArray }

/-! ## Evaluation lemmas -/

theorem litVal_congr {σ₁ σ₂ : Assignment} {l : Lit} (h : σ₁ l.1 = σ₂ l.1) :
    litVal σ₁ l = litVal σ₂ l := by
  simp [litVal, h]

theorem litVal_negLit (σ : Assignment) (l : Lit) : litVal σ (negLit l) = !litVal σ l := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases h : σ v <;> simp [litVal, negLit, h]

theorem clause_eval_eq (σ : Assignment) (C : CNF.Clause Var) :
    CNF.Clause.eval σ C = C.any (litVal σ) := by
  induction C with
  | nil => rfl
  | cons l C ih => simp [CNF.Clause.eval_cons, ih, litVal]

theorem gate_eval_congr {σ₁ σ₂ : Assignment} (g : Gate)
    (h : ∀ l ∈ g.inputs, σ₁ l.1 = σ₂ l.1) : g.eval σ₁ = g.eval σ₂ := by
  have hl : ∀ l ∈ g.inputs, litVal σ₁ l = litVal σ₂ l := fun l hl => litVal_congr (h l hl)
  unfold Gate.eval
  cases g.kind
  · rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true]
    exact ⟨fun h l hm => hl l hm ▸ h l hm, fun h l hm => (hl l hm).symm ▸ h l hm⟩
  · rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    exact ⟨fun ⟨l, hm, h⟩ => ⟨l, hm, hl l hm ▸ h⟩, fun ⟨l, hm, h⟩ => ⟨l, hm, (hl l hm).symm ▸ h⟩⟩

/-- The gates `gs`, numbered from `k`, have their values under `σ`. -/
def Consistent (k : Nat) (gs : List Gate) (σ : Assignment) : Prop :=
  ∀ i g, gs[i]? = some g → σ (k + i) = g.eval σ

theorem Consistent.tail {k : Nat} {g : Gate} {gs : List Gate} {σ : Assignment}
    (h : Consistent k (g :: gs) σ) : Consistent (k + 1) gs σ := by
  intro i g' hg'
  have := h (i + 1) g' (by simpa using hg')
  have e : k + 1 + i = k + (i + 1) := by omega
  rw [e]; exact this

theorem extendFrom_fix {k : Nat} {gs : List Gate} {σ : Assignment}
    (h : Consistent k gs σ) : extendFrom k gs σ = σ := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
      have h0 : σ k = g.eval σ := by simpa using h 0 g rfl
      have hset : σ[k ↦ g.eval σ] = σ := by
        funext y
        by_cases hy : y = k
        · subst hy; simp [h0]
        · simp [Assignment.set_other _ _ hy]
      simp only [extendFrom, hset]
      exact ih h.tail

/-- The clauses of a gate hold under an assignment that gives the gate its value. -/
theorem gate_clauses_eval {g : Gate} {num : Nat} {σ : Assignment} (h : σ num = g.eval σ) :
    ∀ C ∈ g.clauses num, CNF.Clause.eval σ C = true := by
  intro C hC
  rw [clause_eval_eq]
  unfold Gate.clauses at hC
  unfold Gate.eval at h
  cases hk : g.kind <;> simp only [hk] at hC h
  · -- and
    rcases List.mem_cons.mp hC with rfl | hC
    · by_cases hall : g.inputs.all (litVal σ) = true
      · simp [litVal, h, hall]
      · simp only [Bool.not_eq_true] at hall
        obtain ⟨l, hl, hlv⟩ : ∃ l ∈ g.inputs, litVal σ l = false := by
          simpa using hall
        simp only [List.any_cons, Bool.or_eq_true, List.any_eq_true, List.mem_map]
        exact Or.inr ⟨negLit l, ⟨l, hl, rfl⟩, by simp [litVal_negLit, hlv]⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hC
      by_cases hlv : litVal σ l = true
      · simp [hlv]
      · have hall : g.inputs.all (litVal σ) = false := by
          simp only [Bool.not_eq_true] at hlv
          exact List.all_eq_false.mpr ⟨l, hl, by simp [hlv]⟩
        simp [litVal, h, hall]
  · -- or
    rcases List.mem_cons.mp hC with rfl | hC
    · by_cases hany : g.inputs.any (litVal σ) = true
      · simp [hany]
      · simp only [Bool.not_eq_true] at hany
        simp [litVal, h, hany]
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hC
      by_cases hlv : litVal σ l = true
      · have hany : g.inputs.any (litVal σ) = true := List.any_eq_true.mpr ⟨l, hl, hlv⟩
        simp [litVal, h, hany]
      · simp only [Bool.not_eq_true] at hlv
        simp [litVal_negLit, hlv]

theorem tseitinFrom_eval {k : Nat} {gs : List Gate} {σ : Assignment}
    (h : Consistent k gs σ) : ∀ C ∈ tseitinFrom k gs, CNF.Clause.eval σ C = true := by
  induction gs generalizing k with
  | nil => intro C hC; cases hC
  | cons g gs ih =>
      intro C hC
      rcases List.mem_append.mp hC with hC | hC
      · exact gate_clauses_eval (by simpa using h 0 g rfl) C hC
      · exact ih h.tail C hC

theorem mem_tseitinFrom {k : Nat} {gs : List Gate} {i : Nat} {g : Gate}
    (hg : gs[i]? = some g) : ∀ C ∈ g.clauses (k + i), C ∈ tseitinFrom k gs := by
  induction gs generalizing k i with
  | nil => simp at hg
  | cons g' gs ih =>
      intro C hC
      cases i with
      | zero =>
          obtain rfl : g' = g := by simpa using hg
          exact List.mem_append.mpr (Or.inl (by simpa using hC))
      | succ i =>
          refine List.mem_append.mpr (Or.inr (ih (k := k + 1) (by simpa using hg) C ?_))
          have : k + 1 + i = k + (i + 1) := by omega
          rw [this]; exact hC

theorem cnf_eval_tseitin {q : Qcir} {σ : Assignment} :
    CNF.eval σ q.tseitin = true ↔ ∀ C ∈ q.tseitinClauses, CNF.Clause.eval σ C = true := by
  simp [tseitin, CNF.eval]

/-- An assignment that gives every gate its value and makes the output true satisfies the
encoding. -/
theorem tseitin_eval {q : Qcir} {σ : Assignment}
    (hc : Consistent (q.numVars + 1) q.gates.toList σ) (hout : litVal σ q.output = true) :
    CNF.eval σ q.tseitin = true := by
  rw [cnf_eval_tseitin]
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · rw [clause_eval_eq]; simp [hout]
  · exact tseitinFrom_eval hc C hC

/-! ## The matrix only depends on the variables -/

theorem extendFrom_congr {k : Nat} {gs : List Gate} {σ₁ σ₂ : Assignment}
    (hwf : gatesWf k gs = true) (h : ∀ v, v < k → σ₁ v = σ₂ v) :
    ∀ v, v < k + gs.length → extendFrom k gs σ₁ v = extendFrom k gs σ₂ v := by
  induction gs generalizing k σ₁ σ₂ with
  | nil => intro v hv; exact h v (by simpa using hv)
  | cons g gs ih =>
      simp only [gatesWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
      obtain ⟨hin, hwf'⟩ := hwf
      have he : g.eval σ₁ = g.eval σ₂ := gate_eval_congr g fun l hl => h _ (hin l hl).2
      intro v hv
      simp only [extendFrom]
      refine ih hwf' ?_ v (by simp only [List.length_cons] at hv; omega)
      intro w hw
      by_cases hwk : w = k
      · subst hwk; simp [he]
      · rw [Assignment.set_other _ _ hwk, Assignment.set_other _ _ hwk]
        exact h w (by omega)

theorem matrix_congr {q : Qcir} (hwf : q.wf = true) {σ₁ σ₂ : Assignment}
    (h : ∀ v, v ≤ q.numVars → σ₁ v = σ₂ v) : q.matrix σ₁ = q.matrix σ₂ := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨_, hg⟩, _, hout⟩ := hwf
  unfold matrix
  refine litVal_congr (extendFrom_congr hg (fun v hv => h v (by omega)) _ ?_)
  simp only [maxVar] at hout
  simp only [Array.length_toList]
  vomega

theorem evalPrefixF_congr {f : Assignment → Bool} {n : Nat}
    (hf : ∀ σ₁ σ₂ : Assignment, (∀ v, v ≤ n → σ₁ v = σ₂ v) → f σ₁ = f σ₂) :
    ∀ (p : Prefix) (σ₁ σ₂ : Assignment), (∀ v, v ≤ n → σ₁ v = σ₂ v) →
      evalPrefixF p σ₁ f → evalPrefixF p σ₂ f
  | [], σ₁, σ₂, h, he => by
      simp only [evalPrefixF] at he ⊢
      rw [← hf σ₁ σ₂ h]; exact he
  | (qt, x) :: p, σ₁, σ₂, h, he => by
      have hset : ∀ b : Bool, ∀ v, v ≤ n → σ₁[x ↦ b] v = σ₂[x ↦ b] v := by
        intro b v hv
        by_cases hvx : v = x
        · subst hvx; simp
        · rw [Assignment.set_other _ _ hvx, Assignment.set_other _ _ hvx]; exact h v hv
      cases qt with
      | ex =>
          obtain ⟨b, hb⟩ := he
          exact ⟨b, evalPrefixF_congr hf p _ _ (hset b) hb⟩
      | all =>
          intro b
          exact evalPrefixF_congr hf p _ _ (hset b) (he b)

/-! ## Extended prefixes -/

/-- `P` extends the prefix of `q` by existential gate variables that come after their inputs. -/
structure ExtValid (q : Qcir) (P : Prefix) : Prop where
  nodup : (Prefix.vars P).Nodup
  /-- Without the gate variables, `P` is the prefix of `q`. -/
  restrict : P.filter (fun qx => decide (qx.2 ≤ q.numVars)) = q.pre
  /-- Every other entry is the variable of a gate, existentially quantified, and the inputs of
  the gate come earlier. -/
  gate : ∀ P₁ qt v P₂, P = P₁ ++ (qt, v) :: P₂ → q.numVars < v →
    qt = Quant.ex ∧ ∃ g, q.gates.toList[v - (q.numVars + 1)]? = some g ∧
      ∀ l ∈ g.inputs, l.1 ∈ Prefix.vars P₁
  /-- Every gate has a variable. -/
  all : ∀ k, k < q.gates.size → q.numVars + 1 + k ∈ Prefix.vars P

/-- The invariant of the induction below: the gates whose variables are in `P₁` have their
values under `σ`, and their inputs are in `P₁` as well. -/
def Settled (q : Qcir) (P₁ : Prefix) (σ : Assignment) : Prop :=
  ∀ k g, q.gates.toList[k]? = some g → q.numVars + 1 + k ∈ Prefix.vars P₁ →
    σ (q.numVars + 1 + k) = g.eval σ ∧ ∀ l ∈ g.inputs, l.1 ∈ Prefix.vars P₁

theorem tseitin_evalPrefix_aux {q : Qcir} (hwf : q.wf = true) {P : Prefix}
    (hv : ExtValid q P) :
    ∀ (S P₁ : Prefix) (σ : Assignment), P = P₁ ++ S → Settled q P₁ σ →
      evalPrefixF (S.filter fun qx => decide (qx.2 ≤ q.numVars)) σ q.matrix →
      evalPrefix S σ q.tseitin
  | [], P₁, σ, hP, hs, he => by
      simp only [List.append_nil] at hP
      subst hP
      simp only [List.filter_nil, evalPrefixF] at he
      have hc : Consistent (q.numVars + 1) q.gates.toList σ := by
        intro i g hg
        have hi : i < q.gates.size := by
          have := (List.getElem?_eq_some_iff.mp hg).1
          simpa using this
        exact (hs i g hg (hv.all i hi)).1
      simp only [evalPrefix_nil]
      refine tseitin_eval hc ?_
      have : q.extend σ = σ := extendFrom_fix hc
      simpa [matrix, this] using he
  | (qt, v) :: S, P₁, σ, hP, hs, he => by
      have hP' : P = (P₁ ++ [(qt, v)]) ++ S := by simp [hP]
      have hnd := hv.nodup
      rw [hP] at hnd
      simp only [Prefix.vars_append, Prefix.vars_cons] at hnd
      have hvP₁ : v ∉ Prefix.vars P₁ := fun hmem =>
        (List.nodup_append.mp hnd).2.2 v hmem v (List.mem_cons_self) rfl
      -- Assigning `v` does not disturb the gates settled so far.
      have keep : ∀ b : Bool, ∀ k g, q.gates.toList[k]? = some g →
          q.numVars + 1 + k ∈ Prefix.vars P₁ →
          σ[v ↦ b] (q.numVars + 1 + k) = g.eval σ[v ↦ b] ∧
            ∀ l ∈ g.inputs, l.1 ∈ Prefix.vars (P₁ ++ [(qt, v)]) := by
        intro b k g hg hk
        obtain ⟨hval, hin⟩ := hs k g hg hk
        have hne : q.numVars + 1 + k ≠ v := fun h => hvP₁ (h ▸ hk)
        refine ⟨?_, fun l hl => by simp [hin l hl]⟩
        rw [Assignment.set_other _ _ hne, hval]
        refine gate_eval_congr g fun l hl => ?_
        have : l.1 ≠ v := fun h => hvP₁ (h ▸ hin l hl)
        rw [Assignment.set_other _ _ this]
      by_cases hvn : v ≤ q.numVars
      · -- A variable of `q`: follow the play of the original formula.
        have hsettled : ∀ b : Bool, Settled q (P₁ ++ [(qt, v)]) σ[v ↦ b] := by
          intro b k g hg hk
          simp only [Prefix.vars_append, Prefix.vars_cons, Prefix.vars_nil, List.mem_append,
            List.mem_singleton] at hk
          rcases hk with hk | hk
          · exact keep b k g hg hk
          · vomega
        simp only [List.filter_cons, hvn, decide_true, if_true] at he
        cases qt with
        | ex =>
            obtain ⟨b, hb⟩ := he
            exact ⟨b, tseitin_evalPrefix_aux hwf hv S _ _ hP' (hsettled b) hb⟩
        | all =>
            intro b
            exact tseitin_evalPrefix_aux hwf hv S _ _ hP' (hsettled b) (he b)
      · -- A gate variable: assign the value of the gate.
        obtain ⟨hqt, g, hg, hin⟩ := hv.gate P₁ qt v S hP (by vomega)
        subst hqt
        simp only [List.filter_cons, hvn, decide_false] at he
        have hin' : ∀ l ∈ g.inputs, l.1 ≠ v := fun l hl h => hvP₁ (h ▸ hin l hl)
        have hsame : g.eval σ[v ↦ g.eval σ] = g.eval σ :=
          gate_eval_congr g fun l hl => Assignment.set_other _ _ (hin' l hl)
        have hsettled : Settled q (P₁ ++ [(Quant.ex, v)]) σ[v ↦ g.eval σ] := by
          intro k g' hg' hk
          simp only [Prefix.vars_append, Prefix.vars_cons, Prefix.vars_nil, List.mem_append,
            List.mem_singleton] at hk
          rcases hk with hk | hk
          · exact keep _ k g' hg' hk
          · have hkv : k = v - (q.numVars + 1) := by vomega
            subst hkv
            obtain rfl : g = g' := by rw [hg] at hg'; exact Option.some.inj hg'
            refine ⟨?_, fun l hl => by simp [hin l hl]⟩
            rw [hk, Assignment.set_same, hsame]
        refine ⟨g.eval σ, tseitin_evalPrefix_aux hwf hv S _ _ hP' hsettled ?_⟩
        refine evalPrefixF_congr (n := q.numVars) (fun σ₁ σ₂ h => matrix_congr hwf h) _ σ (σ[v ↦ g.eval σ]) ?_ he
        intro w hw
        have : w ≠ v := by vomega
        rw [Assignment.set_other _ _ this]

/-- If `q` is true, then so is its Tseitin encoding under any extended prefix. -/
theorem tseitin_evalPrefix {q : Qcir} (hwf : q.wf = true) {P : Prefix} (hv : ExtValid q P)
    (h : q.True) : evalPrefix P (fun _ => false) q.tseitin := by
  refine tseitin_evalPrefix_aux hwf hv P ([] : Prefix) _ (by simp) ?_ ?_
  · intro k g _ hk; simp at hk
  · rw [hv.restrict]; exact h

end Qcir

end Qlrup
