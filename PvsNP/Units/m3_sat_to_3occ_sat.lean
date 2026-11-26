import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin

namespace PvsNP.Units.M3OccAux

/-! ## The occurrence-splitting transform (CNF level)

The `j`-th literal occurrence of the whole CNF (in flatten order), `(b, v)`,
is renamed to `(b, B + j)`: every copy is a fresh variable.  For each original
variable `v`, the copies of its occurrences `j₁ < … < jₖ` are tied together by
a cycle of implication clauses `(¬y_{jᵢ} ∨ y_{jᵢ₊₁})` (indices modulo `k`),
which forces all copies to take the same truth value.  Each copy then occurs
exactly three times when `k ≥ 2` (once in its renamed clause, once negated,
once positive in the cycle) and once when `k = 1` (the self-loop clause
`[(¬y ∨ y)]` is a tautology and keeps the count at three as well: once in the
renamed clause and twice in the self-loop).  The base `B` is arbitrary:
copies are pairwise distinct for any `B`, and no original variable survives. -/

/-- Rename one clause, counting literal positions from `j`. -/
def renameClause (B j : Nat) (C : clause) : clause :=
  (C.zipIdx j).map (fun p => (p.1.1, B + p.2))

/-- Rename a whole CNF, counting literal positions from `j` across clauses. -/
def renameFrom (B : Nat) : Nat → cnf → cnf
  | _, [] => []
  | j, C :: N => renameClause B j C :: renameFrom B (j + C.length) N

/-- Rename a whole CNF, counting from `0`. -/
def renameCnf (B : Nat) (N : cnf) : cnf := renameFrom B 0 N

/-- The positions (global literal indices) at which variable `v` occurs in `N`. -/
def posOf (v : var) (N : cnf) : List Nat :=
  ((N.flatten.zipIdx).filter (fun p => p.1.2 = v)).map Prod.snd

/-- The implication chain over positions `js`, closed back to `first`:
clauses `(¬y_{j₁} ∨ y_{j₂}), …, (¬y_{jₖ} ∨ first)`. -/
def chainClauses (B : Nat) (first : Nat) : List Nat → cnf
  | [] => []
  | [j] => [[(false, B + j), (true, B + first)]]
  | j₁ :: j₂ :: rest => [(false, B + j₁), (true, B + j₂)] :: chainClauses B first (j₂ :: rest)

/-- The implication cycle tying the copies at positions `js` together. -/
def cycleClauses (B : Nat) (js : List Nat) : cnf :=
  match js with
  | [] => []
  | j :: rest => chainClauses B j (j :: rest)

/-- The variables occurring in `N`, in flatten order (with repetitions). -/
def varsList (N : cnf) : List Nat := N.flatten.map (fun l => l.2)

/-- Deduplicate a list of variables, keeping one copy of each. -/
def dedupVars : List Nat → List Nat
  | [] => []
  | v :: vs => if v ∈ dedupVars vs then dedupVars vs else v :: dedupVars vs

theorem mem_dedupVars {x : Nat} {l : List Nat} : x ∈ dedupVars l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupVars]
  | cons v vs ih =>
      by_cases hv : v ∈ dedupVars vs
      · simp only [dedupVars, hv, if_true]
        constructor
        · intro h
          exact List.mem_cons_of_mem v (ih.mp h)
        · intro h
          rcases List.mem_cons.mp h with rfl | h
          · exact hv
          · exact ih.mpr h
      · simp only [dedupVars, hv, if_false, List.mem_cons]
        exact or_congr Iff.rfl ih

theorem nodup_dedupVars (l : List Nat) : (dedupVars l).Nodup := by
  induction l with
  | nil => simp [dedupVars]
  | cons v vs ih =>
      by_cases hv : v ∈ dedupVars vs
      · simp only [dedupVars, hv, if_true]
        exact ih
      · simp only [dedupVars, hv, if_false]
        exact List.Nodup.cons hv ih

/-- The full transform: renamed CNF plus one implication cycle per variable. -/
def occT (B : Nat) (N : cnf) : cnf :=
  renameCnf B N ++ (List.range ((varsList N).sum + 1)).flatMap
    (fun v => cycleClauses B (posOf v N))

/-- The renamed CNF flattens to the renamed literal list. -/
theorem flatten_renameFrom (B : Nat) (j : Nat) (N : cnf) :
    (renameFrom B j N).flatten =
      (N.flatten.zipIdx j).map (fun p => (p.1.1, B + p.2)) := by
  induction N generalizing j with
  | nil => rfl
  | cons C N ih =>
      simp only [renameFrom, List.flatten_cons, ih, renameClause, List.zipIdx_append,
        List.map_append]

/-- Membership in `posOf`: `j` is the index of an occurrence of `v`. -/
theorem mem_posOf {v : var} {N : cnf} {j : Nat} :
    j ∈ posOf v N ↔ ∃ l : literal, (l, j) ∈ N.flatten.zipIdx ∧ l.2 = v := by
  simp only [posOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l, j'⟩, ⟨hj', hl⟩, rfl⟩
    exact ⟨l, hj', hl⟩
  · rintro ⟨l, hj, hl⟩
    exact ⟨⟨l, j⟩, ⟨hj, hl⟩, rfl⟩

/-- The positions of any variable are pairwise distinct. -/
theorem nodup_posOf (v : var) (N : cnf) : (posOf v N).Nodup := by
  have hsub : List.Sublist (posOf v N) ((N.flatten.zipIdx).map Prod.snd) :=
    List.Sublist.map Prod.snd List.filter_sublist
  rw [List.zipIdx_map_snd] at hsub
  exact hsub.nodup List.nodup_range'

/-- Two pairs in a `zipIdx` with the same index have the same first component. -/
theorem zipIdx_unique {α : Type*} {L : List α} {j g : Nat} {a b : α}
    (h1 : (a, g) ∈ L.zipIdx j) (h2 : (b, g) ∈ L.zipIdx j) : a = b := by
  have e1 := List.mem_zipIdx h1
  have e2 := List.mem_zipIdx h2
  exact e1.2.2.trans e2.2.2.symm

/-- A clause of a chain mentions two positions of the list (the second may be
the closing target `first`). -/
theorem mem_chainClauses {B f : Nat} {js : List Nat} {C : clause}
    (hC : C ∈ chainClauses B f js) :
    ∃ p q, C = [(false, B + p), (true, B + q)] ∧ p ∈ js ∧ (q ∈ js ∨ q = f) := by
  induction js with
  | nil => cases hC
  | cons j js ih =>
      cases js with
      | nil =>
          simp only [chainClauses, List.mem_singleton] at hC
          exact ⟨j, f, hC, by simp, Or.inr rfl⟩
      | cons j₂ rest =>
          simp only [chainClauses, List.mem_cons] at hC
          rcases hC with rfl | hC
          · exact ⟨j, j₂, rfl, by simp, Or.inl (by simp)⟩
          · obtain ⟨p, q, rfl, hp, hq⟩ := ih hC
            exact ⟨p, q, rfl, by simp [hp], hq.imp_left (by simp [·])⟩

/-- A satisfied implication clause `(¬y_p ∨ y_q)` gives `val p ≤ val q`. -/
theorem imp_le {a' : assgn} {B p q : Nat}
    (h : evalClause a' [(false, B + p), (true, B + q)] = true) :
    evalVar a' (B + p) ≤ evalVar a' (B + q) := by
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false] at h
  have h1 : evalLiteral a' (false, B + p) = decide (evalVar a' (B + p) = false) := rfl
  have h2 : evalLiteral a' (true, B + q) = decide (evalVar a' (B + q) = true) := rfl
  rw [h1, h2] at h
  cases hp : evalVar a' (B + p) <;> cases hq : evalVar a' (B + q) <;> simp_all

/-- Along a satisfied chain, every position's value is at most the closing target's. -/
theorem chain_le_first {a' : assgn} {B f : Nat} :
    ∀ {js : List Nat} {i : Nat}, i ∈ js →
      (∀ C ∈ chainClauses B f js, evalClause a' C = true) →
      evalVar a' (B + i) ≤ evalVar a' (B + f) := by
  intro js
  induction js with
  | nil => intro i hi; cases hi
  | cons j js ih =>
      intro i hi hsat
      cases js with
      | nil =>
          simp only [List.mem_singleton] at hi
          subst hi
          exact imp_le (hsat _ (by simp [chainClauses]))
      | cons j₂ rest =>
          have hstep : evalVar a' (B + j) ≤ evalVar a' (B + j₂) :=
            imp_le (hsat _ (by simp [chainClauses]))
          have htail : ∀ C ∈ chainClauses B f (j₂ :: rest), evalClause a' C = true :=
            fun C hC => hsat C (by simp [chainClauses, hC])
          rcases List.mem_cons.mp hi with rfl | hi'
          · exact le_trans hstep (ih (by simp) htail)
          · exact ih hi' htail

/-- Along a satisfied chain, the head's value is at most every position's. -/
theorem chain_ge_head {a' : assgn} {B f : Nat} :
    ∀ {js : List Nat} {i : Nat}, i ∈ js →
      (∀ C ∈ chainClauses B f js, evalClause a' C = true) →
      evalVar a' (B + js.head!) ≤ evalVar a' (B + i) := by
  intro js
  induction js with
  | nil => intro i hi; cases hi
  | cons j js ih =>
      intro i hi hsat
      cases js with
      | nil =>
          simp only [List.mem_singleton] at hi
          subst hi
          simp
      | cons j₂ rest =>
          have hstep : evalVar a' (B + j) ≤ evalVar a' (B + j₂) :=
            imp_le (hsat _ (by simp [chainClauses]))
          have htail : ∀ C ∈ chainClauses B f (j₂ :: rest), evalClause a' C = true :=
            fun C hC => hsat C (by simp [chainClauses, hC])
          rcases List.mem_cons.mp hi with rfl | hi'
          · simp
          · have := ih hi' htail
            simp only [List.head!_cons] at this
            exact le_trans hstep this

/-- **All copies of one variable agree.** If every clause of the cycle over
`js` is satisfied, all positions in `js` have the same value. -/
theorem cycle_eq {a' : assgn} {B : Nat} {js : List Nat} {x y : Nat}
    (hx : x ∈ js) (hy : y ∈ js)
    (hsat : ∀ C ∈ cycleClauses B js, evalClause a' C = true) :
    evalVar a' (B + x) = evalVar a' (B + y) := by
  cases js with
  | nil => cases hx
  | cons j rest =>
      have hsat' : ∀ C ∈ chainClauses B j (j :: rest), evalClause a' C = true := hsat
      have h1 : evalVar a' (B + x) ≤ evalVar a' (B + j) := chain_le_first hx hsat'
      have h2 : evalVar a' (B + j) ≤ evalVar a' (B + x) := by
        have := chain_ge_head (B := B) (f := j) hx hsat'
        simpa using this
      have h3 : evalVar a' (B + y) ≤ evalVar a' (B + j) := chain_le_first hy hsat'
      have h4 : evalVar a' (B + j) ≤ evalVar a' (B + y) := by
        have := chain_ge_head (B := B) (f := j) hy hsat'
        simpa using this
      exact le_antisymm (le_trans h1 h4) (le_trans h3 h2)

/-- The assignment on copies induced by `a`: copy `B + j` is true exactly when
the variable at occurrence `j` is true under `a`. -/
def copiesOf (a : assgn) (B : Nat) (N : cnf) : assgn :=
  ((N.flatten.zipIdx).filter (fun p => evalVar a p.1.2)).map (fun p => B + p.2)

/-- Copies evaluate exactly like their original variables. -/
theorem evalVar_copies {a : assgn} {B : Nat} {N : cnf} {l : literal} {g : Nat}
    (h : (l, g) ∈ N.flatten.zipIdx) :
    evalVar (copiesOf a B N) (B + g) = evalVar a l.2 := by
  have h1 : N.flatten[g]? = some l := List.mem_zipIdx_iff_getElem?.mp h
  unfold evalVar copiesOf
  rw [decide_eq_decide]
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpg⟩ := hmem
    rw [List.mem_filter] at hp
    have hpg' : B + p.2 = B + g := hpg
    have hp2 : p.2 = g := by omega
    have h2 : N.flatten[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.mp hp.1
    rw [hp2, h1] at h2
    have hpl : p.1 = l := (Option.some.inj h2).symm
    rw [← hpl]
    exact of_decide_eq_true hp.2
  · intro hl
    rw [List.mem_map]
    refine ⟨(l, g), ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨h, decide_eq_true hl⟩

/-- Renamed satisfaction transfers between two assignments that agree on all
copy/original variable pairs at the occurring positions. -/
theorem renameFrom_sat_iff {a a' : assgn} {B j : Nat} :
    ∀ {N : cnf},
      (∀ l g, (l, g) ∈ N.flatten.zipIdx j → evalVar a' (B + g) = evalVar a l.2) →
      (satisfiesCnf a' (renameFrom B j N) ↔ satisfiesCnf a N) := by
  intro N
  induction N generalizing j with
  | nil => intro _; rfl
  | cons C N ih =>
      intro hval
      have hvalC : ∀ l g, (l, g) ∈ C.zipIdx j → evalVar a' (B + g) = evalVar a l.2 := by
        intro l g hg
        apply hval
        rw [List.flatten_cons, List.zipIdx_append]
        exact List.mem_append_left _ hg
      have hvalN : ∀ l g, (l, g) ∈ N.flatten.zipIdx (j + C.length) →
          evalVar a' (B + g) = evalVar a l.2 := by
        intro l g hg
        apply hval
        rw [List.flatten_cons, List.zipIdx_append]
        exact List.mem_append_right _ hg
      have hclause : evalClause a' (renameClause B j C) = true ↔ evalClause a C = true := by
        constructor
        · intro h
          rw [evalClause, List.any_eq_true] at h ⊢
          obtain ⟨l', hl', hev⟩ := h
          rw [renameClause, List.mem_map] at hl'
          obtain ⟨⟨l, g⟩, hg, rfl⟩ := hl'
          have hlC : l ∈ C := by
            have e := List.mem_zipIdx hg
            rw [e.2.2]
            exact List.getElem_mem _
          refine ⟨l, hlC, ?_⟩
          have hv := hvalC l g hg
          cases l with
          | mk s v =>
              simp only [evalLiteral] at hev ⊢
              rw [hv] at hev
              exact hev
        · intro h
          rw [evalClause, List.any_eq_true] at h ⊢
          obtain ⟨l, hl, hev⟩ := h
          obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp hl
          have hg : (l, j + i) ∈ C.zipIdx j := by
            rw [List.mem_iff_getElem]
            refine ⟨i, by rw [List.length_zipIdx]; exact hi, ?_⟩
            rw [List.getElem_zipIdx]
            exact Prod.ext hli rfl
          refine ⟨(l.1, B + (j + i)), ?_, ?_⟩
          · rw [renameClause, List.mem_map]
            exact ⟨(l, j + i), hg, rfl⟩
          · have hv := hvalC l (j + i) hg
            cases l with
            | mk s v =>
                simp only [evalLiteral] at hev ⊢
                rw [hv]
                exact hev
      simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true, renameFrom] at *
      exact and_congr hclause (ih hvalN)

/-- Every variable of a literal in the flatten list is in `varsList`. -/
theorem mem_varsList {N : cnf} {l : literal} (h : l ∈ N.flatten) : l.2 ∈ varsList N := by
  simp only [varsList, List.mem_map]
  exact ⟨l, h, rfl⟩

/-- The cycle clauses are satisfied by the copies assignment: both endpoints of
every implication are copies of the same variable, hence agree. -/
theorem cycle_sat_copies {a : assgn} {B : Nat} {N : cnf} {v : var} {C : clause}
    (hC : C ∈ cycleClauses B (posOf v N)) : evalClause (copiesOf a B N) C = true := by
  cases hpos : posOf v N with
  | nil =>
      rw [hpos] at hC
      simp [cycleClauses] at hC
  | cons j rest =>
      rw [hpos] at hC
      rw [show cycleClauses B (j :: rest) = chainClauses B j (j :: rest) from rfl] at hC
      obtain ⟨p, q, rfl, hp, hq⟩ := mem_chainClauses hC
      have hp' : p ∈ posOf v N := by rw [hpos]; exact hp
      have hq' : q ∈ posOf v N := by
        rcases hq with hq | rfl
        · rw [hpos]; exact hq
        · rw [hpos]; exact List.mem_cons_self
      obtain ⟨lp, hlp, hlp2⟩ := mem_posOf.mp hp'
      obtain ⟨lq, hlq, hlq2⟩ := mem_posOf.mp hq'
      have ep : evalVar (copiesOf a B N) (B + p) = evalVar a v := by
        rw [evalVar_copies hlp, hlp2]
      have eq : evalVar (copiesOf a B N) (B + q) = evalVar a v := by
        rw [evalVar_copies hlq, hlq2]
      have e1 : evalLiteral (copiesOf a B N) (false, B + p) =
          decide (evalVar a v = false) := by
        show decide (evalVar (copiesOf a B N) (B + p) = false) = _
        rw [ep]
      have e2 : evalLiteral (copiesOf a B N) (true, B + q) =
          decide (evalVar a v = true) := by
        show decide (evalVar (copiesOf a B N) (B + q) = true) = _
        rw [eq]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, e1, e2]
      cases evalVar a v <;> rfl

/-- The value of the backward assignment (first-copy values) at an occurring
variable agrees with every copy's value, when all cycle clauses hold. -/
theorem backward_assignment {a' : assgn} {B : Nat} {N : cnf}
    (hlinks : ∀ v ∈ List.range ((varsList N).sum + 1),
      ∀ C ∈ cycleClauses B (posOf v N), evalClause a' C = true) :
    ∀ l g, (l, g) ∈ N.flatten.zipIdx →
      evalVar a' (B + g) =
        evalVar ((dedupVars (varsList N)).filter
          (fun v => evalVar a' (B + (posOf v N).head?.getD 0))) l.2 := by
  intro l g hg
  have hgpos : g ∈ posOf l.2 N := mem_posOf.mpr ⟨l, hg, rfl⟩
  have hlmem : l.2 ∈ dedupVars (varsList N) :=
    mem_dedupVars.mpr (mem_varsList (by
      have e := List.mem_zipIdx hg
      rw [e.2.2]; exact List.getElem_mem _))
  have hsat : ∀ C ∈ cycleClauses B (posOf l.2 N), evalClause a' C = true :=
    hlinks l.2 (List.mem_range.mpr (Nat.lt_succ.mpr
      (List.single_le_sum (fun x _ => Nat.zero_le x) l.2 (mem_dedupVars.mp hlmem))))
  obtain ⟨j₀, rest, hpos⟩ : ∃ j₀ rest, posOf l.2 N = j₀ :: rest := by
    cases h : posOf l.2 N with
    | nil => rw [h] at hgpos; cases hgpos
    | cons j₀ rest => exact ⟨j₀, rest, rfl⟩
  have hhead : (posOf l.2 N).head?.getD 0 = j₀ := by simp [hpos]
  have hjeq : evalVar a' (B + g) = evalVar a' (B + j₀) :=
    cycle_eq hgpos (by rw [hpos]; exact List.mem_cons_self) hsat
  have hmem : l.2 ∈ (dedupVars (varsList N)).filter
        (fun v => evalVar a' (B + (posOf v N).head?.getD 0)) ↔
      evalVar a' (B + j₀) = true := by
    rw [List.mem_filter]
    constructor
    · intro h
      have h2 := h.2
      simp only [hhead] at h2
      exact h2
    · intro h
      exact ⟨hlmem, by simp only [hhead]; exact h⟩
  have hfin : evalVar ((dedupVars (varsList N)).filter
        (fun v => evalVar a' (B + (posOf v N).head?.getD 0))) l.2 =
      evalVar a' (B + j₀) := by
    unfold evalVar
    rw [decide_eq_decide]
    constructor
    · intro h
      exact of_decide_eq_true (hmem.mp h)
    · intro h
      exact hmem.mpr (decide_eq_true h)
  rw [hjeq, hfin]

/-- **The transform preserves satisfiability**, for every base `B`. -/
theorem occT_sat {B : Nat} {N : cnf} : SAT (occT B N) ↔ SAT N := by
  constructor
  · rintro ⟨a', ha'⟩
    have ha'split : satisfiesCnf a' (renameCnf B N) ∧
        evalCnf a' ((List.range ((varsList N).sum + 1)).flatMap
          (fun v => cycleClauses B (posOf v N))) = true := by
      have h := ha'
      rw [occT, satisfiesCnf, evalCnf_app_iff] at h
      exact h
    obtain ⟨hren, hlinks⟩ := ha'split
    have hlinks' : ∀ v ∈ List.range ((varsList N).sum + 1),
        ∀ C ∈ cycleClauses B (posOf v N), evalClause a' C = true := by
      intro v hv C hC
      exact (evalCnf_clause_iff a' _).mp hlinks C (List.mem_flatMap.mpr ⟨v, hv, hC⟩)
    refine ⟨(dedupVars (varsList N)).filter
      (fun v => evalVar a' (B + (posOf v N).head?.getD 0)), ?_⟩
    have hval : ∀ l g, (l, g) ∈ N.flatten.zipIdx →
        evalVar a' (B + g) = evalVar ((dedupVars (varsList N)).filter
          (fun v => evalVar a' (B + (posOf v N).head?.getD 0))) l.2 :=
      backward_assignment hlinks'
    exact (renameFrom_sat_iff hval).mp hren
  · rintro ⟨a, ha⟩
    refine ⟨copiesOf a B N, ?_⟩
    have hsplit : satisfiesCnf (copiesOf a B N) (renameCnf B N) ∧
        evalCnf (copiesOf a B N) ((List.range ((varsList N).sum + 1)).flatMap
          (fun v => cycleClauses B (posOf v N))) = true := by
      constructor
      · have hval : ∀ l g, (l, g) ∈ N.flatten.zipIdx →
            evalVar (copiesOf a B N) (B + g) = evalVar a l.2 :=
          fun l g hg => evalVar_copies hg
        exact (renameFrom_sat_iff hval).mpr ha
      · rw [evalCnf_clause_iff]
        intro C hC
        rw [List.mem_flatMap] at hC
        obtain ⟨v, hv, hCv⟩ := hC
        exact cycle_sat_copies hCv
    rw [occT, satisfiesCnf, evalCnf_app_iff]
    exact hsplit

/-- In a range, the values `B + i` hit any target at most once. -/
theorem countP_range'_le (B v : Nat) :
    ∀ (s m : Nat), (List.range' s m).countP (fun i => (B + i) == v) ≤ 1 := by
  intro s m
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      rw [List.range'_succ, List.countP_cons]
      by_cases h : (B + s) == v
      · simp only [beq_iff_eq] at h
        have h0 : (List.range' (s + 1) m).countP (fun i => (B + i) == v) = 0 := by
          rw [List.countP_eq_zero]
          intro i hi
          rw [List.mem_range'] at hi
          have hne : B + i ≠ v := by omega
          simp [hne]
        simp [h0, h]
      · have h0 : ((B + s) == v) = false := by
          cases h' : (B + s) == v with
          | true => exact absurd h' h
          | false => rfl
        rw [h0]
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        exact ih (s + 1)

/-- The renamed CNF mentions any variable at most once: its literals are the
distinct copies `B + j`. -/
theorem countP_renameCnf_le (B v : Nat) (N : cnf) :
    (renameCnf B N).flatten.countP (fun l => l.2 == v) ≤ 1 := by
  have h1 : (renameCnf B N).flatten =
      (N.flatten.zipIdx).map (fun p => (p.1.1, B + p.2)) := flatten_renameFrom B 0 N
  rw [h1, List.countP_map]
  have h2 : (fun l : literal => l.2 == v) ∘ (fun p : literal × Nat => (p.1.1, B + p.2)) =
      (fun p : literal × Nat => (B + p.2) == v) := rfl
  rw [h2]
  have h4 : (N.flatten.zipIdx).countP ((fun i => (B + i) == v) ∘ Prod.snd) =
      ((N.flatten.zipIdx).map Prod.snd).countP (fun i => (B + i) == v) :=
    (List.countP_map).symm
  have h5 : (fun i => (B + i) == v) ∘ Prod.snd =
      (fun p : literal × Nat => (B + p.2) == v) := rfl
  rw [h5, List.zipIdx_map_snd] at h4
  rw [h4]
  exact countP_range'_le B v 0 _

/-- Counting literals in a chain: the sources are `js` (once each), the
targets are `js.tail ++ [f]` (once each). -/
theorem countP_chainClauses (B v : Nat) :
    ∀ (js : List Nat) (f : Nat), js ≠ [] →
      (chainClauses B f js).flatten.countP (fun l => l.2 == v) =
        js.countP (fun i => (B + i) == v) +
          (js.tail ++ [f]).countP (fun i => (B + i) == v) := by
  intro js
  induction js with
  | nil => intro f h; exact absurd rfl h
  | cons j js ih =>
      intro f _
      cases js with
      | nil =>
          simp only [chainClauses, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.countP_cons, List.countP_nil, List.tail_cons, List.nil_append]
          split_ifs <;> omega
      | cons j₂ rest =>
          have ih' := ih f (by simp)
          simp only [chainClauses, List.flatten_cons, List.countP_append, List.countP_cons,
            List.countP_nil, List.tail_cons] at ih' ⊢
          omega

/-- Counting literals in a cycle: every position appears exactly twice. -/
theorem countP_cycleClauses (B v : Nat) (js : List Nat) :
    (cycleClauses B js).flatten.countP (fun l => l.2 == v) =
      2 * js.countP (fun i => (B + i) == v) := by
  cases js with
  | nil => simp [cycleClauses]
  | cons j rest =>
      rw [show cycleClauses B (j :: rest) = chainClauses B j (j :: rest) from rfl,
        countP_chainClauses B v (j :: rest) j (by simp)]
      simp only [List.tail_cons, List.countP_append, List.countP_cons, List.countP_nil]
      omega

/-- Positions of a variable form a sublist of the index range. -/
theorem posOf_sublist_range (v : var) (N : cnf) :
    (posOf v N).Sublist (List.range' 0 N.flatten.length) := by
  have hsub : (posOf v N).Sublist ((N.flatten.zipIdx).map Prod.snd) :=
    List.Sublist.map Prod.snd List.filter_sublist
  rwa [List.zipIdx_map_snd] at hsub

/-- A variable's positions hit any copy index at most once. -/
theorem countP_posOf_le (B v : Nat) (w : var) (N : cnf) :
    (posOf w N).countP (fun i => (B + i) == v) ≤ 1 :=
  le_trans (List.Sublist.countP_le (posOf_sublist_range w N)) (countP_range'_le B v 0 _)

/-- A sum over a nodup list is bounded by `M` when every term is at most `M`
and at most one term is nonzero. -/
theorem sum_le_of_unique {g : Nat → Nat} {M : Nat} :
    ∀ {ws : List Nat}, ws.Nodup → (∀ w, g w ≤ M) →
      (∀ w₁ ∈ ws, ∀ w₂ ∈ ws, g w₁ ≠ 0 → g w₂ ≠ 0 → w₁ = w₂) →
      (ws.map g).sum ≤ M := by
  intro ws
  induction ws with
  | nil => intro _ _ _; simp
  | cons w ws ih =>
      intro hnod hM huniq
      rw [List.map_cons, List.sum_cons]
      have hnod' : ws.Nodup := (List.nodup_cons.mp hnod).2
      have hw : w ∉ ws := (List.nodup_cons.mp hnod).1
      by_cases hgw : g w = 0
      · rw [hgw, Nat.zero_add]
        exact ih hnod' hM (fun w₁ h₁ w₂ h₂ => huniq w₁ (List.mem_cons_of_mem _ h₁)
          w₂ (List.mem_cons_of_mem _ h₂))
      · have hsum0 : (ws.map g).sum = 0 := by
          rw [List.sum_eq_zero_iff]
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨w', hw', rfl⟩ := hx
          by_contra hne
          have : w' = w := huniq w' (List.mem_cons_of_mem _ hw') w List.mem_cons_self hne hgw
          exact hw (this ▸ hw')
        rw [hsum0, Nat.add_zero]
        exact hM w

/-- Flattening a flatMap of CNFs. -/
theorem flatten_flatMap (ws : List Nat) (f : Nat → cnf) :
    (ws.flatMap f).flatten = ws.flatMap (fun w => (f w).flatten) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatten_append, ih]

/-- The cycle part of the transform mentions any variable at most twice:
all its copies of one original variable contribute, and only those. -/
theorem countP_links_le (B v : Nat) (N : cnf) :
    ((List.range ((varsList N).sum + 1)).flatMap
      (fun w => cycleClauses B (posOf w N))).flatten.countP (fun l => l.2 == v) ≤ 2 := by
  rw [flatten_flatMap, List.countP_flatMap]
  have hcomp : (List.countP (fun l => l.2 == v)) ∘ (fun w => (cycleClauses B (posOf w N)).flatten)
      = (fun w => (cycleClauses B (posOf w N)).flatten.countP (fun l => l.2 == v)) := rfl
  rw [hcomp]
  apply sum_le_of_unique (M := 2) List.nodup_range
  · intro w
    rw [countP_cycleClauses]
    have := countP_posOf_le B v w N
    omega
  · intro w₁ hw₁ w₂ hw₂ h₁ h₂
    rw [countP_cycleClauses] at h₁ h₂
    have hp₁ : ∃ i ∈ posOf w₁ N, ((B + i) == v) = true := by
      by_contra hcon
      push_neg at hcon
      have hz : (posOf w₁ N).countP (fun i => (B + i) == v) = 0 :=
        List.countP_eq_zero.mpr hcon
      omega
    have hp₂ : ∃ i ∈ posOf w₂ N, ((B + i) == v) = true := by
      by_contra hcon
      push_neg at hcon
      have hz : (posOf w₂ N).countP (fun i => (B + i) == v) = 0 :=
        List.countP_eq_zero.mpr hcon
      omega
    obtain ⟨i, hi₁, hi₁eq⟩ := hp₁
    obtain ⟨i', hi₂, hi₂eq⟩ := hp₂
    obtain ⟨l₁, hl₁, hl₁2⟩ := mem_posOf.mp hi₁
    obtain ⟨l₂, hl₂, hl₂2⟩ := mem_posOf.mp hi₂
    have hii : i = i' := by
      rw [beq_iff_eq] at hi₁eq hi₂eq
      omega
    subst hii
    have : l₁ = l₂ := zipIdx_unique hl₁ hl₂
    rw [← hl₁2, ← hl₂2, this]

/-- **Occurrence bound**: in the transformed CNF, every variable occurs at
most three times. -/
theorem occT_occ_le (B : Nat) (N : cnf) :
    ∀ v, (occT B N).flatten.countP (fun l => l.2 == v) ≤ 3 := by
  intro v
  rw [occT, List.flatten_append, List.countP_append]
  have h1 := countP_renameCnf_le B v N
  have h2 := countP_links_le B v N
  omega

/-- The string-level reduction map: split occurrences in the parsed CNF
(base `0`, so copy names are exactly the occurrence indices); junk inputs go
to the junk string `[false]`. -/
def occMap (x : List Bool) : List Bool :=
  if CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) then
    CookLevin.Lang.boolsOf (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x)))
  else [false]

theorem cnfOf_occMap_wf {x : List Bool}
    (hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true) :
    SATStr.cnfOf (occMap x) = occT 0 (SATStr.cnfOf x) := by
  unfold occMap SATStr.cnfOf
  rw [if_pos hwf, CookLevin.Lang.strBits_boolsOf (EvalCnfCmd.encodeCnf_bit _),
    CnfWellFormed.parseTotal_encodeCnf]

theorem cnfOf_occMap_not_wf {x : List Bool}
    (hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false) :
    SATStr.cnfOf (occMap x) = [[]] := by
  unfold occMap SATStr.cnfOf
  rw [if_neg (by simp [hwf])]
  decide

/-- **The reduction is correct at the string level.** -/
theorem occMap_iff (x : List Bool) :
    SATStr x ↔ (∀ v, (SATStr.cnfOf (occMap x)).flatten.countP
        (fun l => l.2 == v) ≤ 3) ∧ SAT (SATStr.cnfOf (occMap x)) := by
  by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
  · rw [cnfOf_occMap_wf hwf]
    constructor
    · intro h
      have h' : SAT (SATStr.cnfOf x) := h
      exact ⟨fun v => occT_occ_le 0 _ v, occT_sat.mpr h'⟩
    · intro h
      have h' : SAT (SATStr.cnfOf x) := occT_sat.mp h.2
      exact h'
  · have hwf' : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
      cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) with
      | true => exact absurd h hwf
      | false => rfl
    have hcnf : SATStr.cnfOf x = [[]] := by
      show CnfWellFormed.parseTotal (CookLevin.Lang.strBits x) = [[]]
      rw [CnfWellFormed.parseTotal_of_not_wf _ hwf']
      rfl
    rw [cnfOf_occMap_not_wf hwf']
    constructor
    · intro h
      have h' : SAT (SATStr.cnfOf x) := h
      rw [hcnf] at h'
      exact absurd h' CnfWellFormed.not_sat_botCnf
    · intro h
      exact absurd h.2 CnfWellFormed.not_sat_botCnf

open CookLevin.Lang

/-! ## The register program computing `occMap`

Registers: `0` is input/output. The program first runs the well-formedness
scanner (the `scanRun` DFA) over the input; on well-formed input it then
renames every literal occurrence to its index (phase A) and appends the
implication cycles (phase B); on junk input it outputs `[0]`. -/

abbrev rIN : CookLevin.Lang.Var := 1
abbrev rCUR : CookLevin.Lang.Var := 2
abbrev rHD : CookLevin.Lang.Var := 3
abbrev rOUT : CookLevin.Lang.Var := 4
abbrev rJ : CookLevin.Lang.Var := 5
abbrev rVARACC : CookLevin.Lang.Var := 6
abbrev rWF : CookLevin.Lang.Var := 7
abbrev rSA : CookLevin.Lang.Var := 8
abbrev rSB : CookLevin.Lang.Var := 9
abbrev rIDX : CookLevin.Lang.Var := 10
abbrev rIDX2 : CookLevin.Lang.Var := 11
abbrev rIDX3 : CookLevin.Lang.Var := 12
abbrev rVCTR : CookLevin.Lang.Var := 13
abbrev rEQ : CookLevin.Lang.Var := 14
abbrev rPREV : CookLevin.Lang.Var := 15
abbrev rFIRST : CookLevin.Lang.Var := 16
abbrev rHAS : CookLevin.Lang.Var := 17
abbrev rJ2 : CookLevin.Lang.Var := 18
abbrev rTMP : CookLevin.Lang.Var := 19

def nop : Cmd := Cmd.op (.clear rTMP)
def setZero (r : CookLevin.Lang.Var) : Cmd := Cmd.op (.clear r) ;; Cmd.op (.appendZero r)
def setOne (r : CookLevin.Lang.Var) : Cmd := Cmd.op (.clear r) ;; Cmd.op (.appendOne r)

/-- One cell of the well-formedness scan (the `scanStep` DFA). -/
def wfBody : Cmd :=
  Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR) ;;
  Cmd.ifBit rSA
    (Cmd.ifBit rSB
      (Cmd.ifBit rHD nop (setZero rSA))
      (setOne rSB))
    (Cmd.ifBit rHD
      (setOne rSA ;; setZero rSB)
      (setZero rSB))

/-- The well-formedness check: sets `rWF` to `[1]` iff the input in `rCUR`
is a well-formed CNF encoding. -/
def wfProg : Cmd :=
  setZero rSA ;; setZero rSB ;;
  Cmd.forBnd rIDX rIN wfBody ;;
  setOne rWF ;;
  Cmd.ifBit rSA (setZero rWF) nop ;;
  Cmd.ifBit rSB (setZero rWF) nop

def emitBit : Cmd :=
  Cmd.ifBit rHD (Cmd.op (.appendOne rOUT)) (Cmd.op (.appendZero rOUT))

/-- One cell of the renaming pass. -/
def renameBody : Cmd :=
  Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR) ;;
  Cmd.ifBit rSA
    (Cmd.ifBit rSB
      (Cmd.ifBit rHD nop
        (Cmd.op (.concat rOUT rOUT rJ) ;; Cmd.op (.appendZero rOUT) ;;
         Cmd.op (.appendOne rJ) ;; setZero rSA ;; setZero rSB))
      (emitBit ;; setOne rSB))
    (Cmd.ifBit rHD
      (Cmd.op (.appendOne rOUT) ;; setOne rSA ;; setZero rSB)
      (Cmd.op (.appendZero rOUT)))

/-- Phase A: rename every literal occurrence to its global index. -/
def renameProg : Cmd :=
  Cmd.op (.clear rJ) ;; Cmd.op (.clear rOUT) ;; setZero rSA ;; setZero rSB ;;
  Cmd.forBnd rIDX2 rIN renameBody

/-- Emit the implication clause `(¬a ∨ b)` for unary registers `a`, `b`. -/
def emitLink (a b : CookLevin.Lang.Var) : Cmd :=
  Cmd.op (.appendOne rOUT) ;; Cmd.op (.appendZero rOUT) ;; Cmd.op (.concat rOUT rOUT a) ;;
  Cmd.op (.appendZero rOUT) ;;
  Cmd.op (.appendOne rOUT) ;; Cmd.op (.appendOne rOUT) ;; Cmd.op (.concat rOUT rOUT b) ;;
  Cmd.op (.appendZero rOUT) ;; Cmd.op (.appendZero rOUT)

/-- Process one literal occurrence (at the end of its variable block). -/
def processOcc : Cmd :=
  Cmd.op (.eqBit rEQ rVARACC rVCTR) ;;
  Cmd.ifBit rEQ
    (Cmd.ifBit rHAS
      (emitLink rPREV rJ2 ;; Cmd.op (.copy rPREV rJ2))
      (Cmd.op (.copy rFIRST rJ2) ;; setOne rHAS ;; Cmd.op (.copy rPREV rJ2)))
    nop ;;
  Cmd.op (.appendOne rJ2)

/-- One cell of the per-variable scan in phase B. -/
def linksBody : Cmd :=
  Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR) ;;
  Cmd.ifBit rSA
    (Cmd.ifBit rSB
      (Cmd.ifBit rHD (Cmd.op (.appendOne rVARACC))
        (processOcc ;; setZero rSA ;; setZero rSB))
      (setOne rSB ;; Cmd.op (.clear rVARACC)))
    (Cmd.ifBit rHD (setOne rSA ;; setZero rSB) nop)

/-- One variable's pass in phase B: scan the input, link its occurrences. -/
def linksPass : Cmd :=
  Cmd.op (.copy rCUR rIN) ;;
  Cmd.op (.clear rJ2) ;; Cmd.op (.clear rPREV) ;; Cmd.op (.clear rFIRST) ;; setZero rHAS ;;
  setZero rSA ;; setZero rSB ;;
  Cmd.forBnd rIDX3 rIN linksBody ;;
  Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop

/-- Phase B: for every variable `v < |input|`, append its implication cycle. -/
def linksProg : Cmd :=
  Cmd.forBnd rVCTR rIN linksPass

/-- The whole reduction program. -/
def occCmd : Cmd :=
  Cmd.op (.copy rIN 0) ;;
  Cmd.op (.copy rCUR rIN) ;; wfProg ;;
  Cmd.ifBit rWF
    (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
    (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)) ;;
  Cmd.op (.copy 0 rOUT)



theorem wfBody_eval (st : State) (a b : Bool) (cell : Nat) (rest : List Nat)
    (hSA : st.get rSA = [if a then 1 else 0]) (hSB : st.get rSB = [if b then 1 else 0])
    (hCUR : st.get rCUR = cell :: rest) :
    (wfBody.eval st).get rCUR = rest ∧
    (wfBody.eval st).get rSA =
      [if (CnfWellFormed.scanStep (a, b, 0) cell).1 then 1 else 0] ∧
    (wfBody.eval st).get rSB =
      [if (CnfWellFormed.scanStep (a, b, 0) cell).2.1 then 1 else 0] := by
  have step1 : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rCUR = rest := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1HD : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rHD = [cell] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1SA : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSA =
      [if a then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSA, State.get_set_ne]
  have step1SB : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSB =
      [if b then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSB, State.get_set_ne]
  have hsplit : wfBody.eval st = (Cmd.ifBit rSA
      (Cmd.ifBit rSB (Cmd.ifBit rHD nop (setZero rSA)) (setOne rSB))
      (Cmd.ifBit rHD (setOne rSA ;; setZero rSB) (setZero rSB))).eval
        ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st) := by
    simp only [wfBody, Cmd.eval_seq]
  set s1 := ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st) with hs1
  rw [hsplit]
  cases a with
  | false =>
      rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SA])]
      by_cases hcell : cell = 1
      · subst hcell
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, CnfWellFormed.scanStep, step1, step1SA, step1SB]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell])]
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, CnfWellFormed.scanStep, step1, step1SA, step1SB,
            hcell]
  | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SA])]
      cases b with
      | false =>
          rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SB])]
          refine ⟨?_, ?_, ?_⟩ <;>
            simp [setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, CnfWellFormed.scanStep, step1, step1SA, step1SB]
      | true =>
          rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SB])]
          by_cases hcell : cell = 1
          · subst hcell
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
            refine ⟨?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, CnfWellFormed.scanStep, step1, step1SA,
                step1SB]
          · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell])]
            refine ⟨?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, CnfWellFormed.scanStep, step1, step1SA,
                step1SB, hcell]


theorem scanStep_k_indep (a b : Bool) (k : Nat) (c : Nat) :
    (CnfWellFormed.scanStep (a, b, k) c).1 = (CnfWellFormed.scanStep (a, b, 0) c).1 ∧
    (CnfWellFormed.scanStep (a, b, k) c).2.1 = (CnfWellFormed.scanStep (a, b, 0) c).2.1 := by
  cases a <;> cases b <;> by_cases h : c = 1 <;> simp [CnfWellFormed.scanStep, h]

theorem scanRun_take_succ_fst (l : List Nat) (i : Nat) (hi : i < l.length) :
    (CnfWellFormed.scanRun (l.take (i + 1))).1 =
      (CnfWellFormed.scanStep ((CnfWellFormed.scanRun (l.take i)).1,
        (CnfWellFormed.scanRun (l.take i)).2.1, 0) l[i]).1 := by
  have htake : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hi]
  have hrun : CnfWellFormed.scanRun (l.take i ++ [l[i]]) =
      CnfWellFormed.scanStep (CnfWellFormed.scanRun (l.take i)) l[i] := by
    show List.foldl CnfWellFormed.scanStep (false, false, 0) (l.take i ++ [l[i]]) =
      CnfWellFormed.scanStep (List.foldl CnfWellFormed.scanStep (false, false, 0)
        (l.take i)) l[i]
    rw [List.foldl_append]
    rfl
  rw [htake, hrun]
  exact (scanStep_k_indep _ _ _ _).1

theorem scanRun_take_succ_snd (l : List Nat) (i : Nat) (hi : i < l.length) :
    (CnfWellFormed.scanRun (l.take (i + 1))).2.1 =
      (CnfWellFormed.scanStep ((CnfWellFormed.scanRun (l.take i)).1,
        (CnfWellFormed.scanRun (l.take i)).2.1, 0) l[i]).2.1 := by
  have htake : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hi]
  have hrun : CnfWellFormed.scanRun (l.take i ++ [l[i]]) =
      CnfWellFormed.scanStep (CnfWellFormed.scanRun (l.take i)) l[i] := by
    show List.foldl CnfWellFormed.scanStep (false, false, 0) (l.take i ++ [l[i]]) =
      CnfWellFormed.scanStep (List.foldl CnfWellFormed.scanStep (false, false, 0)
        (l.take i)) l[i]
    rw [List.foldl_append]
    rfl
  rw [htake, hrun]
  exact (scanStep_k_indep _ _ _ _).2

theorem wfLoop (l : List Nat) (s : State)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0]) :
    ((Cmd.forBnd rIDX rIN wfBody).eval s).get rSA =
      [if (CnfWellFormed.scanRun l).1 then 1 else 0] ∧
    ((Cmd.forBnd rIDX rIN wfBody).eval s).get rSB =
      [if (CnfWellFormed.scanRun l).2.1 then 1 else 0] ∧
    ((Cmd.forBnd rIDX rIN wfBody).eval s).get rIN = l := by
  rw [Cmd.eval_forBnd, hIN]
  have key := Cmd.foldlState_range_induct wfBody rIDX l.length s
    (fun i st => st.get rCUR = l.drop i ∧
      st.get rSA = [if (CnfWellFormed.scanRun (l.take i)).1 then 1 else 0] ∧
      st.get rSB = [if (CnfWellFormed.scanRun (l.take i)).2.1 then 1 else 0] ∧
      st.get rIN = l)
    (by simp [hCUR, hSA, hSB, hIN, CnfWellFormed.scanRun])
    (by
      intro i st hi hM
      obtain ⟨hCURi, hSAi, hSBi, hINi⟩ := hM
      rw [List.drop_eq_getElem_cons hi] at hCURi
      have hCUR' : (st.set rIDX (List.replicate i 1)).get rCUR = l[i] :: l.drop (i + 1) := by
        simp [State.get_set_ne, hCURi]
      have hSA' : (st.set rIDX (List.replicate i 1)).get rSA =
          [if (CnfWellFormed.scanRun (l.take i)).1 then 1 else 0] := by
        simp [State.get_set_ne, hSAi]
      have hSB' : (st.set rIDX (List.replicate i 1)).get rSB =
          [if (CnfWellFormed.scanRun (l.take i)).2.1 then 1 else 0] := by
        simp [State.get_set_ne, hSBi]
      have hIN' : (st.set rIDX (List.replicate i 1)).get rIN = l := by
        simp [State.get_set_ne, hINi]
      obtain ⟨hCURn, hSAn, hSBn⟩ := wfBody_eval (st.set rIDX (List.replicate i 1))
        (CnfWellFormed.scanRun (l.take i)).1 (CnfWellFormed.scanRun (l.take i)).2.1
        l[i] (l.drop (i + 1)) hSA' hSB' hCUR'
      refine ⟨hCURn, ?_, ?_, ?_⟩
      · rw [hSAn, scanRun_take_succ_fst l i hi]
      · rw [hSBn, scanRun_take_succ_snd l i hi]
      · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes wfBody)]
        exact hIN')
  obtain ⟨-, hSAf, hSBf, hINf⟩ := key
  rw [List.take_of_length_le (le_refl _)] at hSAf hSBf
  exact ⟨hSAf, hSBf, hINf⟩


theorem setZero_get_eq (r : Var) (st : State) : ((setZero r).eval st).get r = [0] := by
  simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]

theorem setZero_get_ne (r q : Var) (st : State) (h : q ≠ r) :
    ((setZero r).eval st).get q = st.get q := by
  simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, h]

theorem nop_get (q : Var) (st : State) (h : q ≠ rTMP) : (nop.eval st).get q = st.get q := by
  simp [nop, Cmd.eval_op, Op.eval, State.get_set_ne, h]

theorem wfProg_eval (s : State) (l : List Nat)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l) :
    (wfProg.eval s).get rWF = [if CnfWellFormed.wfCnfB l then 1 else 0] ∧
    (wfProg.eval s).get rIN = l := by
  have g2SA : ((setZero rSB).eval ((setZero rSA).eval s)).get rSA = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have g2SB : ((setZero rSB).eval ((setZero rSA).eval s)).get rSB = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have g2CUR : ((setZero rSB).eval ((setZero rSA).eval s)).get rCUR = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hCUR]
  have g2IN : ((setZero rSB).eval ((setZero rSA).eval s)).get rIN = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  obtain ⟨g3SA, g3SB, g3IN⟩ := wfLoop l ((setZero rSB).eval ((setZero rSA).eval s))
    g2CUR g2IN g2SA g2SB
  have g4WF : ((setOne rWF).eval ((Cmd.forBnd rIDX rIN wfBody).eval
      ((setZero rSB).eval ((setZero rSA).eval s)))).get rWF = [1] := by
    simp [setOne, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have g4SA : ((setOne rWF).eval ((Cmd.forBnd rIDX rIN wfBody).eval
      ((setZero rSB).eval ((setZero rSA).eval s)))).get rSA =
      [if (CnfWellFormed.scanRun l).1 then 1 else 0] := by
    simp [setOne, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g3SA]
  have g4SB : ((setOne rWF).eval ((Cmd.forBnd rIDX rIN wfBody).eval
      ((setZero rSB).eval ((setZero rSA).eval s)))).get rSB =
      [if (CnfWellFormed.scanRun l).2.1 then 1 else 0] := by
    simp [setOne, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g3SB]
  have g4IN : ((setOne rWF).eval ((Cmd.forBnd rIDX rIN wfBody).eval
      ((setZero rSB).eval ((setZero rSA).eval s)))).get rIN = l := by
    simp [setOne, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g3IN]
  have hfull : wfProg.eval s = (Cmd.ifBit rSB (setZero rWF) nop).eval
      ((Cmd.ifBit rSA (setZero rWF) nop).eval
        ((setZero rSA ;; setZero rSB ;; Cmd.forBnd rIDX rIN wfBody ;; setOne rWF).eval s)) := by
    simp only [wfProg, Cmd.eval_seq]
  rw [hfull]
  cases h1 : (CnfWellFormed.scanRun l).1 <;> cases h2 : (CnfWellFormed.scanRun l).2.1
  · -- SA false, SB false: WF stays [1]
    rw [Cmd.eval_ifBit_false rSA (setZero rWF) nop _ (by simp [Cmd.eval_seq, g4SA, h1]),
      Cmd.eval_ifBit_false rSB (setZero rWF) nop _ (by
        simp [nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g4SB, h2])]
    constructor
    · simp [nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g4WF,
        CnfWellFormed.wfCnfB, h1, h2]
    · simp [nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g4IN]
  · -- SA false, SB true: WF := [0] at the second test
    rw [Cmd.eval_ifBit_false rSA (setZero rWF) nop _ (by simp [Cmd.eval_seq, g4SA, h1]),
      Cmd.eval_ifBit_true rSB (setZero rWF) nop _ (by
        simp [nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, g4SB, h2])]
    constructor
    · simp [setZero, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
        State.get_set_ne, CnfWellFormed.wfCnfB, h1, h2]
    · rw [setZero_get_ne rWF rIN _ (by decide), nop_get rIN _ (by decide)]
      simp only [Cmd.eval_seq]; exact g4IN
  · -- SA true, SB false: WF := [0] at the first test
    rw [Cmd.eval_ifBit_true rSA (setZero rWF) nop _ (by simp [Cmd.eval_seq, g4SA, h1]),
      Cmd.eval_ifBit_false rSB (setZero rWF) nop _ (by
        rw [setZero_get_ne rWF rSB _ (by decide)]; simp only [Cmd.eval_seq]; rw [g4SB];
        simp [h2])]
    constructor
    · simp [setZero, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
        State.get_set_ne, CnfWellFormed.wfCnfB, h1, h2]
    · rw [nop_get rIN _ (by decide), setZero_get_ne rWF rIN _ (by decide)]
      simp only [Cmd.eval_seq]; exact g4IN
  · -- SA true, SB true: WF := [0]
    rw [Cmd.eval_ifBit_true rSA (setZero rWF) nop _ (by simp [Cmd.eval_seq, g4SA, h1]),
      Cmd.eval_ifBit_true rSB (setZero rWF) nop _ (by
        rw [setZero_get_ne rWF rSB _ (by decide)]; simp only [Cmd.eval_seq]; rw [g4SB];
        simp [h2])]
    constructor
    · simp [setZero, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
        State.get_set_ne, CnfWellFormed.wfCnfB, h1, h2]
    · rw [setZero_get_ne rWF rIN _ (by decide), setZero_get_ne rWF rIN _ (by decide)]
      simp only [Cmd.eval_seq]; exact g4IN


/-- One cell of the renaming pass, as a pure state transition on
`(output, occurrence counter, in-literal, in-variable-block)`. Mirrors
`renameBody` exactly. -/
def renStep : List Nat × Nat × Bool × Bool → Nat → List Nat × Nat × Bool × Bool
  | (out, j, false, sb), cell =>
      if cell = 1 then (out ++ [1], j, true, false) else (out ++ [0], j, false, sb)
  | (out, j, true, false), cell => (out ++ [cell], j, true, true)
  | (out, j, true, true), cell =>
      if cell = 1 then (out, j, true, true)
      else (out ++ List.replicate j 1 ++ [0], j + 1, false, false)

/-- The renaming pass over a whole stream. -/
def renRun (l : List Nat) : List Nat × Nat × Bool × Bool :=
  l.foldl renStep ([], 0, false, false)

theorem renameBody_eval (st : State) (sa sb : Bool) (cell : Nat) (rest : List Nat)
    (out : List Nat) (j : Nat) (hcell : cell ≤ 1)
    (himp : sa = false → sb = false)
    (hSA : st.get rSA = [if sa then 1 else 0]) (hSB : st.get rSB = [if sb then 1 else 0])
    (hCUR : st.get rCUR = cell :: rest) (hOUT : st.get rOUT = out)
    (hJ : st.get rJ = List.replicate j 1) :
    (renameBody.eval st).get rCUR = rest ∧
    (renameBody.eval st).get rOUT = (renStep (out, j, sa, sb) cell).1 ∧
    (renameBody.eval st).get rJ = List.replicate (renStep (out, j, sa, sb) cell).2.1 1 ∧
    (renameBody.eval st).get rSA =
      [if (renStep (out, j, sa, sb) cell).2.2.1 then 1 else 0] ∧
    (renameBody.eval st).get rSB =
      [if (renStep (out, j, sa, sb) cell).2.2.2 then 1 else 0] := by
  have step1 : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rCUR = rest := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1HD : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rHD = [cell] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1SA : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSA =
      [if sa then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSA, State.get_set_ne]
  have step1SB : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSB =
      [if sb then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSB, State.get_set_ne]
  have step1OUT : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rOUT = out := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hOUT, State.get_set_ne]
  have step1J : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rJ =
      List.replicate j 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hJ, State.get_set_ne]
  have hsplit : renameBody.eval st = (Cmd.ifBit rSA
      (Cmd.ifBit rSB
        (Cmd.ifBit rHD nop
          (Cmd.op (.concat rOUT rOUT rJ) ;; Cmd.op (.appendZero rOUT) ;;
           Cmd.op (.appendOne rJ) ;; setZero rSA ;; setZero rSB))
        (emitBit ;; setOne rSB))
      (Cmd.ifBit rHD
        (Cmd.op (.appendOne rOUT) ;; setOne rSA ;; setZero rSB)
        (Cmd.op (.appendZero rOUT)))).eval
        ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st) := by
    simp only [renameBody, Cmd.eval_seq]
  rw [hsplit]
  cases sa with
  | false =>
      have hsb : sb = false := himp rfl
      subst hsb
      rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SA])]
      by_cases hcell1 : cell = 1
      · subst hcell1
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR, hCUR]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell1])]
        have hc0 : cell = 0 := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR,
            hcell1, hc0]
  | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SA])]
      cases sb with
      | false =>
          rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SB])]
          by_cases hcell1 : cell = 1
          · subst hcell1
            rw [show (emitBit ;; setOne rSB) =
              (Cmd.ifBit rHD (Cmd.op (.appendOne rOUT)) (Cmd.op (.appendZero rOUT)) ;;
                setOne rSB) from rfl,
              Cmd.eval_seq,
              Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR, hCUR]
          · have hc0 : cell = 0 := by omega
            rw [show (emitBit ;; setOne rSB) =
              (Cmd.ifBit rHD (Cmd.op (.appendOne rOUT)) (Cmd.op (.appendZero rOUT)) ;;
                setOne rSB) from rfl,
              Cmd.eval_seq,
              Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell1])]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR,
                hcell1, hc0]
      | true =>
          rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SB])]
          by_cases hcell1 : cell = 1
          · subst hcell1
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR, hCUR]
          · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell1])]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, emitBit, renStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J, step1SA, step1SB, hSA, hSB, hOUT, hJ, hCUR,
                hcell1, List.replicate_succ']


theorem renRun_take_succ (l : List Nat) (i : Nat) (hi : i < l.length) :
    renRun (l.take (i + 1)) = renStep (renRun (l.take i)) l[i] := by
  have htake : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hi]
  show List.foldl renStep ([], 0, false, false) (l.take (i + 1)) = _
  rw [htake, List.foldl_append]
  rfl

theorem renStep_himp (st : List Nat × Nat × Bool × Bool) (cell : Nat)
    (h : st.2.2.1 = false → st.2.2.2 = false) :
    (renStep st cell).2.2.1 = false → (renStep st cell).2.2.2 = false := by
  obtain ⟨out, j, sa, sb⟩ := st
  cases sa with
  | false =>
      have hsb : sb = false := h rfl
      subst hsb
      by_cases hc : cell = 1 <;> simp [renStep, hc]
  | true => cases sb <;> by_cases hc : cell = 1 <;> simp [renStep, hc]

theorem renameLoop (l : List Nat) (hl : ∀ c ∈ l, c ≤ 1) (s : State)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l)
    (hOUT : s.get rOUT = []) (hJ : s.get rJ = List.replicate 0 1)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0]) :
    ((Cmd.forBnd rIDX2 rIN renameBody).eval s).get rOUT = (renRun l).1 ∧
    ((Cmd.forBnd rIDX2 rIN renameBody).eval s).get rJ =
      List.replicate (renRun l).2.1 1 ∧
    ((Cmd.forBnd rIDX2 rIN renameBody).eval s).get rIN = l := by
  rw [Cmd.eval_forBnd, hIN]
  have key := Cmd.foldlState_range_induct renameBody rIDX2 l.length s
    (fun i st => st.get rCUR = l.drop i ∧
      st.get rOUT = (renRun (l.take i)).1 ∧
      st.get rJ = List.replicate (renRun (l.take i)).2.1 1 ∧
      st.get rSA = [if (renRun (l.take i)).2.2.1 then 1 else 0] ∧
      st.get rSB = [if (renRun (l.take i)).2.2.2 then 1 else 0] ∧
      ((renRun (l.take i)).2.2.1 = false → (renRun (l.take i)).2.2.2 = false) ∧
      st.get rIN = l)
    (by simp [renRun, hCUR, hOUT, hJ, hSA, hSB, hIN])
    (by
      intro i st hi hM
      obtain ⟨hCURi, hOUTi, hJi, hSAi, hSBi, himpi, hINi⟩ := hM
      rw [List.drop_eq_getElem_cons hi] at hCURi
      have hcell : l[i] ≤ 1 := hl _ (List.getElem_mem hi)
      have hCUR' : (st.set rIDX2 (List.replicate i 1)).get rCUR = l[i] :: l.drop (i + 1) := by
        simp [State.get_set_ne, hCURi]
      have hOUT' : (st.set rIDX2 (List.replicate i 1)).get rOUT = (renRun (l.take i)).1 := by
        simp [State.get_set_ne, hOUTi]
      have hJ' : (st.set rIDX2 (List.replicate i 1)).get rJ =
          List.replicate (renRun (l.take i)).2.1 1 := by
        simp [State.get_set_ne, hJi]
      have hSA' : (st.set rIDX2 (List.replicate i 1)).get rSA =
          [if (renRun (l.take i)).2.2.1 then 1 else 0] := by
        simp [State.get_set_ne, hSAi]
      have hSB' : (st.set rIDX2 (List.replicate i 1)).get rSB =
          [if (renRun (l.take i)).2.2.2 then 1 else 0] := by
        simp [State.get_set_ne, hSBi]
      have hIN' : (st.set rIDX2 (List.replicate i 1)).get rIN = l := by
        simp [State.get_set_ne, hINi]
      obtain ⟨hCURn, hOUTn, hJn, hSAn, hSBn⟩ := renameBody_eval
        (st.set rIDX2 (List.replicate i 1))
        (renRun (l.take i)).2.2.1 (renRun (l.take i)).2.2.2
        l[i] (l.drop (i + 1)) (renRun (l.take i)).1 (renRun (l.take i)).2.1
        hcell himpi hSA' hSB' hCUR' hOUT' hJ'
      refine ⟨hCURn, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [renRun_take_succ l i hi]; exact hOUTn
      · rw [renRun_take_succ l i hi]; exact hJn
      · rw [renRun_take_succ l i hi]; exact hSAn
      · rw [renRun_take_succ l i hi]; exact hSBn
      · rw [renRun_take_succ l i hi]; exact renStep_himp _ _ himpi
      · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes renameBody)]
        exact hIN')
  obtain ⟨-, hOUTf, hJf, -, -, -, hINf⟩ := key
  rw [List.take_of_length_le (le_refl _)] at hOUTf hJf
  exact ⟨hOUTf, hJf, hINf⟩

theorem renameProg_eval (s : State) (l : List Nat) (hl : ∀ c ∈ l, c ≤ 1)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l) :
    (renameProg.eval s).get rOUT = (renRun l).1 ∧
    (renameProg.eval s).get rIN = l := by
  have gJ : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rJ =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gOUT : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rOUT = [] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSA : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rSA = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSB : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rSB = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gCUR : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rCUR = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hCUR]
  have gIN : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rIN = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  obtain ⟨hOUTf, -, hINf⟩ := renameLoop l hl _ gCUR gIN gOUT gJ gSA gSB
  constructor
  · have : (renameProg.eval s).get rOUT =
        ((Cmd.forBnd rIDX2 rIN renameBody).eval ((setZero rSB).eval ((setZero rSA).eval
          ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s))))).get rOUT := by
      simp only [renameProg, Cmd.eval_seq]
    rw [this]; exact hOUTf
  · have : (renameProg.eval s).get rIN =
        ((Cmd.forBnd rIDX2 rIN renameBody).eval ((setZero rSB).eval ((setZero rSA).eval
          ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s))))).get rIN := by
      simp only [renameProg, Cmd.eval_seq]
    rw [this]; exact hINf

/-- Folding the renaming pass over a block of variable ones changes nothing. -/
theorem renFold_replicate (v : Nat) (o : List Nat) (j : Nat) :
    (List.replicate v 1).foldl renStep (o, j, true, true) = (o, j, true, true) := by
  induction v with
  | zero => rfl
  | succ v ih =>
      rw [List.replicate_succ, List.foldl_cons]
      show (List.replicate v 1).foldl renStep (renStep (o, j, true, true) 1) = _
      rw [show renStep (o, j, true, true) 1 = (o, j, true, true) from by simp [renStep]]
      exact ih

/-- Folding the renaming pass over one encoded literal renames its variable
to the current occurrence index. -/
theorem renFold_lit (pol : Bool) (v j : Nat) (out : List Nat) :
    (EvalCnfCmd.encodeLit (pol, v)).foldl renStep (out, j, false, false) =
      (out ++ EvalCnfCmd.encodeLit (pol, j), j + 1, false, false) := by
  show ((1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).foldl renStep
      (out, j, false, false)) = _
  rw [List.foldl_cons, List.foldl_cons]
  show ((List.replicate v 1 ++ [0]).foldl renStep
      (renStep (renStep (out, j, false, false) 1) (if pol then 1 else 0))) = _
  rw [show renStep (renStep (out, j, false, false) 1) (if pol then 1 else 0) =
      (out ++ [1, if pol then 1 else 0], j, true, true) from by simp [renStep],
    List.foldl_append, renFold_replicate]
  show renStep (out ++ [1, if pol then 1 else 0], j, true, true) 0 = _
  rw [show renStep (out ++ [1, if pol then 1 else 0], j, true, true) 0 =
      (out ++ [1, if pol then 1 else 0] ++ List.replicate j 1 ++ [0], j + 1, false, false)
      from by simp [renStep]]
  simp [EvalCnfCmd.encodeLit, List.append_assoc]

/-- Folding the renaming pass over one encoded clause. -/
theorem renFold_clause (C : clause) (out : List Nat) (j : Nat) :
    (EvalCnfCmd.encodeClause C).foldl renStep (out, j, false, false) =
      (out ++ EvalCnfCmd.encodeClause (renameClause 0 j C), j + C.length, false, false) := by
  induction C generalizing out j with
  | nil =>
      show ([0] : List Nat).foldl renStep (out, j, false, false) = _
      rw [List.foldl_cons, List.foldl_nil]
      show renStep (out, j, false, false) 0 = _
      rw [show renStep (out, j, false, false) 0 = (out ++ [0], j, false, false) from by
        simp [renStep]]
      simp [renameClause, EvalCnfCmd.encodeClause]
  | cons lit C ih =>
      obtain ⟨pol, v⟩ := lit
      have henc : EvalCnfCmd.encodeClause ((pol, v) :: C) =
          EvalCnfCmd.encodeLit (pol, v) ++ EvalCnfCmd.encodeClause C := by
        simp [EvalCnfCmd.encodeClause, List.append_assoc]
      rw [henc, List.foldl_append, renFold_lit, ih]
      have hren : renameClause 0 j ((pol, v) :: C) =
          (pol, j) :: renameClause 0 (j + 1) C := by
        simp [renameClause, List.zipIdx_cons]
      rw [hren]
      have henc2 : EvalCnfCmd.encodeClause ((pol, j) :: renameClause 0 (j + 1) C) =
          EvalCnfCmd.encodeLit (pol, j) ++
            EvalCnfCmd.encodeClause (renameClause 0 (j + 1) C) := by
        simp [EvalCnfCmd.encodeClause, List.append_assoc]
      rw [henc2]
      simp [List.append_assoc, List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Folding the renaming pass over a whole encoded CNF: the output is the
encoding of the renamed CNF. -/
theorem renFold_cnf (N : cnf) (out : List Nat) (j : Nat) :
    (EvalCnfCmd.encodeCnf N).foldl renStep (out, j, false, false) =
      (out ++ EvalCnfCmd.encodeCnf (renameFrom 0 j N), j + N.flatten.length,
        false, false) := by
  induction N generalizing out j with
  | nil => simp [EvalCnfCmd.encodeCnf, renameFrom]
  | cons C N ih =>
      have henc : EvalCnfCmd.encodeCnf (C :: N) =
          EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf N := by
        simp [EvalCnfCmd.encodeCnf]
      rw [henc, List.foldl_append, renFold_clause, ih]
      simp [renameFrom, EvalCnfCmd.encodeCnf, List.append_assoc, List.flatten_cons,
        List.length_append, Nat.add_assoc]

/-- The renaming pass over an encoded CNF produces the renamed encoding. -/
theorem renRun_encodeCnf (N : cnf) :
    renRun (EvalCnfCmd.encodeCnf N) =
      (EvalCnfCmd.encodeCnf (renameCnf 0 N), N.flatten.length, false, false) := by
  have h := renFold_cnf N [] 0
  simpa [renRun, renameCnf] using h

/-- One cell of the per-variable scan in phase B, as a pure state transition
on `(output, occurrence counter, previous occurrence, first occurrence,
seen-any, current variable, in-literal, in-variable-block)`. Mirrors
`linksBody` (with `processOcc` at the end of a variable block). -/
def linkStep (v : Nat) :
    List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool → Nat →
    List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool
  | (out, k, prev, first, has, vacc, false, sb), cell =>
      if cell = 1 then (out, k, prev, first, has, vacc, true, false)
      else (out, k, prev, first, has, vacc, false, sb)
  | (out, k, prev, first, has, vacc, true, false), _ =>
      (out, k, prev, first, has, 0, true, true)
  | (out, k, prev, first, has, vacc, true, true), cell =>
      if cell = 1 then (out, k, prev, first, has, vacc + 1, true, true)
      else if vacc = v then
        if has then
          (out ++ EvalCnfCmd.encodeClause [(false, prev), (true, k)], k + 1, k, first,
            true, vacc, false, false)
        else (out, k + 1, k, k, true, vacc, false, false)
      else (out, k + 1, prev, first, has, vacc, false, false)

/-- The effect of `processOcc` on the registers it touches. -/
theorem processOcc_eval (st : State) (v vacc k prev first : Nat) (has : Bool)
    (out : List Nat)
    (hVARACC : st.get rVARACC = List.replicate vacc 1)
    (hVCTR : st.get rVCTR = List.replicate v 1)
    (hJ2 : st.get rJ2 = List.replicate k 1) (hPREV : st.get rPREV = List.replicate prev 1)
    (hFIRST : st.get rFIRST = List.replicate first 1)
    (hHAS : st.get rHAS = [if has then 1 else 0])
    (hOUT : st.get rOUT = out) :
    (processOcc.eval st).get rOUT =
      (if vacc = v then
        (if has then out ++ EvalCnfCmd.encodeClause [(false, prev), (true, k)] else out)
      else out) ∧
    (processOcc.eval st).get rJ2 = List.replicate (k + 1) 1 ∧
    (processOcc.eval st).get rPREV = List.replicate (if vacc = v then k else prev) 1 ∧
    (processOcc.eval st).get rFIRST =
      List.replicate (if vacc = v then (if has then first else k) else first) 1 ∧
    (processOcc.eval st).get rHAS = [if vacc = v then 1 else if has then 1 else 0] ∧
    (processOcc.eval st).get rVARACC = List.replicate vacc 1 := by
  have hrepl : (List.replicate vacc 1 = List.replicate v 1) ↔ vacc = v := by
    constructor
    · intro h
      have := congrArg List.length h
      simpa [List.length_replicate] using this
    · intro h; rw [h]
  have s1EQ : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rEQ =
      (if vacc = v then [1] else [0]) := by
    simp [Cmd.eval_op, Op.eval, hVARACC, hVCTR, hrepl, State.get_set_eq]
  have s1OUT : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rOUT = out := by
    simp [Cmd.eval_op, Op.eval, hOUT, State.get_set_ne]
  have s1J2 : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rJ2 =
      List.replicate k 1 := by
    simp [Cmd.eval_op, Op.eval, hJ2, State.get_set_ne]
  have s1PREV : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rPREV =
      List.replicate prev 1 := by
    simp [Cmd.eval_op, Op.eval, hPREV, State.get_set_ne]
  have s1FIRST : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rFIRST =
      List.replicate first 1 := by
    simp [Cmd.eval_op, Op.eval, hFIRST, State.get_set_ne]
  have s1HAS : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rHAS =
      [if has then 1 else 0] := by
    simp [Cmd.eval_op, Op.eval, hHAS, State.get_set_ne]
  have s1VARACC : ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st).get rVARACC =
      List.replicate vacc 1 := by
    simp [Cmd.eval_op, Op.eval, hVARACC, State.get_set_ne]
  have hsplit : processOcc.eval st = (Cmd.op (.appendOne rJ2)).eval
      ((Cmd.ifBit rEQ
        (Cmd.ifBit rHAS
          (emitLink rPREV rJ2 ;; Cmd.op (.copy rPREV rJ2))
          (Cmd.op (.copy rFIRST rJ2) ;; setOne rHAS ;; Cmd.op (.copy rPREV rJ2)))
        nop).eval ((Cmd.op (.eqBit rEQ rVARACC rVCTR)).eval st)) := by
    simp only [processOcc, Cmd.eval_seq]
  rw [hsplit]
  by_cases hvacc : vacc = v
  · subst hvacc
    rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [s1EQ])]
    cases has with
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by
          simp [Cmd.eval_seq, s1HAS])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [emitLink, setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, s1OUT, s1J2, s1PREV, s1FIRST, s1HAS,
            s1VARACC, hVARACC, hVCTR, hJ2, hPREV, hFIRST, hHAS, hOUT,
            EvalCnfCmd.encodeClause, EvalCnfCmd.encodeLit, List.append_assoc,
            List.replicate_succ']
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [s1HAS])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [emitLink, setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, s1OUT, s1J2, s1PREV, s1FIRST, s1HAS,
            s1VARACC, hVARACC, hVCTR, hJ2, hPREV, hFIRST, hHAS, hOUT,
            EvalCnfCmd.encodeClause, EvalCnfCmd.encodeLit, List.append_assoc,
            List.replicate_succ']
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [s1EQ, hvacc])]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [emitLink, setZero, setOne, nop, Cmd.eval_seq, Cmd.eval_op, Op.eval,
        State.get_set_eq, State.get_set_ne, s1OUT, s1J2, s1PREV, s1FIRST, s1HAS,
        s1VARACC, hVARACC, hVCTR, hJ2, hPREV, hFIRST, hHAS, hOUT, hvacc,
        EvalCnfCmd.encodeClause, EvalCnfCmd.encodeLit, List.append_assoc,
        List.replicate_succ']


/-- One cell of the per-variable scan: the register effect of `linksBody`
is exactly `linkStep`. -/
theorem linksBody_eval (st : State) (v : Nat) (sa sb : Bool) (cell : Nat)
    (rest out : List Nat) (k prev first vacc : Nat) (has : Bool) (hcell : cell ≤ 1)
    (himp : sa = false → sb = false)
    (hSA : st.get rSA = [if sa then 1 else 0]) (hSB : st.get rSB = [if sb then 1 else 0])
    (hCUR : st.get rCUR = cell :: rest) (hOUT : st.get rOUT = out)
    (hJ2 : st.get rJ2 = List.replicate k 1) (hPREV : st.get rPREV = List.replicate prev 1)
    (hFIRST : st.get rFIRST = List.replicate first 1)
    (hHAS : st.get rHAS = [if has then 1 else 0])
    (hVARACC : st.get rVARACC = List.replicate vacc 1)
    (hVCTR : st.get rVCTR = List.replicate v 1) :
    (linksBody.eval st).get rCUR = rest ∧
    (linksBody.eval st).get rOUT =
      (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).1 ∧
    (linksBody.eval st).get rJ2 =
      List.replicate (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.1 1 ∧
    (linksBody.eval st).get rPREV =
      List.replicate (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.1 1 ∧
    (linksBody.eval st).get rFIRST =
      List.replicate (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.2.1 1 ∧
    (linksBody.eval st).get rHAS =
      [if (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.2.2.1 then 1
      else 0] ∧
    (linksBody.eval st).get rVARACC =
      List.replicate (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.2.2.2.1
        1 ∧
    (linksBody.eval st).get rSA =
      [if (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.2.2.2.2.1 then 1
      else 0] ∧
    (linksBody.eval st).get rSB =
      [if (linkStep v (out, k, prev, first, has, vacc, sa, sb) cell).2.2.2.2.2.2.2 then 1
      else 0] := by
  have step1 : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rCUR
      = rest := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1HD : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rHD
      = [cell] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hCUR, State.get_set_eq, State.get_set_ne]
  have step1SA : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSA =
      [if sa then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSA, State.get_set_ne]
  have step1SB : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rSB =
      [if sb then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hSB, State.get_set_ne]
  have step1OUT : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rOUT
      = out := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hOUT, State.get_set_ne]
  have step1J2 : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rJ2 =
      List.replicate k 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hJ2, State.get_set_ne]
  have step1PREV : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get
      rPREV = List.replicate prev 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hPREV, State.get_set_ne]
  have step1FIRST : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get
      rFIRST = List.replicate first 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hFIRST, State.get_set_ne]
  have step1HAS : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get rHAS =
      [if has then 1 else 0] := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hHAS, State.get_set_ne]
  have step1VARACC : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get
      rVARACC = List.replicate vacc 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hVARACC, State.get_set_ne]
  have step1VCTR : ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st).get
      rVCTR = List.replicate v 1 := by
    simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, hVCTR, State.get_set_ne]
  have hsplit : linksBody.eval st = (Cmd.ifBit rSA
      (Cmd.ifBit rSB
        (Cmd.ifBit rHD (Cmd.op (.appendOne rVARACC))
          (processOcc ;; setZero rSA ;; setZero rSB))
        (setOne rSB ;; Cmd.op (.clear rVARACC)))
      (Cmd.ifBit rHD (setOne rSA ;; setZero rSB) nop)).eval
        ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st) := by
    simp only [linksBody, Cmd.eval_seq]
  rw [hsplit]
  cases sa with
  | false =>
      have hsb : sb = false := himp rfl
      subst hsb
      rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SA])]
      by_cases hcell1 : cell = 1
      · subst hcell1
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
            step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
            hJ2, hPREV, hFIRST, hHAS, hVARACC]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell1])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
            State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
            step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
            hJ2, hPREV, hFIRST, hHAS, hVARACC, hcell1]
  | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SA])]
      cases sb with
      | false =>
          rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1SB])]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · rw [Cmd.eval_get_of_not_writes _ _ _
              (by decide : rHAS ∉ Cmd.writes (setOne rSB ;; Cmd.op (.clear rVARACC))),
              step1HAS,
              show (linkStep v (out, k, prev, first, has, vacc, true, false)
                cell).2.2.2.2.1 = has from rfl]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
          · simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
              State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
              step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
              hJ2, hPREV, hFIRST, hHAS, hVARACC]
      | true =>
          rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1SB])]
          by_cases hcell1 : cell = 1
          · subst hcell1
            rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [step1HD])]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [setZero, setOne, nop, linkStep, Cmd.eval_seq, Cmd.eval_op, Op.eval,
                State.get_set_eq, State.get_set_ne, step1, step1OUT, step1J2, step1PREV,
                step1FIRST, step1HAS, step1VARACC, step1SA, step1SB, hSA, hSB, hCUR, hOUT,
                hJ2, hPREV, hFIRST, hHAS, hVARACC, List.replicate_succ']
          · rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [step1HD, hcell1])]
            obtain ⟨pOUT, pJ2, pPREV, pFIRST, pHAS, pVARACC⟩ := processOcc_eval
              ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st)
              v vacc k prev first has out step1VARACC step1VCTR step1J2 step1PREV
              step1FIRST step1HAS step1OUT
            have hstage : ∀ (r : Var), r ≠ rSA → r ≠ rSB →
                ((processOcc ;; setZero rSA ;; setZero rSB).eval
                  ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st)).get r =
                (processOcc.eval
                  ((Cmd.op (.head rHD rCUR) ;; Cmd.op (.tail rCUR rCUR)).eval st)).get r := by
              intro r hr1 hr2
              simp only [Cmd.eval_seq]
              rw [setZero_get_ne rSB r _ hr2, setZero_get_ne rSA r _ hr1]
            by_cases hvacc : vacc = v
            · subst hvacc
              cases has with
              | true =>
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [hstage rCUR (by decide) (by decide),
                      Cmd.eval_get_of_not_writes _ _ _
                        (by decide : rCUR ∉ Cmd.writes processOcc)]
                    exact step1
                  · rw [hstage rOUT (by decide) (by decide), pOUT]
                    simp [linkStep, hcell1]
                  · rw [hstage rJ2 (by decide) (by decide), pJ2]
                    simp [linkStep, hcell1]
                  · rw [hstage rPREV (by decide) (by decide), pPREV]
                    simp [linkStep, hcell1]
                  · rw [hstage rFIRST (by decide) (by decide), pFIRST]
                    simp [linkStep, hcell1]
                  · rw [hstage rHAS (by decide) (by decide), pHAS]
                    simp [linkStep, hcell1]
                  · rw [hstage rVARACC (by decide) (by decide), pVARACC]
                    simp [linkStep, hcell1]
                  · simp only [Cmd.eval_seq]
                    rw [setZero_get_ne rSB rSA _ (by decide), setZero_get_eq]
                    simp [linkStep, hcell1]
                  · simp only [Cmd.eval_seq]
                    rw [setZero_get_eq]
                    simp [linkStep, hcell1]
              | false =>
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [hstage rCUR (by decide) (by decide),
                      Cmd.eval_get_of_not_writes _ _ _
                        (by decide : rCUR ∉ Cmd.writes processOcc)]
                    exact step1
                  · rw [hstage rOUT (by decide) (by decide), pOUT]
                    simp [linkStep, hcell1]
                  · rw [hstage rJ2 (by decide) (by decide), pJ2]
                    simp [linkStep, hcell1]
                  · rw [hstage rPREV (by decide) (by decide), pPREV]
                    simp [linkStep, hcell1]
                  · rw [hstage rFIRST (by decide) (by decide), pFIRST]
                    simp [linkStep, hcell1]
                  · rw [hstage rHAS (by decide) (by decide), pHAS]
                    simp [linkStep, hcell1]
                  · rw [hstage rVARACC (by decide) (by decide), pVARACC]
                    simp [linkStep, hcell1]
                  · simp only [Cmd.eval_seq]
                    rw [setZero_get_ne rSB rSA _ (by decide), setZero_get_eq]
                    simp [linkStep, hcell1]
                  · simp only [Cmd.eval_seq]
                    rw [setZero_get_eq]
                    simp [linkStep, hcell1]
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hstage rCUR (by decide) (by decide),
                  Cmd.eval_get_of_not_writes _ _ _
                    (by decide : rCUR ∉ Cmd.writes processOcc)]
                exact step1
              · rw [hstage rOUT (by decide) (by decide), pOUT]
                simp [linkStep, hcell1, hvacc]
              · rw [hstage rJ2 (by decide) (by decide), pJ2]
                simp [linkStep, hcell1, hvacc]
              · rw [hstage rPREV (by decide) (by decide), pPREV]
                simp [linkStep, hcell1, hvacc]
              · rw [hstage rFIRST (by decide) (by decide), pFIRST]
                simp [linkStep, hcell1, hvacc]
              · rw [hstage rHAS (by decide) (by decide), pHAS]
                simp [linkStep, hcell1, hvacc]
              · rw [hstage rVARACC (by decide) (by decide), pVARACC]
                simp [linkStep, hcell1, hvacc]
              · simp only [Cmd.eval_seq]
                rw [setZero_get_ne rSB rSA _ (by decide), setZero_get_eq]
                simp [linkStep, hcell1, hvacc]
              · simp only [Cmd.eval_seq]
                rw [setZero_get_eq]
                simp [linkStep, hcell1, hvacc]


/-- The scan of one pass, from an arbitrary output prefix and initial
variable-block accumulator. -/
def linkRunFrom (v : Nat) (out : List Nat) (vacc : Nat) (l : List Nat) :
    List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool :=
  l.foldl (linkStep v) (out, 0, 0, 0, false, vacc, false, false)

theorem linkRunFrom_take_succ (v : Nat) (out : List Nat) (vacc : Nat) (l : List Nat)
    (i : Nat) (hi : i < l.length) :
    linkRunFrom v out vacc (l.take (i + 1)) =
      linkStep v (linkRunFrom v out vacc (l.take i)) l[i] := by
  have htake : l.take (i + 1) = l.take i ++ [l[i]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hi]
  show List.foldl (linkStep v) (out, 0, 0, 0, false, vacc, false, false)
      (l.take (i + 1)) = _
  rw [htake, List.foldl_append]
  rfl

theorem linkStep_himp (v : Nat)
    (st : List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool) (cell : Nat)
    (h : st.2.2.2.2.2.2.1 = false → st.2.2.2.2.2.2.2 = false) :
    (linkStep v st cell).2.2.2.2.2.2.1 = false →
      (linkStep v st cell).2.2.2.2.2.2.2 = false := by
  obtain ⟨out, k, prev, first, has, vacc, sa, sb⟩ := st
  cases sa with
  | false =>
      have hsb : sb = false := h rfl
      subst hsb
      by_cases hc : cell = 1 <;> simp [linkStep, hc]
  | true =>
      cases sb with
      | false => simp [linkStep]
      | true =>
          by_cases hc : cell = 1 <;> simp [linkStep, hc]
          by_cases hv : vacc = v <;> simp [linkStep, hc, hv]
          cases has <;> simp [linkStep, hc, hv]

theorem linksLoop (v : Nat) (l : List Nat) (hl : ∀ c ∈ l, c ≤ 1) (s : State)
    (out0 : List Nat) (vacc0 : Nat)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l) (hOUT : s.get rOUT = out0)
    (hJ2 : s.get rJ2 = List.replicate 0 1) (hPREV : s.get rPREV = List.replicate 0 1)
    (hFIRST : s.get rFIRST = List.replicate 0 1) (hHAS : s.get rHAS = [0])
    (hVARACC : s.get rVARACC = List.replicate vacc0 1)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0])
    (hVCTR : s.get rVCTR = List.replicate v 1) :
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rOUT = (linkRunFrom v out0 vacc0 l).1 ∧
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rHAS =
      [if (linkRunFrom v out0 vacc0 l).2.2.2.2.1 then 1 else 0] ∧
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rPREV =
      List.replicate (linkRunFrom v out0 vacc0 l).2.2.1 1 ∧
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rFIRST =
      List.replicate (linkRunFrom v out0 vacc0 l).2.2.2.1 1 ∧
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rVARACC =
      List.replicate (linkRunFrom v out0 vacc0 l).2.2.2.2.2.1 1 ∧
    ((Cmd.forBnd rIDX3 rIN linksBody).eval s).get rIN = l := by
  rw [Cmd.eval_forBnd, hIN]
  have key := Cmd.foldlState_range_induct linksBody rIDX3 l.length s
    (fun i st => st.get rCUR = l.drop i ∧
      st.get rOUT = (linkRunFrom v out0 vacc0 (l.take i)).1 ∧
      st.get rJ2 = List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.1 1 ∧
      st.get rPREV = List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.1 1 ∧
      st.get rFIRST = List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.1 1 ∧
      st.get rHAS =
        [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.1 then 1 else 0] ∧
      st.get rVARACC =
        List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.1 1 ∧
      st.get rSA =
        [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.1 then 1 else 0] ∧
      st.get rSB =
        [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.2 then 1 else 0] ∧
      ((linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.1 = false →
        (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.2 = false) ∧
      st.get rVCTR = List.replicate v 1 ∧
      st.get rIN = l)
    (by simp [linkRunFrom, hCUR, hOUT, hJ2, hPREV, hFIRST, hHAS, hVARACC, hSA, hSB,
      hVCTR, hIN])
    (by
      intro i st hi hM
      obtain ⟨hCURi, hOUTi, hJ2i, hPREVi, hFIRSTi, hHASi, hVARACCi, hSAi, hSBi, himpi,
        hVCTRi, hINi⟩ := hM
      rw [List.drop_eq_getElem_cons hi] at hCURi
      have hcell : l[i] ≤ 1 := hl _ (List.getElem_mem hi)
      have hCUR' : (st.set rIDX3 (List.replicate i 1)).get rCUR =
          l[i] :: l.drop (i + 1) := by simp [State.get_set_ne, hCURi]
      have hOUT' : (st.set rIDX3 (List.replicate i 1)).get rOUT =
          (linkRunFrom v out0 vacc0 (l.take i)).1 := by simp [State.get_set_ne, hOUTi]
      have hJ2' : (st.set rIDX3 (List.replicate i 1)).get rJ2 =
          List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.1 1 := by
        simp [State.get_set_ne, hJ2i]
      have hPREV' : (st.set rIDX3 (List.replicate i 1)).get rPREV =
          List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.1 1 := by
        simp [State.get_set_ne, hPREVi]
      have hFIRST' : (st.set rIDX3 (List.replicate i 1)).get rFIRST =
          List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.1 1 := by
        simp [State.get_set_ne, hFIRSTi]
      have hHAS' : (st.set rIDX3 (List.replicate i 1)).get rHAS =
          [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.1 then 1 else 0] := by
        simp [State.get_set_ne, hHASi]
      have hVARACC' : (st.set rIDX3 (List.replicate i 1)).get rVARACC =
          List.replicate (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.1 1 := by
        simp [State.get_set_ne, hVARACCi]
      have hSA' : (st.set rIDX3 (List.replicate i 1)).get rSA =
          [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.1 then 1 else 0] := by
        simp [State.get_set_ne, hSAi]
      have hSB' : (st.set rIDX3 (List.replicate i 1)).get rSB =
          [if (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.2 then 1 else 0] := by
        simp [State.get_set_ne, hSBi]
      have hVCTR' : (st.set rIDX3 (List.replicate i 1)).get rVCTR =
          List.replicate v 1 := by simp [State.get_set_ne, hVCTRi]
      have hIN' : (st.set rIDX3 (List.replicate i 1)).get rIN = l := by
        simp [State.get_set_ne, hINi]
      obtain ⟨hCURn, hOUTn, hJ2n, hPREVn, hFIRSTn, hHASn, hVARACCn, hSAn, hSBn⟩ :=
        linksBody_eval (st.set rIDX3 (List.replicate i 1)) v
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.1
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.2.2
          l[i] (l.drop (i + 1)) (linkRunFrom v out0 vacc0 (l.take i)).1
          (linkRunFrom v out0 vacc0 (l.take i)).2.1
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.1
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.1
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.2.1
          (linkRunFrom v out0 vacc0 (l.take i)).2.2.2.2.1
          hcell himpi hSA' hSB' hCUR' hOUT' hJ2' hPREV' hFIRST' hHAS' hVARACC' hVCTR'
      refine ⟨hCURn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hOUTn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hJ2n
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hPREVn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hFIRSTn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hHASn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hVARACCn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hSAn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]; exact hSBn
      · rw [linkRunFrom_take_succ v out0 vacc0 l i hi]
        exact linkStep_himp v _ _ himpi
      · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rVCTR ∉ Cmd.writes linksBody)]
        exact hVCTR'
      · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes linksBody)]
        exact hIN')
  obtain ⟨-, hOUTf, -, hPREVf, hFIRSTf, hHASf, hVARACCf, -, -, -, -, hINf⟩ := key
  rw [List.take_of_length_le (le_refl _)] at hOUTf hPREVf hFIRSTf hHASf hVARACCf
  exact ⟨hOUTf, hHASf, hPREVf, hFIRSTf, hVARACCf, hINf⟩

/-- The effect of `emitLink a b` on the output register. -/
theorem emitLink_eval (st : State) (a b : Var) (va vb : Nat) (out : List Nat)
    (ha : st.get a = List.replicate va 1) (hb : st.get b = List.replicate vb 1)
    (hOUT : st.get rOUT = out) (haO : a ≠ rOUT) (hbO : b ≠ rOUT) :
    ((emitLink a b).eval st).get rOUT =
      out ++ EvalCnfCmd.encodeClause [(false, va), (true, vb)] := by
  simp [emitLink, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
    ha, hb, hOUT, haO, hbO, EvalCnfCmd.encodeClause, EvalCnfCmd.encodeLit,
    List.append_assoc]

/-- One full pass of phase B: scan the input for variable `v` and append the
implication cycle of its occurrences (including the closing clause). -/
theorem linksPass_eval (s : State) (v : Nat) (l : List Nat) (hl : ∀ c ∈ l, c ≤ 1)
    (out0 : List Nat) (vacc0 : Nat)
    (hIN : s.get rIN = l) (hOUT : s.get rOUT = out0)
    (hVARACC : s.get rVARACC = List.replicate vacc0 1)
    (hVCTR : s.get rVCTR = List.replicate v 1) :
    (linksPass.eval s).get rOUT =
      (linkRunFrom v out0 vacc0 l).1 ++
        (if (linkRunFrom v out0 vacc0 l).2.2.2.2.1 then
          EvalCnfCmd.encodeClause
            [(false, (linkRunFrom v out0 vacc0 l).2.2.1),
             (true, (linkRunFrom v out0 vacc0 l).2.2.2.1)]
        else []) ∧
    (linksPass.eval s).get rIN = l ∧
    (linksPass.eval s).get rVARACC =
      List.replicate (linkRunFrom v out0 vacc0 l).2.2.2.2.2.1 1 := by
  have gCUR : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rCUR =
      l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
      hIN]
  have gIN : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rIN =
      l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  have gOUT : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rOUT =
      out0 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hOUT]
  have gJ2 : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rJ2 =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gPREV : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rPREV =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gFIRST : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rFIRST =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gHAS : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rHAS =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gVARACC : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rVARACC =
      List.replicate vacc0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hVARACC]
  have gSA : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rSA =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSB : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rSB =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gVCTR : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rVCTR =
      List.replicate v 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hVCTR]
  obtain ⟨hOUTf, hHASf, hPREVf, hFIRSTf, hVARACCf, hINf⟩ := linksLoop v l hl
    ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))))))
    out0 vacc0 gCUR gIN gOUT gJ2 gPREV gFIRST gHAS gVARACC gSA gSB gVCTR
  have hstage : linksPass.eval s = (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).eval
      ((Cmd.forBnd rIDX3 rIN linksBody).eval
        ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
          ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
            ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))))))) := by
    simp only [linksPass, Cmd.eval_seq]
  rw [hstage]
  refine ⟨?_, ?_, ?_⟩
  · cases hh : (linkRunFrom v out0 vacc0 l).2.2.2.2.1 with
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [hHASf, hh]),
          Cmd.eval_get_of_not_writes _ _ _ (by decide : rOUT ∉ Cmd.writes nop), hOUTf]
        simp
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [hHASf, hh]),
          emitLink_eval _ rPREV rFIRST _ _ _ hPREVf hFIRSTf hOUTf (by decide) (by decide)]
        simp
  · cases hh : (linkRunFrom v out0 vacc0 l).2.2.2.2.1 with
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [hHASf, hh]),
          Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes nop)]
        exact hINf
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [hHASf, hh]),
          Cmd.eval_get_of_not_writes _ _ _
            (by decide : rIN ∉ Cmd.writes (emitLink rPREV rFIRST))]
        exact hINf
  · cases hh : (linkRunFrom v out0 vacc0 l).2.2.2.2.1 with
    | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by simp [hHASf, hh]),
          Cmd.eval_get_of_not_writes _ _ _ (by decide : rVARACC ∉ Cmd.writes nop)]
        exact hVARACCf
    | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by simp [hHASf, hh]),
          Cmd.eval_get_of_not_writes _ _ _
            (by decide : rVARACC ∉ Cmd.writes (emitLink rPREV rFIRST))]
        exact hVARACCf






/-- The implication chain over a list of occurrence positions, given the
chain's first position and the previous position. -/
def chainFrom (fst prev : Nat) : List Nat → List clause
  | [] => []
  | j :: js => [(false, prev), (true, j)] :: chainFrom fst j js

/-- Thread `(first, previous, seen-any)` over a list of occurrence positions,
emitting the implication chain. -/
def chainEmit (first prev : Nat) (has : Bool) : List Nat → List clause × Nat × Nat × Bool
  | [] => ([], prev, first, has)
  | j :: js => if has then
      ([(false, prev), (true, j)] :: (chainEmit first j true js).1,
       (chainEmit first j true js).2.1, (chainEmit first j true js).2.2.1, true)
    else chainEmit j j true js

/-- The positions of variable `v` inside one clause, counted from `k`. -/
def posOfClause (k v : Nat) (C : clause) : List Nat :=
  C.findIdxs (fun l => decide (l.2 = v)) k

/-- The positions of variable `v` in a CNF, counted from `k`. -/
def posOfFrom (k v : Nat) (N : cnf) : List Nat :=
  (N.flatten).findIdxs (fun l => decide (l.2 = v)) k

theorem zipIdx_filter_map_snd_findIdxs (l : List literal) (v n : Nat) :
    ((l.zipIdx n).filter (fun p => p.1.2 = v)).map Prod.snd =
      l.findIdxs (fun l => decide (l.2 = v)) n := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
      rw [List.zipIdx_cons]
      by_cases ha : a.2 = v <;> simp [ha, ih, List.findIdxs_cons]

theorem posOf_eq (v : Nat) (N : cnf) :
    posOf v N = (N.flatten).findIdxs (fun l => decide (l.2 = v)) 0 :=
  zipIdx_filter_map_snd_findIdxs N.flatten v 0

theorem findIdxs_map_add (l : List literal) (v : Nat) (s k : Nat) :
    (l.findIdxs (fun l => decide (l.2 = v)) s).map (· + k) =
      l.findIdxs (fun l => decide (l.2 = v)) (s + k) := by
  have h1 : l.findIdxs (fun l => decide (l.2 = v)) s =
      (l.findIdxs (fun l => decide (l.2 = v))).map (· + s) := List.findIdxs_start
  have h2 : l.findIdxs (fun l => decide (l.2 = v)) (s + k) =
      (l.findIdxs (fun l => decide (l.2 = v))).map (· + (s + k)) := List.findIdxs_start
  rw [h1, h2, List.map_map]
  congr 1
  funext x
  exact Nat.add_assoc x s k

theorem posOfFrom_map (k v : Nat) (N : cnf) :
    posOfFrom k v N = (posOf v N).map (· + k) := by
  rw [posOfFrom, posOf_eq, findIdxs_map_add, Nat.zero_add]

theorem findIdxs_append (l₁ l₂ : List literal) (v : Nat) (s : Nat) :
    ((l₁ ++ l₂).findIdxs (fun l => decide (l.2 = v)) s) =
      (l₁.findIdxs (fun l => decide (l.2 = v)) s) ++
        (l₂.findIdxs (fun l => decide (l.2 = v)) (s + l₁.length)) := by
  induction l₁ generalizing s with
  | nil => simp [Nat.zero_add]
  | cons a l₁ ih =>
      by_cases ha : a.2 = v <;>
        simp [ha, List.findIdxs_cons, ih, List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

theorem posOfFrom_cons (k v : Nat) (C : clause) (N : cnf) :
    posOfFrom k v (C :: N) =
      posOfClause k v C ++ posOfFrom (k + C.length) v N := by
  simp [posOfFrom, posOfClause, List.flatten_cons, findIdxs_append]

theorem getLast?_getD_cons2 (a b : Nat) (l : List Nat) (x y : Nat) :
    (a :: b :: l).getLast?.getD x = (b :: l).getLast?.getD y := by
  cases l with
  | nil => rfl
  | cons c l => rfl

theorem chainEmit_true (f p : Nat) (js : List Nat) :
    chainEmit f p true js = (chainFrom f p js, js.getLast?.getD p, f, true) := by
  induction js generalizing p with
  | nil => rfl
  | cons j js ih =>
      simp only [chainEmit, chainFrom]
      rw [ih]
      cases js with
      | nil => rfl
      | cons x xs => rfl

theorem chainEmit_has_true (f p : Nat) (js : List Nat) :
    (chainEmit f p true js).2.2.2 = true := by
  cases js with
  | nil => rfl
  | cons j js => rfl

theorem chainEmit_append (f p : Nat) (h : Bool) (js₁ js₂ : List Nat) :
    chainEmit f p h (js₁ ++ js₂) =
      ((chainEmit f p h js₁).1 ++
        (chainEmit (chainEmit f p h js₁).2.2.1 (chainEmit f p h js₁).2.1
          (chainEmit f p h js₁).2.2.2 js₂).1,
       (chainEmit (chainEmit f p h js₁).2.2.1 (chainEmit f p h js₁).2.1
          (chainEmit f p h js₁).2.2.2 js₂).2.1,
       (chainEmit (chainEmit f p h js₁).2.2.1 (chainEmit f p h js₁).2.1
          (chainEmit f p h js₁).2.2.2 js₂).2.2.1,
       (chainEmit (chainEmit f p h js₁).2.2.1 (chainEmit f p h js₁).2.1
          (chainEmit f p h js₁).2.2.2 js₂).2.2.2) := by
  induction js₁ generalizing f p h with
  | nil => simp [chainEmit]
  | cons j js ih =>
      cases h with
      | true => simp [chainEmit, chainEmit_has_true, ih, List.append_assoc]
      | false => simp [chainEmit, chainEmit_has_true, ih, List.append_assoc]

theorem encodeCnf_append (N₁ N₂ : cnf) :
    EvalCnfCmd.encodeCnf (N₁ ++ N₂) =
      EvalCnfCmd.encodeCnf N₁ ++ EvalCnfCmd.encodeCnf N₂ := by
  induction N₁ with
  | nil => simp [EvalCnfCmd.encodeCnf]
  | cons C N ih => simp [EvalCnfCmd.encodeCnf, ih, List.append_assoc]

/-- Folding the pass scan over a block of variable ones just accumulates
the variable value. -/
theorem linkFold_replicate (v w : Nat) (out : List Nat) (k prev first : Nat)
    (has : Bool) (vacc : Nat) :
    (List.replicate w 1).foldl (linkStep v) (out, k, prev, first, has, vacc, true,
        true) =
      (out, k, prev, first, has, vacc + w, true, true) := by
  induction w generalizing vacc with
  | zero => rfl
  | succ w ih =>
      rw [List.replicate_succ, List.foldl_cons,
        show linkStep v (out, k, prev, first, has, vacc, true, true) 1 =
          (out, k, prev, first, has, vacc + 1, true, true) from by simp [linkStep],
        ih, show vacc + 1 + w = vacc + (w + 1) from by omega]

/-- Folding the pass scan over one encoded literal processes exactly one
occurrence. -/
theorem linkFold_lit (v : Nat) (pol : Bool) (w : Nat) (out : List Nat)
    (k prev first : Nat) (has : Bool) (vacc : Nat) :
    (EvalCnfCmd.encodeLit (pol, w)).foldl (linkStep v)
        (out, k, prev, first, has, vacc, false, false) =
      (out ++ (if w = v then
          (if has then EvalCnfCmd.encodeClause [(false, prev), (true, k)] else [])
        else []),
       k + 1, if w = v then k else prev,
       if w = v then (if has then first else k) else first,
       if w = v then true else has, w, false, false) := by
  show ((1 :: (if pol then 1 else 0) :: (List.replicate w 1 ++ [0])).foldl (linkStep v)
      (out, k, prev, first, has, vacc, false, false)) = _
  rw [List.foldl_cons, List.foldl_cons]
  show ((List.replicate w 1 ++ [0]).foldl (linkStep v)
      (linkStep v (linkStep v (out, k, prev, first, has, vacc, false, false) 1)
        (if pol then 1 else 0))) = _
  rw [show linkStep v (linkStep v (out, k, prev, first, has, vacc, false, false) 1)
        (if pol then 1 else 0) = (out, k, prev, first, has, 0, true, true) from by
      simp [linkStep],
    List.foldl_append, linkFold_replicate]
  show linkStep v (out, k, prev, first, has, 0 + w, true, true) 0 = _
  by_cases hv : w = v <;> cases has <;> simp [linkStep, hv]

/-- Folding the pass scan over one encoded clause. -/
theorem linkFold_clause (v : Nat) (C : clause) (out : List Nat) (k prev first : Nat)
    (has : Bool) (vacc : Nat) :
    ∃ vacc',
      (EvalCnfCmd.encodeClause C).foldl (linkStep v) (out, k, prev, first, has, vacc,
          false, false) =
        (out ++ EvalCnfCmd.encodeCnf (chainEmit first prev has (posOfClause k v C)).1,
         k + C.length, (chainEmit first prev has (posOfClause k v C)).2.1,
         (chainEmit first prev has (posOfClause k v C)).2.2.1,
         (chainEmit first prev has (posOfClause k v C)).2.2.2, vacc', false, false) := by
  induction C generalizing out k prev first has vacc with
  | nil =>
      refine ⟨vacc, ?_⟩
      show ([0] : List Nat).foldl (linkStep v) (out, k, prev, first, has, vacc,
        false, false) = _
      rw [List.foldl_cons, List.foldl_nil]
      simp [posOfClause, List.findIdxs_nil, chainEmit, linkStep, EvalCnfCmd.encodeCnf]
  | cons lit C ih =>
      obtain ⟨pol, w⟩ := lit
      have henc : EvalCnfCmd.encodeClause ((pol, w) :: C) =
          EvalCnfCmd.encodeLit (pol, w) ++ EvalCnfCmd.encodeClause C := by
        simp [EvalCnfCmd.encodeClause, List.append_assoc]
      rw [henc, List.foldl_append, linkFold_lit]
      obtain ⟨vacc', ih'⟩ := ih
        (out := out ++ (if w = v then
          (if has then EvalCnfCmd.encodeClause [(false, prev), (true, k)] else [])
          else []))
        (k := k + 1) (prev := if w = v then k else prev)
        (first := if w = v then (if has then first else k) else first)
        (has := if w = v then true else has) (vacc := w)
      refine ⟨vacc', ?_⟩
      rw [ih']
      have hpos : posOfClause k v ((pol, w) :: C) =
          if w = v then k :: posOfClause (k + 1) v C
          else posOfClause (k + 1) v C := by
        by_cases hv : w = v <;> simp [posOfClause, List.findIdxs_cons, hv]
      rw [hpos]
      by_cases hv : w = v
      · cases has with
        | true =>
            simp [hv, chainEmit, chainEmit_has_true, EvalCnfCmd.encodeCnf,
              List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        | false =>
            simp [hv, chainEmit, chainEmit_has_true, EvalCnfCmd.encodeCnf,
              List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [hv, chainEmit, List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

/-- Folding the pass scan over a whole encoded CNF. -/
theorem linkFold_cnf (v : Nat) (N : cnf) (out : List Nat) (k prev first : Nat)
    (has : Bool) (vacc : Nat) :
    ∃ vacc',
      (EvalCnfCmd.encodeCnf N).foldl (linkStep v) (out, k, prev, first, has, vacc,
          false, false) =
        (out ++ EvalCnfCmd.encodeCnf (chainEmit first prev has (posOfFrom k v N)).1,
         k + N.flatten.length, (chainEmit first prev has (posOfFrom k v N)).2.1,
         (chainEmit first prev has (posOfFrom k v N)).2.2.1,
         (chainEmit first prev has (posOfFrom k v N)).2.2.2, vacc', false, false) := by
  induction N generalizing out k prev first has vacc with
  | nil =>
      refine ⟨vacc, ?_⟩
      simp [posOfFrom, chainEmit, EvalCnfCmd.encodeCnf]
  | cons C N ih =>
      have henc : EvalCnfCmd.encodeCnf (C :: N) =
          EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf N := by
        simp [EvalCnfCmd.encodeCnf]
      rw [henc, List.foldl_append]
      obtain ⟨vacc₁, ih₁⟩ := linkFold_clause v C out k prev first has vacc
      rw [ih₁]
      obtain ⟨vacc', ih'⟩ := ih
        (out := out ++ EvalCnfCmd.encodeCnf (chainEmit first prev has
          (posOfClause k v C)).1)
        (k := k + C.length)
        (prev := (chainEmit first prev has (posOfClause k v C)).2.1)
        (first := (chainEmit first prev has (posOfClause k v C)).2.2.1)
        (has := (chainEmit first prev has (posOfClause k v C)).2.2.2)
        (vacc := vacc₁)
      refine ⟨vacc', ?_⟩
      rw [ih', posOfFrom_cons, chainEmit_append]
      simp [encodeCnf_append, List.append_assoc, List.flatten_cons, List.length_append,
        Nat.add_assoc]

/-- The chain construction of phase B, unfolded: the scan's chain plus the
closing clause is exactly `chainClauses`. -/
theorem chainClauses_chainFrom (f j : Nat) (js : List Nat) :
    chainClauses 0 f (j :: js) =
      chainFrom f j js ++ [[(false, (j :: js).getLast?.getD j), (true, f)]] := by
  induction js generalizing j with
  | nil => simp [chainClauses, chainFrom]
  | cons j2 js ih =>
      have h1 : chainClauses 0 f (j :: j2 :: js) =
          [(false, j), (true, j2)] :: chainClauses 0 f (j2 :: js) := by
        simp [chainClauses]
      have h2 : chainFrom f j (j2 :: js) =
          [(false, j), (true, j2)] :: chainFrom f j2 js := rfl
      rw [h1, ih, h2, List.cons_append]
      congr 2

/-- One pass over an encoded CNF appends exactly the encoding of the
variable's implication cycle. -/
theorem encodeCnf_nil : EvalCnfCmd.encodeCnf [] = [] := rfl

theorem encodeCnf_singleton (C : clause) :
    EvalCnfCmd.encodeCnf [C] = EvalCnfCmd.encodeClause C := by
  simp [EvalCnfCmd.encodeCnf]

theorem linkRunFrom_encodeCnf (v : Nat) (N : cnf) (out : List Nat) (vacc : Nat) :
    (linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N)).1 ++
      (if (linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N)).2.2.2.2.1 then
        EvalCnfCmd.encodeClause
          [(false, (linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N)).2.2.1),
           (true, (linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N)).2.2.2.1)]
      else []) =
    out ++ EvalCnfCmd.encodeCnf (cycleClauses 0 (posOf v N)) := by
  obtain ⟨vacc', hfold⟩ := linkFold_cnf v N out 0 0 0 false vacc
  have hrun : linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N) =
      (out ++ EvalCnfCmd.encodeCnf (chainEmit 0 0 false (posOfFrom 0 v N)).1,
       0 + N.flatten.length, (chainEmit 0 0 false (posOfFrom 0 v N)).2.1,
       (chainEmit 0 0 false (posOfFrom 0 v N)).2.2.1,
       (chainEmit 0 0 false (posOfFrom 0 v N)).2.2.2, vacc', false, false) := hfold
  have hpos : posOfFrom 0 v N = posOf v N := by rw [posOfFrom_map]; simp
  rw [hpos] at hrun
  cases hjs : posOf v N with
  | nil =>
      have hemit : chainEmit 0 0 false [] = ([], 0, 0, false) := rfl
      rw [hjs] at hrun
      rw [hemit] at hrun
      simp [hrun, cycleClauses, encodeCnf_nil]
  | cons j js =>
      have hemit : chainEmit 0 0 false (j :: js) = chainEmit j j true js := rfl
      rw [hjs] at hrun
      rw [hemit, chainEmit_true] at hrun
      have hlast : (j :: js).getLast?.getD j = js.getLast?.getD j := by
        cases js with
        | nil => rfl
        | cons x xs => rfl
      simp [hrun, cycleClauses, chainClauses_chainFrom, hlast, encodeCnf_append,
        encodeCnf_singleton, List.append_assoc]


/-- Phase B as a whole: for every `v < |input|`, append the implication
cycle of `v`'s occurrences. -/
theorem linksProg_eval (s : State) (N : cnf) (out0 : List Nat) (vacc0 : Nat)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N) (hOUT : s.get rOUT = out0)
    (hVARACC : s.get rVARACC = List.replicate vacc0 1) :
    (linksProg.eval s).get rOUT =
      out0 ++ EvalCnfCmd.encodeCnf
        ((List.range (EvalCnfCmd.encodeCnf N).length).flatMap
          (fun v => cycleClauses 0 (posOf v N))) ∧
    (linksProg.eval s).get rIN = EvalCnfCmd.encodeCnf N := by
  have hl : ∀ c ∈ EvalCnfCmd.encodeCnf N, c ≤ 1 := by
    intro c hc
    have := EvalCnfCmd.encodeCnf_bit N c hc
    omega
  rw [show linksProg = Cmd.forBnd rVCTR rIN linksPass from rfl, Cmd.eval_forBnd, hIN]
  have key := Cmd.foldlState_range_induct linksPass rVCTR (EvalCnfCmd.encodeCnf N).length s
    (fun i st => st.get rOUT =
        out0 ++ EvalCnfCmd.encodeCnf
          ((List.range i).flatMap (fun v => cycleClauses 0 (posOf v N))) ∧
      st.get rIN = EvalCnfCmd.encodeCnf N ∧
      ∃ vacc, st.get rVARACC = List.replicate vacc 1)
    (by simp [hOUT, hIN, hVARACC, encodeCnf_nil])
    (by
      intro i st hi hM
      obtain ⟨hOUTi, hINi, vacc, hVARACCi⟩ := hM
      have hOUT' : (st.set rVCTR (List.replicate i 1)).get rOUT =
          out0 ++ EvalCnfCmd.encodeCnf
            ((List.range i).flatMap (fun v => cycleClauses 0 (posOf v N))) := by
        simp [State.get_set_ne, hOUTi]
      have hIN' : (st.set rVCTR (List.replicate i 1)).get rIN =
          EvalCnfCmd.encodeCnf N := by simp [State.get_set_ne, hINi]
      have hVARACC' : (st.set rVCTR (List.replicate i 1)).get rVARACC =
          List.replicate vacc 1 := by simp [State.get_set_ne, hVARACCi]
      have hVCTR' : (st.set rVCTR (List.replicate i 1)).get rVCTR =
          List.replicate i 1 := by simp [State.get_set_eq]
      obtain ⟨hOUTf, hINf, hVARACCf⟩ := linksPass_eval (st.set rVCTR (List.replicate i 1))
        i (EvalCnfCmd.encodeCnf N) hl
        (out0 ++ EvalCnfCmd.encodeCnf
          ((List.range i).flatMap (fun v => cycleClauses 0 (posOf v N)))) vacc
        hIN' hOUT' hVARACC' hVCTR'
      refine ⟨?_, hINf, _, hVARACCf⟩
      rw [linkRunFrom_encodeCnf] at hOUTf
      rw [hOUTf]
      have hrange : (List.range (i + 1)).flatMap (fun v => cycleClauses 0 (posOf v N)) =
          (List.range i).flatMap (fun v => cycleClauses 0 (posOf v N)) ++
            cycleClauses 0 (posOf i N) := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hrange, encodeCnf_append, List.append_assoc])
  obtain ⟨hOUTf, hINf, -⟩ := key
  exact ⟨hOUTf, hINf⟩


theorem findIdxs_eq_nil_of_forall (l : List literal) (v : Nat) (s : Nat)
    (h : ∀ lit ∈ l, lit.2 ≠ v) :
    l.findIdxs (fun l => decide (l.2 = v)) s = [] := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
      rw [List.findIdxs_cons]
      simp [h a (by simp),
        ih (s + 1) (fun lit hlit => h lit (List.mem_cons_of_mem a hlit))]

theorem posOf_eq_nil_of_forall (v : Nat) (N : cnf)
    (h : ∀ lit ∈ N.flatten, lit.2 ≠ v) : posOf v N = [] := by
  rw [posOf_eq, findIdxs_eq_nil_of_forall N.flatten v 0 h]

theorem var_le_sum (N : cnf) (lit : literal) (h : lit ∈ N.flatten) :
    lit.2 ≤ (varsList N).sum :=
  List.single_le_sum (fun x _ => Nat.zero_le x) _
    (List.mem_map.mpr ⟨lit, h, rfl⟩)

theorem encodeLit_length (l : literal) :
    (EvalCnfCmd.encodeLit l).length = l.2 + 3 := by
  obtain ⟨pol, w⟩ := l
  simp [EvalCnfCmd.encodeLit]

theorem encodeClause_length (C : clause) :
    (EvalCnfCmd.encodeClause C).length = (C.map (fun l => l.2 + 3)).sum + 1 := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      have henc : EvalCnfCmd.encodeClause (a :: C) =
          EvalCnfCmd.encodeLit a ++ EvalCnfCmd.encodeClause C := by
        simp [EvalCnfCmd.encodeClause, List.append_assoc]
      rw [henc, List.length_append, encodeLit_length, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem flatten_map_sum (N : cnf) (g : literal → Nat) :
    (N.flatten.map g).sum = (N.map (fun C => (C.map g).sum)).sum := by
  induction N with
  | nil => rfl
  | cons C N ih =>
      show ((C ++ N.flatten).map g).sum = _
      rw [List.map_append, List.sum_append, ih]
      simp [List.map_cons, List.sum_cons]

theorem encodeCnf_length (N : cnf) :
    (EvalCnfCmd.encodeCnf N).length =
      (N.flatten.map (fun l => l.2 + 3)).sum + N.length := by
  induction N with
  | nil => rfl
  | cons C N ih =>
      have henc : EvalCnfCmd.encodeCnf (C :: N) =
          EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf N := by
        simp [EvalCnfCmd.encodeCnf]
      rw [henc, List.length_append, encodeClause_length, ih]
      simp only [List.flatten_cons, List.map_append, List.sum_append, List.length_cons]
      omega

theorem flatten_length_le_encodeCnf (N : cnf) :
    N.flatten.length ≤ (EvalCnfCmd.encodeCnf N).length := by
  rw [encodeCnf_length]
  have h : (N.flatten.map (Function.const literal 3)).sum ≤
      (N.flatten.map (fun l => l.2 + 3)).sum :=
    List.sum_le_sum (fun i _ => Nat.le_add_left 3 i.2)
  rw [List.map_const, List.sum_replicate] at h
  exact (Nat.le_mul_of_pos_right _ (show 0 < 3 by decide)).trans
    (h.trans (Nat.le_add_right _ _))

theorem var_lt_encodeCnf_length (N : cnf) (lit : literal) (h : lit ∈ N.flatten) :
    lit.2 < (EvalCnfCmd.encodeCnf N).length := by
  obtain ⟨C, hC, hlit⟩ := List.mem_flatten.mp h
  have h1 : lit.2 + 3 ≤ (EvalCnfCmd.encodeClause C).length := by
    rw [encodeClause_length]
    have hmem : (lit.2 + 3) ∈ C.map (fun l => l.2 + 3) :=
      List.mem_map.mpr ⟨lit, hlit, rfl⟩
    have hle : lit.2 + 3 ≤ (C.map (fun l => l.2 + 3)).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    exact hle.trans (Nat.le_succ _)
  have h2 : (EvalCnfCmd.encodeClause C).length ≤ (EvalCnfCmd.encodeCnf N).length := by
    rw [encodeCnf_length, encodeClause_length, flatten_map_sum]
    have hmem : (C.map (fun l => l.2 + 3)).sum ∈
        N.map (fun C => (C.map (fun l => l.2 + 3)).sum) :=
      List.mem_map.mpr ⟨C, hC, rfl⟩
    have hle : (C.map (fun l => l.2 + 3)).sum ≤
        (N.map (fun C => (C.map (fun l => l.2 + 3)).sum)).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    have hlen : 1 ≤ N.length := List.length_pos_of_mem hC
    exact Nat.add_le_add hle hlen
  have h3 := h1.trans h2
  exact (Nat.add_le_add_left (show (1 : Nat) ≤ 3 by decide) lit.2).trans h3

theorem flatMap_range_extend (f : Nat → List clause) (A : Nat)
    (hA : ∀ v, A ≤ v → f v = []) : ∀ B, A ≤ B →
    (List.range B).flatMap f = (List.range A).flatMap f := by
  intro B
  induction B with
  | zero =>
      intro hB
      have hA0 : A = 0 := by omega
      simp [hA0]
  | succ B ih =>
      intro hB
      by_cases hAB : A = B + 1
      · simp [hAB]
      · have hle : A ≤ B := by omega
        rw [List.range_succ, List.flatMap_append, ih hle]
        simp [hA B hle]

/-- The links phase may range over the input length instead of the
variable bound: both ranges give the same flatMap, since variables outside
either range do not occur. -/
theorem range_bridge (N : cnf) :
    (List.range (EvalCnfCmd.encodeCnf N).length).flatMap
        (fun v => cycleClauses 0 (posOf v N)) =
      (List.range ((varsList N).sum + 1)).flatMap
        (fun v => cycleClauses 0 (posOf v N)) := by
  have hA₁ : ∀ v, (varsList N).sum + 1 ≤ v → cycleClauses 0 (posOf v N) = [] := by
    intro v hv
    have hnil : posOf v N = [] := by
      apply posOf_eq_nil_of_forall
      intro lit hlit
      have hle := var_le_sum N lit hlit
      exact Nat.ne_of_lt (hle.trans_lt (Nat.lt_of_succ_le hv))
    simp [hnil, cycleClauses]
  have hA₂ : ∀ v, (EvalCnfCmd.encodeCnf N).length ≤ v →
      cycleClauses 0 (posOf v N) = [] := by
    intro v hv
    have hnil : posOf v N = [] := by
      apply posOf_eq_nil_of_forall
      intro lit hlit
      have hlt := var_lt_encodeCnf_length N lit hlit
      exact Nat.ne_of_lt (hlt.trans_le hv)
    simp [hnil, cycleClauses]
  have e1 := flatMap_range_extend (fun v => cycleClauses 0 (posOf v N))
    ((varsList N).sum + 1) hA₁
    (max ((varsList N).sum + 1) (EvalCnfCmd.encodeCnf N).length) (by omega)
  have e2 := flatMap_range_extend (fun v => cycleClauses 0 (posOf v N))
    (EvalCnfCmd.encodeCnf N).length hA₂
    (max ((varsList N).sum + 1) (EvalCnfCmd.encodeCnf N).length) (by omega)
  rw [← e2, ← e1]


theorem copy_get_eq (s : State) (dst src : Var) :
    ((Cmd.op (.copy dst src)).eval s).get dst = s.get src := by
  rw [Cmd.eval_op]
  show (s.set dst (s.get src)).get dst = s.get src
  rw [State.get_set_eq]

/-- The whole program computes `occMap` on the nose (at register 0). -/
theorem occCmd_get0 (x : List Bool) :
    (occCmd.eval (CookLevin.Lang.certState x)).get 0 =
      CookLevin.Lang.strBits (occMap x) := by
  have hc0 : (CookLevin.Lang.certState x).get 0 = CookLevin.Lang.strBits x := rfl
  have hcV : (CookLevin.Lang.certState x).get rVARACC = [] := rfl
  have h1IN : ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)).get rIN =
      CookLevin.Lang.strBits x := by
    rw [copy_get_eq]
    exact hc0
  have h1V : ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)).get rVARACC =
      [] := by
    rw [Cmd.eval_get_of_not_writes _ _ _
      (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rIN 0)))]
    exact hcV
  have h2CUR : ((Cmd.op (.copy rCUR rIN)).eval
      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get rCUR =
      CookLevin.Lang.strBits x := by
    rw [copy_get_eq]
    exact h1IN
  have h2IN : ((Cmd.op (.copy rCUR rIN)).eval
      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get rIN =
      CookLevin.Lang.strBits x := by
    rw [Cmd.eval_get_of_not_writes _ _ _
      (by decide : rIN ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
    exact h1IN
  have h2V : ((Cmd.op (.copy rCUR rIN)).eval
      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get rVARACC = [] := by
    rw [Cmd.eval_get_of_not_writes _ _ _
      (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
    exact h1V
  obtain ⟨h3WF, h3IN⟩ := wfProg_eval
    ((Cmd.op (.copy rCUR rIN)).eval
      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))
    (CookLevin.Lang.strBits x) h2CUR h2IN
  have h3V : (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))).get rVARACC = [] := by
    rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rVARACC ∉ Cmd.writes wfProg)]
    exact h2V
  have hfull : occCmd.eval (CookLevin.Lang.certState x) =
      (Cmd.op (.copy 0 rOUT)).eval
        ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) := by
    simp only [occCmd, Cmd.eval_seq]
  cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) with
  | false =>
      rw [hfull, Cmd.eval_ifBit_false _ _ _ _ (by simp [h3WF, hwf])]
      have h8 : ((Cmd.op (.copy 0 rOUT)).eval
          ((Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get 0 =
          [0] := by
        simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
      have hocc : occMap x = [false] := by simp [occMap, hwf]
      rw [h8, hocc]
      rfl
  | true =>
      have h3WF' : (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))).get rWF =
          [1] := by simp [h3WF, hwf]
      have h4CUR : ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rCUR =
          CookLevin.Lang.strBits x := by
        rw [copy_get_eq]
        exact h3IN
      have h4IN : ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rIN =
          CookLevin.Lang.strBits x := by
        rw [Cmd.eval_get_of_not_writes _ _ _
          (by decide : rIN ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
        exact h3IN
      have h4V : ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rVARACC =
          [] := by
        rw [Cmd.eval_get_of_not_writes _ _ _
          (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
        exact h3V
      obtain ⟨h5OUT, h5IN⟩ := renameProg_eval
        ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))
        (CookLevin.Lang.strBits x) (CookLevin.Lang.strBits_bit x) h4CUR h4IN
      have h5V : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get rVARACC =
          [] := by
        rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rVARACC ∉ Cmd.writes renameProg)]
        exact h4V
      have henc : CookLevin.Lang.strBits x =
          EvalCnfCmd.encodeCnf (SATStr.cnfOf x) :=
        (CnfWellFormed.encodeCnf_parseTotal (CookLevin.Lang.strBits x)
          (CookLevin.Lang.strBits_bit x) hwf).symm
      have h5OUT' : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get rOUT =
          EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x)) := by
        rw [h5OUT, henc]
        exact congrArg Prod.fst (renRun_encodeCnf (SATStr.cnfOf x))
      have h5IN' : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get rIN =
          EvalCnfCmd.encodeCnf (SATStr.cnfOf x) := by
        rw [h5IN]; exact henc
      obtain ⟨h6OUT, -⟩ := linksProg_eval
        (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))
        (SATStr.cnfOf x) (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))) 0
        h5IN' h5OUT' h5V
      have h6OUT' : (linksProg.eval (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
          (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))).get rOUT =
          EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x)) := by
        have hoccT : occT 0 (SATStr.cnfOf x) =
            renameCnf 0 (SATStr.cnfOf x) ++
              (List.range ((varsList (SATStr.cnfOf x)).sum + 1)).flatMap
                (fun v => cycleClauses 0 (posOf v (SATStr.cnfOf x))) := rfl
        rw [hoccT, encodeCnf_append, ← range_bridge]
        exact h6OUT
      have h7 : ((Cmd.op (.copy 0 rOUT)).eval
          (linksProg.eval (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))))).get 0 =
          (linksProg.eval (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))).get
            rOUT :=
        copy_get_eq _ _ _
      have hocc : occMap x =
          CookLevin.Lang.boolsOf (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))) := by
        simp [occMap, hwf]
      rw [hfull, Cmd.eval_ifBit_true _ _ _ _ h3WF']
      simp only [Cmd.eval_seq]
      rw [h7, h6OUT', hocc,
        CookLevin.Lang.strBits_boolsOf (EvalCnfCmd.encodeCnf_bit _)]


theorem chainClauses_length (B f : Nat) (js : List Nat) :
    (chainClauses B f js).length = js.length := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      cases js with
      | nil => rfl
      | cons j2 js => simp [chainClauses, ih]

theorem chainClauses_flatten_length (B f : Nat) (js : List Nat) :
    (chainClauses B f js).flatten.length = 2 * js.length := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      cases js with
      | nil => rfl
      | cons j2 js =>
          simp [chainClauses, List.flatten_cons, ih]
          omega

theorem cycleClauses_flatten_length (B : Nat) (js : List Nat) :
    (cycleClauses B js).flatten.length = 2 * (cycleClauses B js).length := by
  cases js with
  | nil => rfl
  | cons j js =>
      have h1 : cycleClauses B (j :: js) = chainClauses B j (j :: js) := rfl
      rw [h1, chainClauses_flatten_length, chainClauses_length]

theorem posOf_length_le (v : Nat) (N : cnf) :
    (posOf v N).length ≤ N.flatten.length := by
  have h1 : (posOf v N).length =
      ((N.flatten.zipIdx).filter (fun p => decide (p.1.2 = v))).length := by
    simp [posOf]
  rw [h1]
  exact (List.length_filter_le _ _).trans_eq List.length_zipIdx

theorem cycleClauses_length_le (B : Nat) (v : Nat) (N : cnf) :
    (cycleClauses B (posOf v N)).length ≤ N.flatten.length := by
  cases hjs : posOf v N with
  | nil => simp [cycleClauses, hjs]
  | cons j js =>
      have h1 : cycleClauses B (j :: js) = chainClauses B j (j :: js) := rfl
      have h2 := posOf_length_le v N
      rw [hjs] at h2
      rw [h1, chainClauses_length]
      exact h2

/-- Every literal in a cycle clause has its variable among the positions. -/
theorem mem_cycleClauses_vars (B : Nat) (js : List Nat) (C : clause) (lit : literal)
    (hC : C ∈ cycleClauses B js) (hlit : lit ∈ C) :
    lit.2 - B ∈ js := by
  cases js with
  | nil => cases hC
  | cons j js =>
      have h1 : cycleClauses B (j :: js) = chainClauses B j (j :: js) := rfl
      rw [h1] at hC
      obtain ⟨p, q, hCeq, hp, hq⟩ := mem_chainClauses hC
      rw [hCeq] at hlit
      simp at hlit
      cases hlit with
      | inl h => rw [h]; simp [hp]
      | inr h => rw [h]; cases hq with
        | inl hq => simp [hq]
        | inr hq => rw [hq]; simp

theorem length_flatten_flatMap (l : List Nat) (f : Nat → cnf) :
    ((l.flatMap f).flatten).length =
      (l.map (fun v => (f v).flatten.length)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatten_append, List.length_append, ih]

theorem occT_flatten_length_le (N : cnf) :
    (occT 0 N).flatten.length ≤
      N.flatten.length + 2 * ((varsList N).sum + 1) * (N.flatten.length + 1) := by
  have hren : (renameCnf 0 N).flatten.length = N.flatten.length := by
    rw [renameCnf, flatten_renameFrom]
    simp
  have hlink : ((List.range ((varsList N).sum + 1)).flatMap
      (fun v => cycleClauses 0 (posOf v N))).flatten.length ≤
      2 * ((varsList N).sum + 1) * (N.flatten.length + 1) := by
    rw [length_flatten_flatMap]
    have h2 : ∀ y ∈ (List.range ((varsList N).sum + 1)).map
        (fun v => (cycleClauses 0 (posOf v N)).flatten.length),
        y ≤ 2 * (N.flatten.length + 1) := by
      intro y hy
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
      rw [cycleClauses_flatten_length]
      have hle := cycleClauses_length_le 0 v N
      omega
    have h3 := List.sum_le_length_nsmul _ (2 * (N.flatten.length + 1)) h2
    rw [List.length_map, List.length_range, smul_eq_mul] at h3
    have h4 : ((varsList N).sum + 1) * (2 * (N.flatten.length + 1)) =
        2 * ((varsList N).sum + 1) * (N.flatten.length + 1) := by ring
    exact h3.trans_eq h4
  have hocc : (occT 0 N).flatten =
      (renameCnf 0 N).flatten ++
        ((List.range ((varsList N).sum + 1)).flatMap
          (fun v => cycleClauses 0 (posOf v N))).flatten := by
    simp [occT, List.flatten_append]
  rw [hocc, List.length_append, hren]
  omega

theorem renameFrom_length (B j : Nat) (N : cnf) :
    (renameFrom B j N).length = N.length := by
  induction N generalizing j with
  | nil => rfl
  | cons C N ih => simp [renameFrom, ih]

theorem occT_length_le (N : cnf) :
    (occT 0 N).length ≤
      (EvalCnfCmd.encodeCnf N).length +
        ((varsList N).sum + 1) * N.flatten.length := by
  have hren : (renameCnf 0 N).length = N.length := renameFrom_length 0 0 N
  have hlink : ((List.range ((varsList N).sum + 1)).flatMap
      (fun v => cycleClauses 0 (posOf v N))).length ≤
      ((varsList N).sum + 1) * N.flatten.length := by
    rw [List.length_flatMap]
    have h2 : ∀ y ∈ (List.range ((varsList N).sum + 1)).map
        (fun v => (cycleClauses 0 (posOf v N)).length),
        y ≤ N.flatten.length := by
      intro y hy
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
      exact cycleClauses_length_le 0 v N
    have h3 := List.sum_le_length_nsmul _ (N.flatten.length) h2
    rwa [List.length_map, List.length_range, smul_eq_mul] at h3
  have hocc : occT 0 N =
      renameCnf 0 N ++
        (List.range ((varsList N).sum + 1)).flatMap
          (fun v => cycleClauses 0 (posOf v N)) := rfl
  rw [hocc, List.length_append, hren]
  have hN : N.length ≤ (EvalCnfCmd.encodeCnf N).length := by
    rw [encodeCnf_length]
    omega
  omega

/-- Every variable of the transformed CNF is below the literal count. -/
theorem occT_var_le (N : cnf) (lit : literal) (h : lit ∈ (occT 0 N).flatten) :
    lit.2 ≤ N.flatten.length := by
  show (lit.2 : Nat) ≤ N.flatten.length
  have hocc : (occT 0 N).flatten =
      (renameCnf 0 N).flatten ++
        ((List.range ((varsList N).sum + 1)).flatMap
          (fun v => cycleClauses 0 (posOf v N))).flatten := by
    simp [occT, List.flatten_append]
  rw [hocc, List.mem_append] at h
  cases h with
  | inl h =>
      rw [renameCnf, flatten_renameFrom] at h
      obtain ⟨⟨l, j⟩, hp, rfl⟩ := List.mem_map.mp h
      have hlt : j < N.flatten.length := by
        have e := List.mem_zipIdx hp
        omega
      show 0 + j ≤ N.flatten.length
      omega
  | inr h =>
      obtain ⟨C, hC, hlit⟩ := List.mem_flatten.mp h
      obtain ⟨v, hv, hCC⟩ := List.mem_flatMap.mp hC
      have hpos : lit.2 ∈ posOf v N := by
        have := mem_cycleClauses_vars 0 (posOf v N) C lit hCC hlit
        simpa using this
      have hlt : (lit.2 : Nat) < N.flatten.length := by
        obtain ⟨l, hl, -⟩ := mem_posOf.mp hpos
        have e := List.mem_zipIdx hl
        rw [Nat.zero_add] at e
        exact e.2.1
      exact Nat.le_of_lt hlt

/-- A polynomial bound on the output length (well-formed case). -/
theorem occMap_length_le (x : List Bool)
    (hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true) :
    (occMap x).length ≤ 20 * (x.length + 1) ^ 4 + 1 := by
  have hN : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) = CookLevin.Lang.strBits x :=
    CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit x) hwf
  have hL : (SATStr.cnfOf x).flatten.length ≤ x.length := by
    have h1 := flatten_length_le_encodeCnf (SATStr.cnfOf x)
    rw [hN, CookLevin.Lang.strBits_length] at h1
    exact h1
  have hA : ((varsList (SATStr.cnfOf x)).sum : Nat) ≤ x.length * x.length := by
    have h2 : (varsList (SATStr.cnfOf x)).sum ≤
        (SATStr.cnfOf x).flatten.length * x.length := by
      have h3 : ((SATStr.cnfOf x).flatten.map (fun l => l.2)).sum ≤
          ((SATStr.cnfOf x).flatten.map (fun l => l.2)).length • x.length := by
        apply List.sum_le_length_nsmul
        intro y hy
        obtain ⟨lit, hlit, rfl⟩ := List.mem_map.mp hy
        have hlt := var_lt_encodeCnf_length (SATStr.cnfOf x) lit hlit
        rw [hN, CookLevin.Lang.strBits_length] at hlt
        show (lit.2 : Nat) ≤ x.length
        exact Nat.le_of_lt hlt
      rw [List.length_map, smul_eq_mul] at h3
      exact h3
    have h4 : ((varsList (SATStr.cnfOf x)).sum : Nat) ≤
        (SATStr.cnfOf x).flatten.length * x.length := h2
    have h5 : (SATStr.cnfOf x).flatten.length * x.length ≤ x.length * x.length :=
      Nat.mul_le_mul_right _ hL
    exact h4.trans h5
  have hocc : occMap x =
      CookLevin.Lang.boolsOf (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))) := by
    simp [occMap, hwf]
  rw [hocc]
  simp only [CookLevin.Lang.boolsOf, List.length_map]
  rw [encodeCnf_length]
  have hF := occT_flatten_length_le (SATStr.cnfOf x)
  have hT := occT_length_le (SATStr.cnfOf x)
  rw [hN, CookLevin.Lang.strBits_length] at hT
  have hsum : ((occT 0 (SATStr.cnfOf x)).flatten.map (fun l => l.2 + 3)).sum ≤
      (occT 0 (SATStr.cnfOf x)).flatten.length *
        ((SATStr.cnfOf x).flatten.length + 3) := by
    have h3 : ((occT 0 (SATStr.cnfOf x)).flatten.map (fun l => l.2 + 3)).sum ≤
        ((occT 0 (SATStr.cnfOf x)).flatten.map (fun l => l.2 + 3)).length •
          ((SATStr.cnfOf x).flatten.length + 3) := by
      apply List.sum_le_length_nsmul
      intro y hy
      obtain ⟨lit, hlit, rfl⟩ := List.mem_map.mp hy
      have hle : (lit.2 : Nat) ≤ (SATStr.cnfOf x).flatten.length :=
        occT_var_le (SATStr.cnfOf x) lit hlit
      show (lit.2 : Nat) + 3 ≤ (SATStr.cnfOf x).flatten.length + 3
      exact Nat.add_le_add_right hle 3
    rwa [List.length_map, smul_eq_mul] at h3
  have hA' : (varsList (SATStr.cnfOf x)).sum + 1 ≤ x.length * x.length + 1 := by
    omega
  have hprod1 : ((varsList (SATStr.cnfOf x)).sum + 1) *
        ((SATStr.cnfOf x).flatten.length + 1) ≤
      (x.length * x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul hA' (by omega)
  have hF2 : (occT 0 (SATStr.cnfOf x)).flatten.length ≤
      x.length + 2 * ((x.length * x.length + 1) * (x.length + 1)) := by
    have h := hF
    rw [show 2 * ((varsList (SATStr.cnfOf x)).sum + 1) *
          ((SATStr.cnfOf x).flatten.length + 1) =
        2 * (((varsList (SATStr.cnfOf x)).sum + 1) *
          ((SATStr.cnfOf x).flatten.length + 1)) from by ring] at h
    exact h.trans (by omega)
  have hT2 : (occT 0 (SATStr.cnfOf x)).length ≤ (x.length + 1) ^ 4 := by
    have hprod : ((varsList (SATStr.cnfOf x)).sum + 1) *
          (SATStr.cnfOf x).flatten.length + x.length ≤ (x.length + 1) ^ 4 := by
      have e1 : ((varsList (SATStr.cnfOf x)).sum + 1) *
            (SATStr.cnfOf x).flatten.length ≤
          (x.length * x.length + 1) * x.length :=
        Nat.mul_le_mul hA' hL
      have e2 : (x.length * x.length + 1) * x.length + x.length ≤
          (x.length + 1) ^ 4 := by
        nlinarith [Nat.zero_le x.length, sq_nonneg (x.length * x.length - x.length)]
      exact (Nat.add_le_add_right e1 x.length).trans e2
    exact hT.trans ((Nat.add_comm _ _).le.trans hprod)
  have hs2 : ((occT 0 (SATStr.cnfOf x)).flatten.map (fun l => l.2 + 3)).sum ≤
      19 * (x.length + 1) ^ 4 := by
    have e1 : ((occT 0 (SATStr.cnfOf x)).flatten.map (fun l => l.2 + 3)).sum ≤
        (x.length + 2 * ((x.length * x.length + 1) * (x.length + 1))) *
          (x.length + 3) :=
      hsum.trans (Nat.mul_le_mul hF2 (by omega))
    have e2 : (x.length + 2 * ((x.length * x.length + 1) * (x.length + 1))) *
          (x.length + 3) ≤ 19 * (x.length + 1) ^ 4 := by
      nlinarith [Nat.zero_le x.length, sq_nonneg (x.length * x.length - x.length),
        sq_nonneg (x.length - 1)]
    exact e1.trans e2
  omega


/-- `renStep` only ever appends to the output component. -/
theorem renStep_out_append (st : List Nat × Nat × Bool × Bool) (c : Nat) :
    ∃ t, (renStep st c).1 = st.1 ++ t := by
  obtain ⟨out, j, sa, sb⟩ := st
  cases sa with
  | false =>
      by_cases hc : c = 1
      · refine ⟨[1], ?_⟩
        simp [renStep, hc]
      · refine ⟨[0], ?_⟩
        simp [renStep, hc]
  | true =>
      cases sb with
      | false =>
          refine ⟨[c], ?_⟩
          simp [renStep]
      | true =>
          by_cases hc : c = 1
          · refine ⟨[], ?_⟩
            simp [renStep, hc]
          · refine ⟨List.replicate j 1 ++ [0], ?_⟩
            simp [renStep, hc, List.append_assoc]

/-- The renaming output after a prefix of the stream is a prefix of the
full output. -/
theorem renRun_take_out_prefix (l : List Nat) (i : Nat) :
    ∃ t, (renRun l).1 = (renRun (l.take i)).1 ++ t := by
  have h : ∀ (b a : List Nat) (st : List Nat × Nat × Bool × Bool),
      ∃ t, ((a ++ b).foldl renStep st).1 = (a.foldl renStep st).1 ++ t := by
    intro b
    induction b with
    | nil => intro a st; exact ⟨[], by simp⟩
    | cons c b ih =>
        intro a st
        have e1 : a ++ (c :: b) = (a ++ [c]) ++ b := by simp [List.append_assoc]
        rw [e1]
        obtain ⟨t, ht⟩ := ih (a ++ [c]) st
        obtain ⟨t', ht'⟩ := renStep_out_append (a.foldl renStep st) c
        have e2 : ((a ++ [c]).foldl renStep st) = renStep (a.foldl renStep st) c := by
          rw [List.foldl_append]; rfl
        refine ⟨t' ++ t, ?_⟩
        rw [ht, e2, ht', List.append_assoc]
  have h2 := h (l.drop i) (l.take i) ([], 0, false, false)
  rw [List.take_append_drop] at h2
  exact h2

/-- The occurrence counter never exceeds the output length. -/
theorem renRun_j_le_out (l : List Nat) :
    (renRun l).2.1 ≤ (renRun l).1.length := by
  have h : ∀ (l : List Nat) (st : List Nat × Nat × Bool × Bool),
      st.2.1 ≤ st.1.length →
      (l.foldl renStep st).2.1 ≤ (l.foldl renStep st).1.length := by
    intro l st hst
    induction l generalizing st with
    | nil => exact hst
    | cons c l ih =>
        rw [List.foldl_cons]
        apply ih
        obtain ⟨out, j, sa, sb⟩ := st
        have hst' : j ≤ out.length := hst
        cases sa with
        | false =>
            by_cases hc : c = 1
            · have e : renStep (out, j, false, sb) c = (out ++ [1], j, true, false) := by
                simp [renStep, hc]
              rw [e]
              show j ≤ (out ++ [1]).length
              simp [List.length_append]
              omega
            · have e : renStep (out, j, false, sb) c = (out ++ [0], j, false, sb) := by
                simp [renStep, hc]
              rw [e]
              show j ≤ (out ++ [0]).length
              simp [List.length_append]
              omega
        | true =>
            cases sb with
            | false =>
                have e : renStep (out, j, true, false) c =
                    (out ++ [c], j, true, true) := by
                  simp [renStep]
                rw [e]
                show j ≤ (out ++ [c]).length
                simp [List.length_append]
                omega
            | true =>
                by_cases hc : c = 1
                · have e : renStep (out, j, true, true) c = (out, j, true, true) := by
                    simp [renStep, hc]
                  rw [e]
                  exact hst
                · have e : renStep (out, j, true, true) c =
                      (out ++ List.replicate j 1 ++ [0], j + 1, false, false) := by
                    simp [renStep, hc]
                  rw [e]
                  show j + 1 ≤ (out ++ List.replicate j 1 ++ [0]).length
                  simp only [List.length_append, List.length_replicate, List.length_cons,
                    List.length_nil]
                  exact Nat.le_add_left _ _
  exact h l ([], 0, false, false) (by simp)

/-- `linkStep` only ever appends to the output component. -/
theorem linkStep_out_append (v : Nat)
    (st : List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool) (c : Nat) :
    ∃ t, (linkStep v st c).1 = st.1 ++ t := by
  obtain ⟨out, k, prev, first, has, vacc, sa, sb⟩ := st
  cases sa with
  | false =>
      by_cases hc : c = 1
      · refine ⟨[], ?_⟩
        simp [linkStep, hc]
      · refine ⟨[], ?_⟩
        simp [linkStep, hc]
  | true =>
      cases sb with
      | false =>
          refine ⟨[], ?_⟩
          simp [linkStep]
      | true =>
          by_cases hc : c = 1
          · refine ⟨[], ?_⟩
            simp [linkStep, hc]
          · by_cases hv : vacc = v
            · cases has
              · refine ⟨[], ?_⟩
                simp [linkStep, hc, hv]
              · refine ⟨EvalCnfCmd.encodeClause [(false, prev), (true, k)], ?_⟩
                simp [linkStep, hc, hv]
            · refine ⟨[], ?_⟩
              simp [linkStep, hc, hv]

/-- The pass output after a prefix of the stream is a prefix of the
full pass output. -/
theorem linkRunFrom_take_out_prefix (v : Nat) (out : List Nat) (vacc : Nat)
    (l : List Nat) (i : Nat) :
    ∃ t, (linkRunFrom v out vacc l).1 =
      (linkRunFrom v out vacc (l.take i)).1 ++ t := by
  have h : ∀ (b a : List Nat)
      (st : List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool),
      ∃ t, ((a ++ b).foldl (linkStep v) st).1 =
        (a.foldl (linkStep v) st).1 ++ t := by
    intro b
    induction b with
    | nil => intro a st; exact ⟨[], by simp⟩
    | cons c b ih =>
        intro a st
        have e1 : a ++ (c :: b) = (a ++ [c]) ++ b := by simp [List.append_assoc]
        rw [e1]
        obtain ⟨t, ht⟩ := ih (a ++ [c]) st
        obtain ⟨t', ht'⟩ := linkStep_out_append v (a.foldl (linkStep v) st) c
        have e2 : ((a ++ [c]).foldl (linkStep v) st) =
            linkStep v (a.foldl (linkStep v) st) c := by
          rw [List.foldl_append]; rfl
        refine ⟨t' ++ t, ?_⟩
        rw [ht, e2, ht', List.append_assoc]
  have h2 := h (l.drop i) (l.take i) (out, 0, 0, 0, false, vacc, false, false)
  rw [List.take_append_drop] at h2
  exact h2

/-- Counting invariants for the pass scan: the occurrence counter, the
previous/first positions and the variable accumulator stay small. -/
theorem linkRunFrom_counts (v : Nat) (out : List Nat) (vacc : Nat) (l : List Nat) :
    (linkRunFrom v out vacc l).2.1 ≤ l.length ∧
    (linkRunFrom v out vacc l).2.2.1 ≤ l.length ∧
    (linkRunFrom v out vacc l).2.2.2.1 ≤ l.length ∧
    (linkRunFrom v out vacc l).2.2.2.2.2.1 ≤ vacc + l.length := by
  have h : ∀ (l : List Nat)
      (st : List Nat × Nat × Nat × Nat × Bool × Nat × Bool × Bool) (B : Nat),
      st.2.1 ≤ B → st.2.2.1 ≤ st.2.1 → st.2.2.2.1 ≤ st.2.1 →
      st.2.2.2.2.2.1 ≤ vacc + B →
      (l.foldl (linkStep v) st).2.1 ≤ B + l.length ∧
      (l.foldl (linkStep v) st).2.2.1 ≤ (l.foldl (linkStep v) st).2.1 ∧
      (l.foldl (linkStep v) st).2.2.2.1 ≤ (l.foldl (linkStep v) st).2.1 ∧
      (l.foldl (linkStep v) st).2.2.2.2.2.1 ≤ vacc + (B + l.length) := by
    intro l st B hk hp hf hv
    induction l generalizing st B with
    | nil => exact ⟨hk, hp, hf, hv⟩
    | cons c l ih =>
        rw [List.foldl_cons]
        obtain ⟨out, k, prev, first, has, vaccs, sa, sb⟩ := st
        have hk' : k ≤ B := hk
        have hp' : prev ≤ k := hp
        have hf' : first ≤ k := hf
        have hv' : vaccs ≤ vacc + B := hv
        cases sa with
        | false =>
            by_cases hc : c = 1
            · have e : linkStep v (out, k, prev, first, has, vaccs, false, sb) c =
                  (out, k, prev, first, has, vaccs, true, false) := by
                simp [linkStep, hc]
              rw [e]
              obtain ⟨a1, a2, a3, a4⟩ := ih (out, k, prev, first, has, vaccs, true,
                false) (B + 1) (by show k ≤ B + 1; omega) (by show prev ≤ k; omega)
                (by show first ≤ k; omega) (by show vaccs ≤ vacc + (B + 1); omega)
              refine ⟨?_, a2, a3, ?_⟩
              · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs, true,
                  false)).2.1 ≤ B + (l.length + 1)
                omega
              · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs, true,
                  false)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                omega
            · have e : linkStep v (out, k, prev, first, has, vaccs, false, sb) c =
                  (out, k, prev, first, has, vaccs, false, sb) := by
                simp [linkStep, hc]
              rw [e]
              obtain ⟨a1, a2, a3, a4⟩ := ih (out, k, prev, first, has, vaccs, false,
                sb) (B + 1) (by show k ≤ B + 1; omega) (by show prev ≤ k; omega)
                (by show first ≤ k; omega) (by show vaccs ≤ vacc + (B + 1); omega)
              refine ⟨?_, a2, a3, ?_⟩
              · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs, false,
                  sb)).2.1 ≤ B + (l.length + 1)
                omega
              · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs, false,
                  sb)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                omega
        | true =>
            cases sb with
            | false =>
                have e : linkStep v (out, k, prev, first, has, vaccs, true, false) c =
                    (out, k, prev, first, has, 0, true, true) := by
                  simp [linkStep]
                rw [e]
                obtain ⟨a1, a2, a3, a4⟩ := ih (out, k, prev, first, has, 0, true,
                  true) (B + 1) (by show k ≤ B + 1; omega) (by show prev ≤ k; omega)
                  (by show first ≤ k; omega) (by show 0 ≤ vacc + (B + 1); omega)
                refine ⟨?_, a2, a3, ?_⟩
                · show (l.foldl (linkStep v) (out, k, prev, first, has, 0, true,
                    true)).2.1 ≤ B + (l.length + 1)
                  omega
                · show (l.foldl (linkStep v) (out, k, prev, first, has, 0, true,
                    true)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                  omega
            | true =>
                by_cases hc : c = 1
                · have e : linkStep v (out, k, prev, first, has, vaccs, true, true) c =
                      (out, k, prev, first, has, vaccs + 1, true, true) := by
                    simp [linkStep, hc]
                  rw [e]
                  obtain ⟨a1, a2, a3, a4⟩ := ih (out, k, prev, first, has, vaccs + 1,
                    true, true) (B + 1) (by show k ≤ B + 1; omega)
                    (by show prev ≤ k; omega) (by show first ≤ k; omega)
                    (by show vaccs + 1 ≤ vacc + (B + 1); omega)
                  refine ⟨?_, a2, a3, ?_⟩
                  · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs + 1,
                      true, true)).2.1 ≤ B + (l.length + 1)
                    omega
                  · show (l.foldl (linkStep v) (out, k, prev, first, has, vaccs + 1,
                      true, true)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                    omega
                · by_cases hvv : vaccs = v
                  · cases has
                    · have e : linkStep v (out, k, prev, first, false, vaccs, true,
                          true) c = (out, k + 1, k, k, true, vaccs, false, false) := by
                        simp [linkStep, hc, hvv]
                      rw [e]
                      obtain ⟨a1, a2, a3, a4⟩ := ih (out, k + 1, k, k, true, vaccs,
                        false, false) (B + 1) (by show k + 1 ≤ B + 1; omega)
                        (by show k ≤ k + 1; omega) (by show k ≤ k + 1; omega)
                        (by show vaccs ≤ vacc + (B + 1); omega)
                      refine ⟨?_, a2, a3, ?_⟩
                      · show (l.foldl (linkStep v) (out, k + 1, k, k, true, vaccs,
                          false, false)).2.1 ≤ B + (l.length + 1)
                        omega
                      · show (l.foldl (linkStep v) (out, k + 1, k, k, true, vaccs,
                          false, false)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                        omega
                    · have e : linkStep v (out, k, prev, first, true, vaccs, true,
                          true) c =
                          (out ++ EvalCnfCmd.encodeClause [(false, prev), (true, k)],
                            k + 1, k, first, true, vaccs, false, false) := by
                        simp [linkStep, hc, hvv]
                      rw [e]
                      obtain ⟨a1, a2, a3, a4⟩ := ih (out ++ EvalCnfCmd.encodeClause
                        [(false, prev), (true, k)], k + 1, k, first, true, vaccs, false,
                        false) (B + 1) (by show k + 1 ≤ B + 1; omega)
                        (by show k ≤ k + 1; omega) (by show first ≤ k + 1; omega)
                        (by show vaccs ≤ vacc + (B + 1); omega)
                      refine ⟨?_, a2, a3, ?_⟩
                      · show (l.foldl (linkStep v) (out ++ EvalCnfCmd.encodeClause
                          [(false, prev), (true, k)], k + 1, k, first, true, vaccs,
                          false, false)).2.1 ≤ B + (l.length + 1)
                        omega
                      · show (l.foldl (linkStep v) (out ++ EvalCnfCmd.encodeClause
                          [(false, prev), (true, k)], k + 1, k, first, true, vaccs,
                          false, false)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                        omega
                  · have e : linkStep v (out, k, prev, first, has, vaccs, true, true)
                        c = (out, k + 1, prev, first, has, vaccs, false, false) := by
                      simp [linkStep, hc, hvv]
                    rw [e]
                    obtain ⟨a1, a2, a3, a4⟩ := ih (out, k + 1, prev, first, has, vaccs,
                      false, false) (B + 1) (by show k + 1 ≤ B + 1; omega)
                      (by show prev ≤ k + 1; omega) (by show first ≤ k + 1; omega)
                      (by show vaccs ≤ vacc + (B + 1); omega)
                    refine ⟨?_, a2, a3, ?_⟩
                    · show (l.foldl (linkStep v) (out, k + 1, prev, first, has, vaccs,
                        false, false)).2.1 ≤ B + (l.length + 1)
                      omega
                    · show (l.foldl (linkStep v) (out, k + 1, prev, first, has, vaccs,
                        false, false)).2.2.2.2.2.1 ≤ vacc + (B + (l.length + 1))
                      omega
  have h2 := h l (out, 0, 0, 0, false, vacc, false, false) 0 (by simp) (by simp)
    (by simp) (by simp)
  simp only [linkRunFrom, Nat.zero_add] at h2
  obtain ⟨a1, a2, a3, a4⟩ := h2
  exact ⟨a1, a2.trans a1, a3.trans a1, a4⟩


set_option maxRecDepth 8192 in
/-- Cost of the well-formedness scan loop. -/
theorem wfLoop_cost (l : List Nat) (s : State)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0]) :
    (Cmd.forBnd rIDX rIN wfBody).cost s ≤
      1 + l.length * (wfBody.flatK * (l.length + 1)) + l.length * l.length := by
  have hreads : wfBody.costReads = [rCUR] := by
    simp only [wfBody, setZero, setOne, nop, Cmd.costReads, Op.costReads,
      List.nil_append, List.append_nil, List.cons_append]
  rw [← hIN]
  refine Cmd.cost_forBnd_flat_le rIDX rIN wfBody (by decide) s (s.get rIN).length
    (fun i st => st.get rCUR = l.drop i ∧
      st.get rSA = [if (CnfWellFormed.scanRun (l.take i)).1 then 1 else 0] ∧
      st.get rSB = [if (CnfWellFormed.scanRun (l.take i)).2.1 then 1 else 0])
    (by simp [hCUR, hSA, hSB, CnfWellFormed.scanRun]) (fun i st hi hM => ?_)
    (fun i st hi hM r hr => ?_)
  · obtain ⟨hCURi, hSAi, hSBi⟩ := hM
    have hi' : i < l.length := hIN ▸ hi
    rw [List.drop_eq_getElem_cons hi'] at hCURi
    have hCUR' : (st.set rIDX (List.replicate i 1)).get rCUR =
        l[i] :: l.drop (i + 1) := by simp [State.get_set_ne, hCURi]
    have hSA' : (st.set rIDX (List.replicate i 1)).get rSA =
        [if (CnfWellFormed.scanRun (l.take i)).1 then 1 else 0] := by
      simp [State.get_set_ne, hSAi]
    have hSB' : (st.set rIDX (List.replicate i 1)).get rSB =
        [if (CnfWellFormed.scanRun (l.take i)).2.1 then 1 else 0] := by
      simp [State.get_set_ne, hSBi]
    obtain ⟨hCURn, hSAn, hSBn⟩ := wfBody_eval (st.set rIDX (List.replicate i 1))
      (CnfWellFormed.scanRun (l.take i)).1 (CnfWellFormed.scanRun (l.take i)).2.1
      l[i] (l.drop (i + 1)) hSA' hSB' hCUR'
    refine ⟨hCURn, ?_, ?_⟩
    · rw [hSAn, scanRun_take_succ_fst l i hi']
    · rw [hSBn, scanRun_take_succ_snd l i hi']
  · rw [hreads] at hr
    simp at hr
    subst hr
    have h1 : (st.set rIDX (List.replicate i 1)).get rCUR = l.drop i := by
      rw [State.get_set_ne _ _ _ _ (by decide : rCUR ≠ rIDX)]
      exact hM.1
    rw [h1, hIN, List.length_drop]
    exact Nat.sub_le _ _

/-- Cost of the well-formedness phase. -/
theorem wfProg_cost (l : List Nat) (s : State)
    (hCUR : s.get rCUR = l) (hIN : s.get rIN = l) :
    wfProg.cost s ≤ (setZero rSA).flatK * (l.length + 1) +
      (setZero rSB).flatK * (l.length + 1) +
      (1 + l.length * (wfBody.flatK * (l.length + 1)) + l.length * l.length) +
      (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
        Cmd.ifBit rSB (setZero rWF) nop).flatK * (l.length + 1) + 3 := by
  have gSA : ((setZero rSB).eval ((setZero rSA).eval s)).get rSA = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSB : ((setZero rSB).eval ((setZero rSA).eval s)).get rSB = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gCUR : ((setZero rSB).eval ((setZero rSA).eval s)).get rCUR = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hCUR]
  have gIN : ((setZero rSB).eval ((setZero rSA).eval s)).get rIN = l := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  have hA1 : (setZero rSA).cost s ≤ (setZero rSA).flatK * (l.length + 1) :=
    (Cmd.cost_le_flat _ (by simp [setZero, Cmd.loopFree]) s l.length
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hA2 : (setZero rSB).cost ((setZero rSA).eval s) ≤
      (setZero rSB).flatK * (l.length + 1) :=
    (Cmd.cost_le_flat _ (by simp [setZero, Cmd.loopFree]) _ l.length
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hB : (Cmd.forBnd rIDX rIN wfBody).cost
      ((setZero rSB).eval ((setZero rSA).eval s)) ≤
      1 + l.length * (wfBody.flatK * (l.length + 1)) + l.length * l.length :=
    wfLoop_cost l _ gCUR gIN gSA gSB
  have hC : (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
      Cmd.ifBit rSB (setZero rWF) nop).cost
      ((Cmd.forBnd rIDX rIN wfBody).eval ((setZero rSB).eval ((setZero rSA).eval s))) ≤
      (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
        Cmd.ifBit rSB (setZero rWF) nop).flatK * (l.length + 1) :=
    (Cmd.cost_le_flat _ (by simp [setOne, setZero, nop, Cmd.loopFree]) _ l.length
      (fun r hr => by
        simp [setOne, setZero, nop, Cmd.costReads, Op.costReads] at hr)).1
  have e : wfProg = (setZero rSA ;; setZero rSB ;; (Cmd.forBnd rIDX rIN wfBody) ;;
      (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
        Cmd.ifBit rSB (setZero rWF) nop)) := rfl
  rw [e, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  omega

set_option maxRecDepth 8192 in
/-- Cost of the renaming loop. -/
theorem renameLoop_cost (N : cnf) (s : State)
    (hCUR : s.get rCUR = EvalCnfCmd.encodeCnf N)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N)
    (hOUT : s.get rOUT = []) (hJ : s.get rJ = List.replicate 0 1)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0]) :
    (Cmd.forBnd rIDX2 rIN renameBody).cost s ≤
      1 + (s.get rIN).length *
          (renameBody.flatK *
            ((s.get rIN).length +
              (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1)) +
        (s.get rIN).length * (s.get rIN).length := by
  have hlen : (s.get rIN).length = (EvalCnfCmd.encodeCnf N).length := by rw [hIN]
  have hl' : ∀ c ∈ EvalCnfCmd.encodeCnf N, c ≤ 1 := EvalCnfCmd.encodeCnf_bit N
  have hreads : ∀ r ∈ renameBody.costReads, r = rCUR ∨ r = rOUT ∨ r = rJ := by
    have heq : renameBody.costReads = [rCUR, rOUT, rJ] := by decide
    intro r hr
    rw [heq] at hr
    simp at hr
    tauto
  refine Cmd.cost_forBnd_flat_le rIDX2 rIN renameBody (by decide) s
    ((s.get rIN).length +
      (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length)
    (fun i st => st.get rCUR = (EvalCnfCmd.encodeCnf N).drop i ∧
      st.get rOUT = (renRun ((EvalCnfCmd.encodeCnf N).take i)).1 ∧
      st.get rJ = List.replicate (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.1 1 ∧
      st.get rSA = [if (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.1 then 1 else 0] ∧
      st.get rSB = [if (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.2 then 1 else 0] ∧
      ((renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.1 = false →
        (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.2 = false) ∧
      st.get rIN = EvalCnfCmd.encodeCnf N)
    (by simp [renRun, hCUR, hOUT, hJ, hSA, hSB, hIN]) (fun i st hi hM => ?_)
    (fun i st hi hM r hr => ?_)
  · obtain ⟨hCURi, hOUTi, hJi, hSAi, hSBi, himpi, hINi⟩ := hM
    have hi' : i < (EvalCnfCmd.encodeCnf N).length := hIN ▸ hi
    rw [List.drop_eq_getElem_cons hi'] at hCURi
    have hcell : (EvalCnfCmd.encodeCnf N)[i] ≤ 1 := hl' _ (List.getElem_mem hi')
    have hCUR' : (st.set rIDX2 (List.replicate i 1)).get rCUR =
        (EvalCnfCmd.encodeCnf N)[i] :: (EvalCnfCmd.encodeCnf N).drop (i + 1) := by
      simp [State.get_set_ne, hCURi]
    have hOUT' : (st.set rIDX2 (List.replicate i 1)).get rOUT =
        (renRun ((EvalCnfCmd.encodeCnf N).take i)).1 := by
      simp [State.get_set_ne, hOUTi]
    have hJ' : (st.set rIDX2 (List.replicate i 1)).get rJ =
        List.replicate (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.1 1 := by
      simp [State.get_set_ne, hJi]
    have hSA' : (st.set rIDX2 (List.replicate i 1)).get rSA =
        [if (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.1 then 1 else 0] := by
      simp [State.get_set_ne, hSAi]
    have hSB' : (st.set rIDX2 (List.replicate i 1)).get rSB =
        [if (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.2 then 1 else 0] := by
      simp [State.get_set_ne, hSBi]
    have hIN' : (st.set rIDX2 (List.replicate i 1)).get rIN =
        EvalCnfCmd.encodeCnf N := by simp [State.get_set_ne, hINi]
    obtain ⟨hCURn, hOUTn, hJn, hSAn, hSBn⟩ := renameBody_eval
      (st.set rIDX2 (List.replicate i 1))
      (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.1
      (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.2.2
      (EvalCnfCmd.encodeCnf N)[i] ((EvalCnfCmd.encodeCnf N).drop (i + 1))
      (renRun ((EvalCnfCmd.encodeCnf N).take i)).1
      (renRun ((EvalCnfCmd.encodeCnf N).take i)).2.1
      hcell himpi hSA' hSB' hCUR' hOUT' hJ'
    refine ⟨hCURn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [renRun_take_succ _ i hi']; exact hOUTn
    · rw [renRun_take_succ _ i hi']; exact hJn
    · rw [renRun_take_succ _ i hi']; exact hSAn
    · rw [renRun_take_succ _ i hi']; exact hSBn
    · rw [renRun_take_succ _ i hi']; exact renStep_himp _ _ himpi
    · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes renameBody)]
      exact hIN'
  · have hset : ∀ (q : Var), q ≠ rIDX2 →
        (st.set rIDX2 (List.replicate i 1)).get q = st.get q :=
      fun q hq => State.get_set_ne _ _ _ _ hq
    rcases hreads r hr with rfl | rfl | rfl
    · rw [hset rCUR (by decide), hM.1, List.length_drop]
      omega
    · rw [hset rOUT (by decide), hM.2.1]
      obtain ⟨t, ht⟩ := renRun_take_out_prefix (EvalCnfCmd.encodeCnf N) i
      have hlen : (renRun (EvalCnfCmd.encodeCnf N)).1.length =
          (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length := by
        rw [renRun_encodeCnf]
      have h2 : (renRun ((EvalCnfCmd.encodeCnf N).take i)).1.length ≤
          (renRun (EvalCnfCmd.encodeCnf N)).1.length := by
        rw [ht, List.length_append]
        exact Nat.le_add_right _ _
      omega
    · rw [hset rJ (by decide), hM.2.2.1]
      simp only [List.length_replicate]
      have hle := renRun_j_le_out ((EvalCnfCmd.encodeCnf N).take i)
      obtain ⟨t, ht⟩ := renRun_take_out_prefix (EvalCnfCmd.encodeCnf N) i
      have hlen : (renRun (EvalCnfCmd.encodeCnf N)).1.length =
          (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length := by
        rw [renRun_encodeCnf]
      have h2 : (renRun ((EvalCnfCmd.encodeCnf N).take i)).1.length ≤
          (renRun (EvalCnfCmd.encodeCnf N)).1.length := by
        rw [ht, List.length_append]
        exact Nat.le_add_right _ _
      omega

/-- Cost of the renaming phase. -/
theorem renameProg_cost (N : cnf) (s : State)
    (hCUR : s.get rCUR = EvalCnfCmd.encodeCnf N)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N) :
    renameProg.cost s ≤
      (Cmd.op (.clear rJ)).flatK *
          ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) +
        (Cmd.op (.clear rOUT)).flatK *
          ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) +
        (setZero rSA).flatK *
          ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) +
        (setZero rSB).flatK *
          ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) +
        (1 + (EvalCnfCmd.encodeCnf N).length *
            (renameBody.flatK *
              ((EvalCnfCmd.encodeCnf N).length +
                (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1)) +
          (EvalCnfCmd.encodeCnf N).length * (EvalCnfCmd.encodeCnf N).length) + 4 := by
  have gJ : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rJ =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gOUT : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rOUT = [] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSA : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rSA = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSB : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rSB = [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gCUR : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rCUR =
      EvalCnfCmd.encodeCnf N := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hCUR]
  have gIN : ((setZero rSB).eval ((setZero rSA).eval
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)))).get rIN =
      EvalCnfCmd.encodeCnf N := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  have hloop := renameLoop_cost N _ gCUR gIN gOUT gJ gSA gSB
  rw [gIN] at hloop
  have hf1 : (Cmd.op (.clear rJ)).cost s ≤
      (Cmd.op (.clear rJ)).flatK *
        ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) :=
    (Cmd.cost_le_flat _ (by simp [Cmd.loopFree]) s _
      (fun r hr => by simp [Cmd.costReads, Op.costReads] at hr)).1
  have hf2 : (Cmd.op (.clear rOUT)).cost ((Cmd.op (.clear rJ)).eval s) ≤
      (Cmd.op (.clear rOUT)).flatK *
        ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) :=
    (Cmd.cost_le_flat _ (by simp [Cmd.loopFree]) _ _
      (fun r hr => by simp [Cmd.costReads, Op.costReads] at hr)).1
  have hf3 : (setZero rSA).cost
      ((Cmd.op (.clear rOUT)).eval ((Cmd.op (.clear rJ)).eval s)) ≤
      (setZero rSA).flatK *
        ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) :=
    (Cmd.cost_le_flat _ (by simp [setZero, Cmd.loopFree]) _ _
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hf4 : (setZero rSB).cost
      ((setZero rSA).eval ((Cmd.op (.clear rOUT)).eval
        ((Cmd.op (.clear rJ)).eval s))) ≤
      (setZero rSB).flatK *
        ((EvalCnfCmd.encodeCnf (renameCnf 0 N)).length + 1) :=
    (Cmd.cost_le_flat _ (by simp [setZero, Cmd.loopFree]) _ _
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have e : renameProg = (Cmd.op (.clear rJ) ;; Cmd.op (.clear rOUT) ;; setZero rSA ;;
      setZero rSB ;; Cmd.forBnd rIDX2 rIN renameBody) := rfl
  rw [e, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  omega


/-- One variable's cycle encoding is no longer than the whole transformed
encoding. -/
theorem encodeCnf_cycleClauses_le (v : Nat) (N : cnf) :
    (EvalCnfCmd.encodeCnf (cycleClauses 0 (posOf v N))).length ≤
      (EvalCnfCmd.encodeCnf (occT 0 N)).length := by
  by_cases hv : posOf v N = []
  · simp [cycleClauses, hv, encodeCnf_nil]
  · have hvlt : v < (varsList N).sum + 1 := by
      obtain ⟨j, hj⟩ : ∃ j, j ∈ posOf v N := by
        cases hpos : posOf v N with
        | nil => exact absurd hpos hv
        | cons j js => exact ⟨j, by simp⟩
      obtain ⟨l, hl, hl2⟩ := mem_posOf.mp hj
      have hlmem : l ∈ N.flatten := by
        have e := List.mem_zipIdx hl
        rw [Nat.zero_add] at e
        have hlt : j - 0 < N.flatten.length := e.2.1
        rw [e.2.2]
        exact List.getElem_mem hlt
      exact Nat.lt_of_le_of_lt (hl2 ▸ var_le_sum N l hlmem) (Nat.lt_succ_self _)
    have hseg : (List.range ((varsList N).sum + 1)).flatMap
          (fun u => cycleClauses 0 (posOf u N)) =
        ((List.range v).flatMap (fun u => cycleClauses 0 (posOf u N))) ++
          cycleClauses 0 (posOf v N) ++
          (((List.range ((varsList N).sum + 1)).drop (v + 1)).flatMap
            (fun u => cycleClauses 0 (posOf u N))) := by
      have htake : (List.range ((varsList N).sum + 1)).take (v + 1) =
          (List.range v) ++ [v] := by
        rw [List.take_range,
          show min (v + 1) ((varsList N).sum + 1) = v + 1 from by omega,
          List.range_succ]
      have hdecomp : (List.range ((varsList N).sum + 1)) =
          (List.range v) ++ [v] ++
            (List.range ((varsList N).sum + 1)).drop (v + 1) := by
        conv_lhs => rw [← List.take_append_drop (v + 1)
          (List.range ((varsList N).sum + 1)), htake]
      conv_lhs => rw [hdecomp]
      rw [List.flatMap_append, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [occT, encodeCnf_append, hseg, List.length_append]
    omega

/-- The links accumulated over any initial segment of variables are no
longer than the whole transformed encoding. -/
theorem encodeCnf_flatMap_range_le (N : cnf) (i : Nat) :
    (EvalCnfCmd.encodeCnf ((List.range i).flatMap
      (fun u => cycleClauses 0 (posOf u N)))).length ≤
      (EvalCnfCmd.encodeCnf (occT 0 N)).length := by
  have hA : ∀ v, (varsList N).sum + 1 ≤ v → cycleClauses 0 (posOf v N) = [] := by
    intro v hv
    have hnil : posOf v N = [] := by
      apply posOf_eq_nil_of_forall
      intro lit hlit
      have hle := var_le_sum N lit hlit
      exact Nat.ne_of_lt (hle.trans_lt (Nat.lt_of_succ_le hv))
    simp [hnil, cycleClauses]
  have hocc : (EvalCnfCmd.encodeCnf (occT 0 N)).length =
      (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length +
        (EvalCnfCmd.encodeCnf ((List.range ((varsList N).sum + 1)).flatMap
          (fun u => cycleClauses 0 (posOf u N)))).length := by
    rw [occT, encodeCnf_append, List.length_append]
  rw [hocc]
  by_cases hi : i ≤ (varsList N).sum + 1
  · have hpre : (List.range ((varsList N).sum + 1)).flatMap
          (fun u => cycleClauses 0 (posOf u N)) =
        (List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)) ++
          ((List.range ((varsList N).sum + 1)).drop i).flatMap
            (fun u => cycleClauses 0 (posOf u N)) := by
      have htake : (List.range ((varsList N).sum + 1)).take i = List.range i := by
        rw [List.take_range, Nat.min_eq_left hi]
      have hdecomp : (List.range ((varsList N).sum + 1)) =
          (List.range i) ++ (List.range ((varsList N).sum + 1)).drop i := by
        conv_lhs => rw [← List.take_append_drop i
          (List.range ((varsList N).sum + 1)), htake]
      conv_lhs => rw [hdecomp]
      rw [List.flatMap_append]
    simp only [hpre, encodeCnf_append, List.length_append]
    omega
  · have heq := flatMap_range_extend (fun u => cycleClauses 0 (posOf u N))
      ((varsList N).sum + 1) hA i (by omega)
    have hlen : (EvalCnfCmd.encodeCnf ((List.range i).flatMap
        (fun u => cycleClauses 0 (posOf u N)))).length =
        (EvalCnfCmd.encodeCnf ((List.range ((varsList N).sum + 1)).flatMap
          (fun u => cycleClauses 0 (posOf u N)))).length := by
      rw [heq]
    omega

/-- The renamed encoding is at most quadratic in the literal count. -/
theorem encodeCnf_renameCnf_length_le (N : cnf) :
    (EvalCnfCmd.encodeCnf (renameCnf 0 N)).length ≤
      N.flatten.length * (N.flatten.length + 3) + N.length := by
  rw [encodeCnf_length]
  have hlen2 : (renameCnf 0 N).length = N.length := renameFrom_length 0 0 N
  rw [hlen2]
  have h1 : (renameCnf 0 N).flatten.map (fun l => l.2 + 3) =
      (N.flatten.zipIdx).map (fun p => p.2 + 3) := by
    rw [renameCnf, flatten_renameFrom]
    rw [List.map_map]
    congr 1
    funext p
    simp
  rw [h1]
  have h2 : ((N.flatten.zipIdx).map (fun p => p.2 + 3)).sum ≤
      ((N.flatten.zipIdx).map (fun p => p.2 + 3)).length *
        (N.flatten.length + 3) := by
    have h3 := List.sum_le_length_nsmul ((N.flatten.zipIdx).map (fun p => p.2 + 3))
      (N.flatten.length + 3) (by
        intro y hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        have e2 : p.2 < N.flatten.length := by
          have e := List.mem_zipIdx hp
          rw [Nat.zero_add] at e
          exact e.2.1
        omega)
    exact h3
  rw [List.length_map, List.length_zipIdx] at h2
  exact Nat.add_le_add_right h2 _

/-- Cost of the inner scan loop of phase B. -/
theorem linksLoop_cost (v : Nat) (N : cnf) (s : State) (out0 : List Nat)
    (vacc0 : Nat)
    (hCUR : s.get rCUR = EvalCnfCmd.encodeCnf N)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N)
    (hOUT : s.get rOUT = out0) (hJ2 : s.get rJ2 = List.replicate 0 1)
    (hPREV : s.get rPREV = List.replicate 0 1)
    (hFIRST : s.get rFIRST = List.replicate 0 1)
    (hHAS : s.get rHAS = [0]) (hVARACC : s.get rVARACC = List.replicate vacc0 1)
    (hSA : s.get rSA = [0]) (hSB : s.get rSB = [0])
    (hVCTR : s.get rVCTR = List.replicate v 1)
    (hv : v ≤ (EvalCnfCmd.encodeCnf N).length)
    (hout0 : out0.length ≤ 2 * (EvalCnfCmd.encodeCnf (occT 0 N)).length)
    (hvacc0 : vacc0 ≤ (EvalCnfCmd.encodeCnf N).length) :
    (Cmd.forBnd rIDX3 rIN linksBody).cost s ≤
      1 + (EvalCnfCmd.encodeCnf N).length *
          (linksBody.flatK * (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1)) +
        (EvalCnfCmd.encodeCnf N).length * (EvalCnfCmd.encodeCnf N).length := by
  suffices h : (Cmd.forBnd rIDX3 rIN linksBody).cost s ≤
      1 + (s.get rIN).length *
          (linksBody.flatK * (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1)) +
        (s.get rIN).length * (s.get rIN).length by
    rwa [hIN] at h
  have hl' : ∀ c ∈ EvalCnfCmd.encodeCnf N, c ≤ 1 := EvalCnfCmd.encodeCnf_bit N
  have hreads : ∀ r ∈ linksBody.costReads,
      r = rCUR ∨ r = rVARACC ∨ r = rVCTR ∨ r = rOUT ∨ r = rPREV ∨ r = rJ2 := by
    have heq : linksBody.costReads = [rCUR, rVARACC, rVCTR, rOUT, rPREV, rOUT,
        rJ2, rJ2, rJ2, rJ2] := by decide
    intro r hr
    rw [heq] at hr
    simp at hr
    tauto
  refine Cmd.cost_forBnd_flat_le rIDX3 rIN linksBody (by decide) s
    (4 * ((EvalCnfCmd.encodeCnf N).length +
      (EvalCnfCmd.encodeCnf (occT 0 N)).length))
    (fun i st => st.get rCUR = (EvalCnfCmd.encodeCnf N).drop i ∧
      st.get rOUT = (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).1 ∧
      st.get rJ2 =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.1 1 ∧
      st.get rPREV =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.1 1 ∧
      st.get rFIRST =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.1 1 ∧
      st.get rHAS =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.1 then 1 else 0] ∧
      st.get rVARACC =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.1 1 ∧
      st.get rSA =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.1 then 1 else 0] ∧
      st.get rSB =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.2 then 1 else 0] ∧
      ((linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.1 = false →
        (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.2 = false) ∧
      st.get rVCTR = List.replicate v 1 ∧
      st.get rIN = EvalCnfCmd.encodeCnf N)
    (by simp [linkRunFrom, hCUR, hOUT, hJ2, hPREV, hFIRST, hHAS, hVARACC, hSA, hSB,
      hVCTR, hIN]) (fun i st hi hM => ?_) (fun i st hi hM r hr => ?_)
  · obtain ⟨hCURi, hOUTi, hJ2i, hPREVi, hFIRSTi, hHASi, hVARACCi, hSAi, hSBi, himpi,
      hVCTRi, hINi⟩ := hM
    have hi' : i < (EvalCnfCmd.encodeCnf N).length := hIN ▸ hi
    rw [List.drop_eq_getElem_cons hi'] at hCURi
    have hcell : (EvalCnfCmd.encodeCnf N)[i] ≤ 1 := hl' _ (List.getElem_mem hi')
    have hCUR' : (st.set rIDX3 (List.replicate i 1)).get rCUR =
        (EvalCnfCmd.encodeCnf N)[i] :: (EvalCnfCmd.encodeCnf N).drop (i + 1) := by
      simp [State.get_set_ne, hCURi]
    have hOUT' : (st.set rIDX3 (List.replicate i 1)).get rOUT =
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).1 := by
      simp [State.get_set_ne, hOUTi]
    have hJ2' : (st.set rIDX3 (List.replicate i 1)).get rJ2 =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.1 1 := by
      simp [State.get_set_ne, hJ2i]
    have hPREV' : (st.set rIDX3 (List.replicate i 1)).get rPREV =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.1 1 := by
      simp [State.get_set_ne, hPREVi]
    have hFIRST' : (st.set rIDX3 (List.replicate i 1)).get rFIRST =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.1 1 := by
      simp [State.get_set_ne, hFIRSTi]
    have hHAS' : (st.set rIDX3 (List.replicate i 1)).get rHAS =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.1 then 1 else 0] := by
      simp [State.get_set_ne, hHASi]
    have hVARACC' : (st.set rIDX3 (List.replicate i 1)).get rVARACC =
        List.replicate (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.1 1 := by
      simp [State.get_set_ne, hVARACCi]
    have hSA' : (st.set rIDX3 (List.replicate i 1)).get rSA =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.1 then 1 else 0] := by
      simp [State.get_set_ne, hSAi]
    have hSB' : (st.set rIDX3 (List.replicate i 1)).get rSB =
        [if (linkRunFrom v out0 vacc0
          ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.2 then 1 else 0] := by
      simp [State.get_set_ne, hSBi]
    have hVCTR' : (st.set rIDX3 (List.replicate i 1)).get rVCTR =
        List.replicate v 1 := by simp [State.get_set_ne, hVCTRi]
    have hIN' : (st.set rIDX3 (List.replicate i 1)).get rIN =
        EvalCnfCmd.encodeCnf N := by simp [State.get_set_ne, hINi]
    obtain ⟨hCURn, hOUTn, hJ2n, hPREVn, hFIRSTn, hHASn, hVARACCn, hSAn, hSBn⟩ :=
      linksBody_eval (st.set rIDX3 (List.replicate i 1)) v
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.2.2
        (EvalCnfCmd.encodeCnf N)[i] ((EvalCnfCmd.encodeCnf N).drop (i + 1))
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.2.1
        (linkRunFrom v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)).2.2.2.2.1
        hcell himpi hSA' hSB' hCUR' hOUT' hJ2' hPREV' hFIRST' hHAS' hVARACC' hVCTR'
    refine ⟨hCURn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hOUTn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hJ2n
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hPREVn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hFIRSTn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hHASn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hVARACCn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hSAn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']; exact hSBn
    · rw [linkRunFrom_take_succ v out0 vacc0 _ i hi']
      exact linkStep_himp v _ _ himpi
    · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rVCTR ∉ Cmd.writes linksBody)]
      exact hVCTR'
    · rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rIN ∉ Cmd.writes linksBody)]
      exact hIN'
  · have hset : ∀ (q : Var), q ≠ rIDX3 →
        (st.set rIDX3 (List.replicate i 1)).get q = st.get q :=
      fun q hq => State.get_set_ne _ _ _ _ hq
    have hcnt := linkRunFrom_counts v out0 vacc0 ((EvalCnfCmd.encodeCnf N).take i)
    have htake : ((EvalCnfCmd.encodeCnf N).take i).length ≤
        (EvalCnfCmd.encodeCnf N).length := by
      rw [List.length_take]
      omega
    have hpre := linkRunFrom_take_out_prefix v out0 vacc0 (EvalCnfCmd.encodeCnf N) i
    have hfull : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
        4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) := by
      have h := linkRunFrom_encodeCnf v N out0 vacc0
      have hlen : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
          ((linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1 ++
            (if (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).2.2.2.2.1 then
              EvalCnfCmd.encodeClause
                [(false, (linkRunFrom v out0 vacc0
                    (EvalCnfCmd.encodeCnf N)).2.2.1),
                 (true, (linkRunFrom v out0 vacc0
                    (EvalCnfCmd.encodeCnf N)).2.2.2.1)]
            else [])).length := by
        simp [List.length_append]
      rw [h] at hlen
      have hcyc := encodeCnf_cycleClauses_le v N
      simp [List.length_append] at hlen
      omega
    rcases hreads r hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hset rCUR (by decide), hM.1, List.length_drop]
      omega
    · rw [hset rVARACC (by decide), hM.2.2.2.2.2.2.1]
      simp only [List.length_replicate]
      omega
    · rw [hset rVCTR (by decide), hM.2.2.2.2.2.2.2.2.2.2.1]
      simp only [List.length_replicate]
      omega
    · rw [hset rOUT (by decide), hM.2.1]
      obtain ⟨t, ht⟩ := hpre
      rw [ht, List.length_append] at hfull
      omega
    · rw [hset rPREV (by decide), hM.2.2.2.1]
      simp only [List.length_replicate]
      omega
    · rw [hset rJ2 (by decide), hM.2.2.1]
      simp only [List.length_replicate]
      omega

/-- After one literal, the variable accumulator is that literal's variable. -/
theorem linkFold_clause_vacc (v : Nat) (C : clause) (out : List Nat)
    (k prev first : Nat) (has : Bool) (vacc : Nat) :
    ((EvalCnfCmd.encodeClause C).foldl (linkStep v)
      (out, k, prev, first, has, vacc, false, false)).2.2.2.2.2.1 ≤
      max vacc ((C.map (fun l => l.2)).sum) := by
  induction C generalizing out k prev first has vacc with
  | nil =>
      show (linkStep v (out, k, prev, first, has, vacc, false, false) 0).2.2.2.2.2.1 ≤ _
      simp [linkStep]
  | cons lit C ih =>
      obtain ⟨pol, w⟩ := lit
      have henc : EvalCnfCmd.encodeClause ((pol, w) :: C) =
          EvalCnfCmd.encodeLit (pol, w) ++ EvalCnfCmd.encodeClause C := by
        simp [EvalCnfCmd.encodeClause, List.append_assoc]
      rw [henc, List.foldl_append, linkFold_lit]
      have h := ih (out := out ++ (if w = v then
          (if has then EvalCnfCmd.encodeClause [(false, prev), (true, k)] else [])
          else []))
        (k := k + 1) (prev := if w = v then k else prev)
        (first := if w = v then (if has then first else k) else first)
        (has := if w = v then true else has) (vacc := w)
      have hle : max w ((C.map (fun l => l.2)).sum) ≤
          max vacc (((pol, w) :: C).map (fun l => l.2)).sum := by
        simp [List.map_cons, List.sum_cons]
      exact h.trans hle

/-- After a whole CNF, the variable accumulator is at most the larger of
the initial value and the sum of all variables. -/
theorem linkFold_cnf_vacc (v : Nat) (N : cnf) (out : List Nat)
    (k prev first : Nat) (has : Bool) (vacc : Nat) :
    ((EvalCnfCmd.encodeCnf N).foldl (linkStep v)
      (out, k, prev, first, has, vacc, false, false)).2.2.2.2.2.1 ≤
      max vacc ((N.flatten.map (fun l => l.2)).sum) := by
  induction N generalizing out k prev first has vacc with
  | nil =>
      show (vacc : Nat) ≤ max vacc (([] : cnf).flatten.map (fun l => l.2)).sum
      exact Nat.le_max_left _ _
  | cons C N ih =>
      have henc : EvalCnfCmd.encodeCnf (C :: N) =
          EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf N := by
        simp [EvalCnfCmd.encodeCnf]
      rw [henc, List.foldl_append]
      obtain ⟨vacc₁, ih₁⟩ := linkFold_clause v C out k prev first has vacc
      have h1 := linkFold_clause_vacc v C out k prev first has vacc
      rw [ih₁]
      have h := ih (out := out ++ EvalCnfCmd.encodeCnf
          (chainEmit first prev has (posOfClause k v C)).1)
        (k := k + C.length)
        (prev := (chainEmit first prev has (posOfClause k v C)).2.1)
        (first := (chainEmit first prev has (posOfClause k v C)).2.2.1)
        (has := (chainEmit first prev has (posOfClause k v C)).2.2.2)
        (vacc := vacc₁)
      have hle : max vacc₁ ((N.flatten.map (fun l => l.2)).sum) ≤
          max vacc (((C :: N).flatten.map (fun l => l.2)).sum) := by
        have h2 : vacc₁ ≤ max vacc ((C.map (fun l => l.2)).sum) := by
          have e : vacc₁ =
              ((EvalCnfCmd.encodeClause C).foldl (linkStep v)
                (out, k, prev, first, has, vacc, false, false)).2.2.2.2.2.1 :=
            (congrArg (fun st => st.2.2.2.2.2.1) ih₁).symm
          rw [e]
          exact h1
        have h3 : (C.map (fun l => l.2)).sum ≤
            ((C :: N).flatten.map (fun l => l.2)).sum := by
          simp [List.flatten_cons, List.map_append, List.sum_append]
        have h4 : (N.flatten.map (fun l => l.2)).sum ≤
            ((C :: N).flatten.map (fun l => l.2)).sum := by
          simp [List.flatten_cons, List.map_append, List.sum_append]
        simp [List.flatten_cons, List.map_append, List.sum_append] at h3 h4 ⊢
        omega
      exact h.trans hle

/-- Pointwise sum bound for the variable components. -/
theorem map_snd_sum_le (l : List literal) :
    (l.map (fun l => l.2)).sum ≤ (l.map (fun l => l.2 + 3)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have e1 : ((a :: l).map (fun l => l.2)).sum =
          a.2 + (l.map (fun l => l.2)).sum := rfl
      have e2 : ((a :: l).map (fun l => l.2 + 3)).sum =
          (a.2 + 3) + (l.map (fun l => l.2 + 3)).sum := rfl
      rw [e1, e2]
      exact Nat.add_le_add (Nat.le_add_right _ _) ih

/-- The sum of all variables is at most the encoding length. -/
theorem varsList_sum_le (N : cnf) :
    (varsList N).sum ≤ (EvalCnfCmd.encodeCnf N).length := by
  have h2 : (varsList N).sum = (N.flatten.map (fun l => l.2)).sum := rfl
  rw [encodeCnf_length, h2]
  exact (map_snd_sum_le N.flatten).trans (Nat.le_add_right _ _)

/-- The pass's final variable accumulator is at most the larger of the
initial value and the encoding length. -/
theorem linkRunFrom_vacc_le (v : Nat) (N : cnf) (out : List Nat) (vacc : Nat) :
    (linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N)).2.2.2.2.2.1 ≤
      max vacc (varsList N).sum := by
  have h := linkFold_cnf_vacc v N out 0 0 0 false vacc
  have h2 : (EvalCnfCmd.encodeCnf N).foldl (linkStep v)
      (out, 0, 0, 0, false, vacc, false, false) =
      linkRunFrom v out vacc (EvalCnfCmd.encodeCnf N) := rfl
  rw [← h2]
  exact h

/-- Cost of one pass of phase B. -/
theorem linksPass_cost (v : Nat) (N : cnf) (s : State) (out0 : List Nat)
    (vacc0 : Nat)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N) (hOUT : s.get rOUT = out0)
    (hVARACC : s.get rVARACC = List.replicate vacc0 1)
    (hVCTR : s.get rVCTR = List.replicate v 1)
    (hv : v ≤ (EvalCnfCmd.encodeCnf N).length)
    (hout0 : out0.length ≤ 2 * (EvalCnfCmd.encodeCnf (occT 0 N)).length)
    (hvacc0 : vacc0 ≤ (EvalCnfCmd.encodeCnf N).length) :
    linksPass.cost s ≤
      (Cmd.op (.copy rCUR rIN)).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (Cmd.op (.clear rJ2)).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (Cmd.op (.clear rPREV)).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (Cmd.op (.clear rFIRST)).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (setZero rHAS).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (setZero rSA).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (setZero rSB).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
        (1 + (EvalCnfCmd.encodeCnf N).length * (linksBody.flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1)) +
          (EvalCnfCmd.encodeCnf N).length * (EvalCnfCmd.encodeCnf N).length) +
        (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
          (4 * ((EvalCnfCmd.encodeCnf N).length +
            (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) + 8 := by
  have hlen : (s.get rIN).length = (EvalCnfCmd.encodeCnf N).length := by rw [hIN]
  have gCUR : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rCUR =
      EvalCnfCmd.encodeCnf N := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne,
      hIN]
  have gIN : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rIN =
      EvalCnfCmd.encodeCnf N := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hIN]
  have gOUT : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rOUT =
      out0 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hOUT]
  have gJ2 : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rJ2 =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gPREV : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rPREV =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gFIRST : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rFIRST =
      List.replicate 0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gHAS : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rHAS =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gVARACC : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rVARACC =
      List.replicate vacc0 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hVARACC]
  have gSA : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rSA =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gSB : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rSB =
      [0] := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.get_set_ne]
  have gVCTR : ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s))))))).get rVCTR =
      List.replicate v 1 := by
    simp [setZero, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_ne, hVCTR]
  have hloop := linksLoop_cost v N
    ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))))))
    out0 vacc0 gCUR gIN gOUT gJ2 gPREV gFIRST gHAS gVARACC gSA gSB gVCTR hv hout0
    hvacc0
  obtain ⟨hOUTf, hHASf, hPREVf, hFIRSTf, -, hINf⟩ := linksLoop v
    (EvalCnfCmd.encodeCnf N) (EvalCnfCmd.encodeCnf_bit N)
    ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))))))
    out0 vacc0 gCUR gIN gOUT gJ2 gPREV gFIRST gHAS gVARACC gSA gSB gVCTR
  have hf1 : (Cmd.op (.copy rCUR rIN)).cost s ≤
      (Cmd.op (.copy rCUR rIN)).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) := by
    have h := (Cmd.cost_le_flat (Cmd.op (.copy rCUR rIN)) (by simp [Cmd.loopFree]) s
      (EvalCnfCmd.encodeCnf N).length (fun r hr => by
        have heq : (Cmd.op (.copy rCUR rIN)).costReads = [rIN] := by decide
        rw [heq] at hr
        simp at hr
        subst hr
        rw [hIN])).1
    exact h.trans (Nat.mul_le_mul_left _
      (by omega : (EvalCnfCmd.encodeCnf N).length + 1 ≤
        4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1))
  have hf2 : (Cmd.op (.clear rJ2)).cost ((Cmd.op (.copy rCUR rIN)).eval s) ≤
      (Cmd.op (.clear rJ2)).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (Cmd.op (.clear rJ2)) (by simp [Cmd.loopFree]) _ _
      (fun r hr => by simp [Cmd.costReads, Op.costReads] at hr)).1
  have hf3 : (Cmd.op (.clear rPREV)).cost
      ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)) ≤
      (Cmd.op (.clear rPREV)).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (Cmd.op (.clear rPREV)) (by simp [Cmd.loopFree]) _ _
      (fun r hr => by simp [Cmd.costReads, Op.costReads] at hr)).1
  have hf4 : (Cmd.op (.clear rFIRST)).cost
      ((Cmd.op (.clear rPREV)).eval ((Cmd.op (.clear rJ2)).eval
        ((Cmd.op (.copy rCUR rIN)).eval s))) ≤
      (Cmd.op (.clear rFIRST)).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (Cmd.op (.clear rFIRST)) (by simp [Cmd.loopFree]) _ _
      (fun r hr => by simp [Cmd.costReads, Op.costReads] at hr)).1
  have hf5 : (setZero rHAS).cost
      ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
        ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))) ≤
      (setZero rHAS).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (setZero rHAS) (by simp [setZero, Cmd.loopFree]) _ _
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hf6 : (setZero rSA).cost
      ((setZero rHAS).eval ((Cmd.op (.clear rFIRST)).eval
        ((Cmd.op (.clear rPREV)).eval ((Cmd.op (.clear rJ2)).eval
          ((Cmd.op (.copy rCUR rIN)).eval s))))) ≤
      (setZero rSA).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (setZero rSA) (by simp [setZero, Cmd.loopFree]) _ _
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hf7 : (setZero rSB).cost
      ((setZero rSA).eval ((setZero rHAS).eval ((Cmd.op (.clear rFIRST)).eval
        ((Cmd.op (.clear rPREV)).eval ((Cmd.op (.clear rJ2)).eval
          ((Cmd.op (.copy rCUR rIN)).eval s)))))) ≤
      (setZero rSB).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) :=
    (Cmd.cost_le_flat (setZero rSB) (by simp [setZero, Cmd.loopFree]) _ _
      (fun r hr => by simp [setZero, Cmd.costReads, Op.costReads] at hr)).1
  have hf9 : (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).cost
      ((Cmd.forBnd rIDX3 rIN linksBody).eval
        ((setZero rSB).eval ((setZero rSA).eval ((setZero rHAS).eval
          ((Cmd.op (.clear rFIRST)).eval ((Cmd.op (.clear rPREV)).eval
            ((Cmd.op (.clear rJ2)).eval ((Cmd.op (.copy rCUR rIN)).eval s)))))))) ≤
      (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
        (4 * ((EvalCnfCmd.encodeCnf N).length +
          (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) := by
    refine (Cmd.cost_le_flat _ (by decide) _
      (4 * ((EvalCnfCmd.encodeCnf N).length +
        (EvalCnfCmd.encodeCnf (occT 0 N)).length)) (fun r hr => ?_)).1
    have heq : (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).costReads =
        [rOUT, rPREV, rOUT, rFIRST] := by decide
    rw [heq] at hr
    simp at hr
    have hcnt := linkRunFrom_counts v out0 vacc0 (EvalCnfCmd.encodeCnf N)
    have hpre := linkRunFrom_encodeCnf v N out0 vacc0
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hOUTf]
      have hlen : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
          out0.length + (EvalCnfCmd.encodeCnf (cycleClauses 0 (posOf v N))).length := by
        have h2 : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
            ((linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1 ++
              (if (linkRunFrom v out0 vacc0
                  (EvalCnfCmd.encodeCnf N)).2.2.2.2.1 then
                EvalCnfCmd.encodeClause
                  [(false, (linkRunFrom v out0 vacc0
                      (EvalCnfCmd.encodeCnf N)).2.2.1),
                   (true, (linkRunFrom v out0 vacc0
                      (EvalCnfCmd.encodeCnf N)).2.2.2.1)]
              else [])).length := by
          simp [List.length_append]
        rw [hpre] at h2
        simpa [List.length_append] using h2
      have hcyc := encodeCnf_cycleClauses_le v N
      omega
    · rw [hPREVf]
      simp only [List.length_replicate]
      omega
    · rw [hOUTf]
      have hlen : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
          out0.length + (EvalCnfCmd.encodeCnf (cycleClauses 0 (posOf v N))).length := by
        have h2 : (linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1.length ≤
            ((linkRunFrom v out0 vacc0 (EvalCnfCmd.encodeCnf N)).1 ++
              (if (linkRunFrom v out0 vacc0
                  (EvalCnfCmd.encodeCnf N)).2.2.2.2.1 then
                EvalCnfCmd.encodeClause
                  [(false, (linkRunFrom v out0 vacc0
                      (EvalCnfCmd.encodeCnf N)).2.2.1),
                   (true, (linkRunFrom v out0 vacc0
                      (EvalCnfCmd.encodeCnf N)).2.2.2.1)]
              else [])).length := by
          simp [List.length_append]
        rw [hpre] at h2
        simpa [List.length_append] using h2
      have hcyc := encodeCnf_cycleClauses_le v N
      omega
    · rw [hFIRSTf]
      simp only [List.length_replicate]
      omega
  have e : linksPass = (Cmd.op (.copy rCUR rIN) ;; Cmd.op (.clear rJ2) ;;
      Cmd.op (.clear rPREV) ;; Cmd.op (.clear rFIRST) ;; setZero rHAS ;;
      setZero rSA ;; setZero rSB ;; Cmd.forBnd rIDX3 rIN linksBody ;;
      Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop) := rfl
  rw [e, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq,
    Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
  omega

/-- Cost of phase B as a whole. -/
theorem linksProg_cost (N : cnf) (s : State) (out0 : List Nat) (vacc0 : Nat)
    (hIN : s.get rIN = EvalCnfCmd.encodeCnf N) (hOUT : s.get rOUT = out0)
    (hVARACC : s.get rVARACC = List.replicate vacc0 1)
    (hout0 : out0.length ≤ (EvalCnfCmd.encodeCnf (occT 0 N)).length)
    (hvacc0 : vacc0 ≤ (EvalCnfCmd.encodeCnf N).length) :
    linksProg.cost s ≤
      1 + (s.get rIN).length *
        ((Cmd.op (.copy rCUR rIN)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (Cmd.op (.clear rJ2)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (Cmd.op (.clear rPREV)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (Cmd.op (.clear rFIRST)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (setZero rHAS).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (setZero rSA).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (setZero rSB).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) +
          (1 + (EvalCnfCmd.encodeCnf N).length * (linksBody.flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1)) +
            (EvalCnfCmd.encodeCnf N).length * (EvalCnfCmd.encodeCnf N).length) +
          (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
            (4 * ((EvalCnfCmd.encodeCnf N).length +
              (EvalCnfCmd.encodeCnf (occT 0 N)).length) + 1) + 8) +
        (s.get rIN).length * (s.get rIN).length := by
  have hl' : ∀ c ∈ EvalCnfCmd.encodeCnf N, c ≤ 1 := EvalCnfCmd.encodeCnf_bit N
  have e : linksProg = Cmd.forBnd rVCTR rIN linksPass := rfl
  rw [e]
  refine Cmd.cost_forBnd_le rVCTR rIN linksPass s _
    (fun i st => st.get rIN = EvalCnfCmd.encodeCnf N ∧
      st.get rOUT = out0 ++ EvalCnfCmd.encodeCnf
        ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N))) ∧
      ∃ vacc, st.get rVARACC = List.replicate vacc 1 ∧
        vacc ≤ (EvalCnfCmd.encodeCnf N).length)
    (by simp [hIN, hOUT, hVARACC, hvacc0, encodeCnf_nil]) (fun i st hi hM => ?_)
    (fun i st hi hM => ?_)
  · obtain ⟨hINi, hOUTi, vacc, hVARACCi, hvacci⟩ := hM
    have hOUT' : (st.set rVCTR (List.replicate i 1)).get rOUT =
        out0 ++ EvalCnfCmd.encodeCnf
          ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N))) := by
      simp [State.get_set_ne, hOUTi]
    have hIN' : (st.set rVCTR (List.replicate i 1)).get rIN =
        EvalCnfCmd.encodeCnf N := by simp [State.get_set_ne, hINi]
    have hVARACC' : (st.set rVCTR (List.replicate i 1)).get rVARACC =
        List.replicate vacc 1 := by simp [State.get_set_ne, hVARACCi]
    have hVCTR' : (st.set rVCTR (List.replicate i 1)).get rVCTR =
        List.replicate i 1 := by simp [State.get_set_eq]
    have hout0' : (out0 ++ EvalCnfCmd.encodeCnf
        ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)))).length ≤
        2 * (EvalCnfCmd.encodeCnf (occT 0 N)).length := by
      have h1 := encodeCnf_flatMap_range_le N i
      simp [List.length_append]
      omega
    have hi' : i ≤ (EvalCnfCmd.encodeCnf N).length := by
      have h2 : (s.get rIN).length = (EvalCnfCmd.encodeCnf N).length := by rw [hIN]
      omega
    obtain ⟨hOUTf, hINf, hVARACCf⟩ := linksPass_eval (st.set rVCTR (List.replicate i 1))
      i (EvalCnfCmd.encodeCnf N) hl'
      (out0 ++ EvalCnfCmd.encodeCnf
        ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)))) vacc
      hIN' hOUT' hVARACC' hVCTR'
    refine ⟨hINf, ?_, _, hVARACCf, ?_⟩
    · rw [linkRunFrom_encodeCnf] at hOUTf
      rw [hOUTf]
      have hrange : (List.range (i + 1)).flatMap
            (fun u => cycleClauses 0 (posOf u N)) =
          (List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)) ++
            cycleClauses 0 (posOf i N) := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hrange, encodeCnf_append, List.append_assoc]
    · have hle := linkRunFrom_vacc_le i N
        (out0 ++ EvalCnfCmd.encodeCnf
          ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)))) vacc
      have hs := varsList_sum_le N
      omega
  · obtain ⟨hINi, hOUTi, vacc, hVARACCi, hvacci⟩ := hM
    have hOUT' : (st.set rVCTR (List.replicate i 1)).get rOUT =
        out0 ++ EvalCnfCmd.encodeCnf
          ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N))) := by
      simp [State.get_set_ne, hOUTi]
    have hIN' : (st.set rVCTR (List.replicate i 1)).get rIN =
        EvalCnfCmd.encodeCnf N := by simp [State.get_set_ne, hINi]
    have hVARACC' : (st.set rVCTR (List.replicate i 1)).get rVARACC =
        List.replicate vacc 1 := by simp [State.get_set_ne, hVARACCi]
    have hVCTR' : (st.set rVCTR (List.replicate i 1)).get rVCTR =
        List.replicate i 1 := by simp [State.get_set_eq]
    have hout0' : (out0 ++ EvalCnfCmd.encodeCnf
        ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)))).length ≤
        2 * (EvalCnfCmd.encodeCnf (occT 0 N)).length := by
      have h1 := encodeCnf_flatMap_range_le N i
      simp [List.length_append]
      omega
    have hi' : i ≤ (EvalCnfCmd.encodeCnf N).length := by
      have h2 : (s.get rIN).length = (EvalCnfCmd.encodeCnf N).length := by rw [hIN]
      omega
    have hcost := linksPass_cost i N (st.set rVCTR (List.replicate i 1))
      (out0 ++ EvalCnfCmd.encodeCnf
        ((List.range i).flatMap (fun u => cycleClauses 0 (posOf u N)))) vacc
      hIN' hOUT' hVARACC' hVCTR' hi' hout0' hvacci
    exact hcost


/-- The transformed encoding is at most quartic in the input length
(well-formed case). -/
theorem occT_encodeCnf_length_le (x : List Bool)
    (hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true) :
    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length ≤
      20 * (x.length + 1) ^ 4 + 1 := by
  have h := occMap_length_le x hwf
  have hocc : occMap x =
      CookLevin.Lang.boolsOf (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))) := by
    simp [occMap, hwf]
  rw [hocc] at h
  simpa [CookLevin.Lang.boolsOf] using h

theorem boolsOf_strBits : ∀ x : List Bool, CookLevin.Lang.boolsOf
    (CookLevin.Lang.strBits x) = x := by
  intro x
  induction x with
  | nil => rfl
  | cons b t ih =>
      cases b with
      | false =>
          have e1 : CookLevin.Lang.strBits (false :: t) =
              0 :: CookLevin.Lang.strBits t := rfl
          have e2 : CookLevin.Lang.boolsOf (0 :: CookLevin.Lang.strBits t) =
              false :: CookLevin.Lang.boolsOf (CookLevin.Lang.strBits t) := rfl
          rw [e1, e2, ih]
      | true =>
          have e1 : CookLevin.Lang.strBits (true :: t) =
              1 :: CookLevin.Lang.strBits t := rfl
          have e2 : CookLevin.Lang.boolsOf (1 :: CookLevin.Lang.strBits t) =
              true :: CookLevin.Lang.boolsOf (CookLevin.Lang.strBits t) := rfl
          rw [e1, e2, ih]

theorem occCmd_usesBelow : Cmd.UsesBelow occCmd 26 := by
  simp [occCmd, wfProg, wfBody, renameProg, renameBody, linksProg, linksPass,
    linksBody, processOcc, emitLink, emitBit, setZero, setOne, nop,
    Cmd.UsesBelow, Op.UsesBelow, rIN, rCUR, rHD, rOUT, rJ, rVARACC, rWF, rSA, rSB,
    rIDX, rIDX2, rIDX3, rVCTR, rEQ, rPREV, rFIRST, rHAS, rJ2, rTMP]


/-- Polynomial domination facts used by the cost assembly. All are proved
by linear arithmetic over the atoms `n`, `n * n`, `(n + 1) ^ 2`,
`(n + 1) ^ 4`, `(n + 1) ^ 8` with the relations between them supplied
explicitly. -/
theorem xbound3 (n R : Nat) (hR : R ≤ n * n + 3 * n + (n + 1)) :
    R + 1 ≤ 100 * (n + 1) ^ 8 := by
  have hP2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hP28 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem xbound4 (n E R : Nat) (hE : E ≤ n + 1) (hR : R ≤ n * n + 3 * n + (n + 1)) :
    E + R + 1 ≤ 100 * (n + 1) ^ 8 := by
  have hP2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hP28 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem xbound5 (n E T : Nat) (hE : E ≤ n + 1) (hT : T ≤ 20 * (n + 1) ^ 4 + 1) :
    4 * (E + T) + 1 ≤ 100 * (n + 1) ^ 8 := by
  have hP14 : (n + 1) ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hP48 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem xbound6 (n T : Nat) (hT : T ≤ 20 * (n + 1) ^ 4 + 1) :
    T + n + 1 ≤ 100 * (n + 1) ^ 8 := by
  have hP14 : (n + 1) ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hP48 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem xbound_mid1 (n L : Nat) (hL : L ≤ n + 1) :
    L * (L + 1) ≤ 100 * (n + 1) ^ 8 := by
  have h1 : L * (L + 1) ≤ (n + 1) * (n + 2) :=
    Nat.mul_le_mul hL (by omega)
  have hP2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hP28 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : (n + 1) * (n + 2) ≤ 100 * (n + 1) ^ 8 := by
    have e : (n + 1) * (n + 2) = n * n + 3 * n + 2 := by ring
    omega
  exact h1.trans h2

theorem xbound_mid2 (n E R : Nat) (hE : E ≤ n + 1)
    (hR : R ≤ n * n + 3 * n + (n + 1)) :
    E * (E + R + 1) ≤ 100 * (n + 1) ^ 8 := by
  have h1 : E * (E + R + 1) ≤ (n + 1) * (n * n + 5 * n + 3) :=
    Nat.mul_le_mul hE (by omega)
  have hP2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hP28 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : (n + 1) * (n * n + 5 * n + 3) ≤ 100 * (n + 1) ^ 8 := by
    have h3 : (n + 1) * (n * n + 5 * n + 3) ≤ (n + 1) * (100 * (n + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (n + 1) * (100 * (n + 1) ^ 2) = 100 * (n + 1) ^ 3 := by ring
    have h5 : (n + 1) ^ 3 ≤ (n + 1) ^ 8 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  exact h1.trans h2

theorem xbound_mid3 (n E T : Nat) (hE : E ≤ n + 1)
    (hT : T ≤ 20 * (n + 1) ^ 4 + 1) :
    E * (4 * (E + T) + 1) ≤ 100 * (n + 1) ^ 8 := by
  have hP14 : (n + 1) ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h1 : E * (4 * (E + T) + 1) ≤ (n + 1) * (80 * (n + 1) ^ 4 + 4 * n + 9) :=
    Nat.mul_le_mul hE (by omega)
  have h2 : (n + 1) * (80 * (n + 1) ^ 4 + 4 * n + 9) ≤ 100 * (n + 1) ^ 8 := by
    have h3 : (n + 1) * (80 * (n + 1) ^ 4 + 4 * n + 9) ≤
        (n + 1) * (100 * (n + 1) ^ 4) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (n + 1) * (100 * (n + 1) ^ 4) = 100 * (n + 1) ^ 5 := by ring
    have h5 : (n + 1) ^ 5 ≤ (n + 1) ^ 8 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  exact h1.trans h2

theorem xbound_sq (n E : Nat) (hE : E ≤ n + 1) :
    E * E ≤ 100 * (n + 1) ^ 8 := by
  have h1 : E * E ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hE hE
  have hP2 : (n + 1) ^ 2 = (n + 1) * (n + 1) := by ring
  have hP28 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- The budget constant: a large multiple of the sum of all flat cost
coefficients of the program's fragments. -/
def occCB : Nat := 100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
  (Cmd.ifBit rSA (setZero rWF) nop).flatK +
  (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)

/-- The full cost bound for the reduction program, with an explicit
polynomial budget. -/
theorem occCmd_cost :
    ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
      (∀ x : List Bool, occCmd.cost (CookLevin.Lang.certState x) ≤
        budget (encodable.size x)) ∧
      (∀ x : List Bool, encodable.size (occMap x) ≤
        budget (encodable.size x)) := by
  refine ⟨fun n => 40 * occCB * (n + 1) ^ 9 + 40 * occCB * (n + 1) ^ 8 + 20, ?_, ?_, ?_,
    ?_⟩
  · refine inOPoly_add (inOPoly_add
      (inOPoly_mul (inOPoly_const (40 * occCB)) ⟨9, 2 ^ 9, 1, ?_⟩)
      (inOPoly_mul (inOPoly_const (40 * occCB)) ⟨8, 2 ^ 8, 1, ?_⟩))
      (inOPoly_const 20)
    · intro n hn
      calc (n + 1) ^ 9 ≤ (2 * n) ^ 9 := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ 9 * n ^ 9 := by rw [Nat.mul_pow]
    · intro n hn
      calc (n + 1) ^ 8 ≤ (2 * n) ^ 8 := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ 8 * n ^ 8 := by rw [Nat.mul_pow]
  · intro a b hab
    dsimp only
    have h9 : (a + 1) ^ 9 ≤ (b + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
    have h8 : (a + 1) ^ 8 ≤ (b + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h9)
      (Nat.mul_le_mul_left _ h8)) (Nat.le_refl _)
  · intro x
    have hCB : ∀ F ∈ [wfBody.flatK, renameBody.flatK, linksBody.flatK,
        (setZero rSA).flatK, (setZero rSB).flatK, (setZero rHAS).flatK,
        (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK, (setOne rWF).flatK,
        (Cmd.ifBit rSA (setZero rWF) nop).flatK,
        (Cmd.ifBit rSB (setZero rWF) nop).flatK, (emitLink rPREV rFIRST).flatK,
        (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK,
        (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
          Cmd.ifBit rSB (setZero rWF) nop).flatK],
        100 * F ≤ occCB := by
      intro F hF
      have h1 : 100000 * F ≤ occCB := by
        show 100000 * F ≤ 100000 * (1 + wfBody.flatK + renameBody.flatK +
          linksBody.flatK + (setZero rSA).flatK + (setZero rSB).flatK +
          (setZero rHAS).flatK +
          (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
          (Cmd.ifBit rSA (setZero rWF) nop).flatK +
          (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
        refine Nat.mul_le_mul_left 100000 ?_
        simp at hF
        rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega
      have h2 : (100 : Nat) * F ≤ 100000 * F := by omega
      exact h2.trans h1
    have hfk5 : 5 ≤ wfBody.flatK := by decide
    have term_le : ∀ (F X : Nat), 100 * F ≤ occCB →
        X ≤ 100 * (x.length + 1) ^ 8 → F * X ≤ occCB * (x.length + 1) ^ 8 := by
      intro F X hF hX
      calc F * X ≤ F * (100 * (x.length + 1) ^ 8) := Nat.mul_le_mul_left F hX
        _ = (100 * F) * (x.length + 1) ^ 8 := by ring
        _ ≤ occCB * (x.length + 1) ^ 8 := Nat.mul_le_mul_right _ hF
    have hc0 : (CookLevin.Lang.certState x).get 0 = CookLevin.Lang.strBits x := rfl
    have h1IN : ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)).get rIN =
        CookLevin.Lang.strBits x := by
      rw [copy_get_eq]; exact hc0
    have h2CUR : ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get rCUR =
        CookLevin.Lang.strBits x := by
      rw [copy_get_eq]; exact h1IN
    have h2IN : ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get rIN =
        CookLevin.Lang.strBits x := by
      rw [Cmd.eval_get_of_not_writes _ _ _
        (by decide : rIN ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
      exact h1IN
    obtain ⟨h3WF, h3IN⟩ := wfProg_eval
      ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))
      (CookLevin.Lang.strBits x) h2CUR h2IN
    have hcV : (CookLevin.Lang.certState x).get rVARACC = [] := rfl
    have h1V : ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)).get
        rVARACC = [] := by
      rw [Cmd.eval_get_of_not_writes _ _ _
        (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rIN 0)))]
      exact hcV
    have h2V : ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))).get
        rVARACC = [] := by
      rw [Cmd.eval_get_of_not_writes _ _ _
        (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
      exact h1V
    have h3V : (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))).get
        rVARACC = [] := by
      rw [Cmd.eval_get_of_not_writes _ _ _ (by decide : rVARACC ∉ Cmd.writes wfProg)]
      exact h2V
    have hcost_full : occCmd.cost (CookLevin.Lang.certState x) =
        1 + (Cmd.op (.copy rIN 0)).cost (CookLevin.Lang.certState x) +
        (1 + (Cmd.op (.copy rCUR rIN)).cost
          ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)) +
        (1 + wfProg.cost ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))) +
        (1 + (Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
            (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).cost
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) +
          (Cmd.op (.copy 0 rOUT)).cost
            ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
              (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))))) := by
      rw [show occCmd = (Cmd.op (.copy rIN 0) ;; Cmd.op (.copy rCUR rIN) ;; wfProg ;;
        Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)) ;;
        Cmd.op (.copy 0 rOUT)) from rfl,
        Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq]
    rw [hcost_full]
    have c1 : (Cmd.op (.copy rIN 0)).cost (CookLevin.Lang.certState x) ≤
        5 * (x.length + 1) := by
      have h := (Cmd.cost_le_flat (Cmd.op (.copy rIN 0)) (by simp [Cmd.loopFree])
        (CookLevin.Lang.certState x) x.length (fun r hr => by
          have heq : (Cmd.op (.copy rIN 0)).costReads = [0] := by decide
          rw [heq] at hr
          have hr2 : r = 0 := List.mem_singleton.mp hr
          rw [hr2, hc0, CookLevin.Lang.strBits_length])).1
      exact h
    have c2 : (Cmd.op (.copy rCUR rIN)).cost
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)) ≤
        5 * (x.length + 1) := by
      have h := (Cmd.cost_le_flat (Cmd.op (.copy rCUR rIN)) (by simp [Cmd.loopFree])
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)) x.length
        (fun r hr => by
          have heq : (Cmd.op (.copy rCUR rIN)).costReads = [rIN] := by decide
          rw [heq] at hr
          have hr2 : r = rIN := List.mem_singleton.mp hr
          rw [hr2, h1IN, CookLevin.Lang.strBits_length])).1
      exact h
    have c3 : wfProg.cost ((Cmd.op (.copy rCUR rIN)).eval
        ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))) ≤
        (setZero rSA).flatK * ((CookLevin.Lang.strBits x).length + 1) +
        (setZero rSB).flatK * ((CookLevin.Lang.strBits x).length + 1) +
        (1 + (CookLevin.Lang.strBits x).length *
          (wfBody.flatK * ((CookLevin.Lang.strBits x).length + 1)) +
          (CookLevin.Lang.strBits x).length * (CookLevin.Lang.strBits x).length) +
        (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
          Cmd.ifBit rSB (setZero rWF) nop).flatK *
          ((CookLevin.Lang.strBits x).length + 1) + 3 :=
      wfProg_cost (CookLevin.Lang.strBits x) _ h2CUR h2IN
    have hoccT : (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length ≤
        20 * (x.length + 1) ^ 4 + 1 := by
      by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
      · exact occT_encodeCnf_length_le x hwf
      · have hfb : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
          cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
          · rfl
          · exact absurd h hwf
        have hcnf : SATStr.cnfOf x = [[]] :=
          CnfWellFormed.parseTotal_of_not_wf _ hfb
        rw [hcnf]
        have h1 : (EvalCnfCmd.encodeCnf (occT 0 [[]])).length = 1 := by decide
        omega
    have hL : (SATStr.cnfOf x).flatten.length ≤ x.length := by
      by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
      · have h1 := flatten_length_le_encodeCnf (SATStr.cnfOf x)
        have henc : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) =
            CookLevin.Lang.strBits x :=
          CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit x) hwf
        rwa [henc, CookLevin.Lang.strBits_length] at h1
      · have hfb : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
          cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
          · rfl
          · exact absurd h hwf
        have hcnf : SATStr.cnfOf x = [[]] :=
          CnfWellFormed.parseTotal_of_not_wf _ hfb
        rw [hcnf]
        simp
    have hclauses : (SATStr.cnfOf x).length ≤ x.length + 1 := by
      by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
      · have henc : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) =
            CookLevin.Lang.strBits x :=
          CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit x) hwf
        have h1 : (SATStr.cnfOf x).length ≤
            (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length := by
          rw [encodeCnf_length]
          exact Nat.le_add_left _ _
        rw [henc, CookLevin.Lang.strBits_length] at h1
        omega
      · have hfb : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
          cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
          · rfl
          · exact absurd h hwf
        have hcnf : SATStr.cnfOf x = [[]] :=
          CnfWellFormed.parseTotal_of_not_wf _ hfb
        rw [hcnf]
        simp
    have hOBr : (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length ≤
        x.length * (x.length + 3) + (x.length + 1) :=
      (encodeCnf_renameCnf_length_le (SATStr.cnfOf x)).trans
        (Nat.add_le_add (Nat.mul_le_mul hL (by omega)) hclauses)
    have hOBr' : (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length ≤
        x.length * x.length + 3 * x.length + (x.length + 1) := by
      have e : x.length * (x.length + 3) = x.length * x.length + 3 * x.length := by
        ring
      omega
    have henclen : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length ≤
        x.length + 1 := by
      by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
      · have henc : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) =
            CookLevin.Lang.strBits x :=
          CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit x) hwf
        rw [henc, CookLevin.Lang.strBits_length]
        omega
      · have hfb : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
          cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
          · rfl
          · exact absurd h hwf
        have hcnf : SATStr.cnfOf x = [[]] :=
          CnfWellFormed.parseTotal_of_not_wf _ hfb
        rw [hcnf]
        have h1 : (EvalCnfCmd.encodeCnf [[]]).length = 1 := by decide
        omega
    have hsize : x.length ≤ encodable.size x := length_le_size x
    have hln : (CookLevin.Lang.strBits x).length = x.length :=
      CookLevin.Lang.strBits_length x
    have hmono8 : occCB * (x.length + 1) ^ 8 ≤
        occCB * (encodable.size x + 1) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
    have hCBbig : (100000 : Nat) ≤ occCB := by
      show 100000 ≤ 100000 * (1 + wfBody.flatK + renameBody.flatK +
        linksBody.flatK + (setZero rSA).flatK + (setZero rSB).flatK +
        (setZero rHAS).flatK +
        (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
        (Cmd.ifBit rSA (setZero rWF) nop).flatK +
        (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
        (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK +
        (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
          Cmd.ifBit rSB (setZero rWF) nop).flatK)
      exact Nat.le_mul_of_pos_right 100000 (by omega)
    have hP9 : (20 : Nat) ≤ occCB * (encodable.size x + 1) ^ 9 := by
      have h1 : (100000 : Nat) * 1 ≤ occCB * (encodable.size x + 1) ^ 9 :=
        Nat.mul_le_mul hCBbig (Nat.one_le_pow 9 _ (by omega))
      omega
    have hmono9 : occCB * (x.length + 1) ^ 9 ≤
        occCB * (encodable.size x + 1) ^ 9 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 9)
    have hB : 12 * (occCB * (x.length + 1) ^ 9) +
          40 * (occCB * (x.length + 1) ^ 8) + 20 ≤
        40 * occCB * (encodable.size x + 1) ^ 9 +
          40 * occCB * (encodable.size x + 1) ^ 8 + 20 := by
      have h1 : 12 * (occCB * (x.length + 1) ^ 9) ≤
          40 * occCB * (encodable.size x + 1) ^ 9 := by
        have e : 12 * (occCB * (x.length + 1) ^ 9) ≤
            12 * (occCB * (encodable.size x + 1) ^ 9) :=
          Nat.mul_le_mul_left _ hmono9
        have e2 : 12 * (occCB * (encodable.size x + 1) ^ 9) ≤
            40 * occCB * (encodable.size x + 1) ^ 9 := by
          have e2a : 12 * (occCB * (encodable.size x + 1) ^ 9) ≤
              40 * (occCB * (encodable.size x + 1) ^ 9) :=
            Nat.mul_le_mul_right _ (by norm_num : (12 : Nat) ≤ 40)
          have e2b : 40 * (occCB * (encodable.size x + 1) ^ 9) =
              40 * occCB * (encodable.size x + 1) ^ 9 := by ring
          rwa [e2b] at e2a
        exact e.trans e2
      have h2 : 40 * (occCB * (x.length + 1) ^ 8) ≤
          40 * occCB * (encodable.size x + 1) ^ 8 := by
        have f : 40 * (occCB * (x.length + 1) ^ 8) ≤
            40 * (occCB * (encodable.size x + 1) ^ 8) :=
          Nat.mul_le_mul_left _ hmono8
        have fb : 40 * (occCB * (encodable.size x + 1) ^ 8) =
            40 * occCB * (encodable.size x + 1) ^ 8 := by ring
        rwa [fb] at f
      exact Nat.add_le_add (Nat.add_le_add h1 h2) (Nat.le_refl 20)
    have hX1 : x.length + 1 ≤ 100 * (x.length + 1) ^ 8 :=
      (Nat.le_self_pow (show (8 : Nat) ≠ 0 by norm_num) _).trans
        (Nat.le_mul_of_pos_left _ (by norm_num))
    have hX3 : (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1 ≤
        100 * (x.length + 1) ^ 8 :=
      xbound3 _ _ hOBr'
    have hX4 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
        (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1 ≤
        100 * (x.length + 1) ^ 8 :=
      xbound4 _ _ _ henclen hOBr'
    have hX5 : 4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
        (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1 ≤
        100 * (x.length + 1) ^ 8 :=
      xbound5 _ _ _ henclen hoccT
    have hX6 : (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
        x.length + 1 ≤ 100 * (x.length + 1) ^ 8 :=
      xbound6 _ _ hoccT
    have h100_5 : (100 : Nat) * 5 ≤ occCB := by
      have h1 : (100000 : Nat) * 5 ≤ occCB := by
        show 100000 * 5 ≤ 100000 * (1 + wfBody.flatK + renameBody.flatK +
          linksBody.flatK + (setZero rSA).flatK + (setZero rSB).flatK +
          (setZero rHAS).flatK +
          (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
          (Cmd.ifBit rSA (setZero rWF) nop).flatK +
          (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
        refine Nat.mul_le_mul_left 100000 ?_
        omega
      have h2 : (100 : Nat) * 5 ≤ 100000 * 5 := by omega
      exact h2.trans h1
    have h100_1 : (100 : Nat) * 1 ≤ occCB := by
      have h1 : (100000 : Nat) * 1 ≤ occCB := by
        show 100000 * 1 ≤ 100000 * (1 + wfBody.flatK + renameBody.flatK +
          linksBody.flatK + (setZero rSA).flatK + (setZero rSB).flatK +
          (setZero rHAS).flatK +
          (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
          (Cmd.ifBit rSA (setZero rWF) nop).flatK +
          (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
        refine Nat.mul_le_mul_left 100000 ?_
        omega
      have h2 : (100 : Nat) * 1 ≤ 100000 * 1 := by omega
      exact h2.trans h1
    cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) with
    | true =>
        have h3WF' : (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))).get rWF =
            [1] := by simp [h3WF, hwf]
        have henc : CookLevin.Lang.strBits x =
            EvalCnfCmd.encodeCnf (SATStr.cnfOf x) :=
          (CnfWellFormed.encodeCnf_parseTotal (CookLevin.Lang.strBits x)
            (CookLevin.Lang.strBits_bit x) hwf).symm
        rw [Cmd.cost_ifBit_true _ _ _ _ h3WF']
        have hTHEN : (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg).cost
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) =
            1 + (Cmd.op (.copy rCUR rIN)).cost
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) +
            (1 + renameProg.cost ((Cmd.op (.copy rCUR rIN)).eval
                (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                  ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) +
              linksProg.cost (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                  ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))) := by
          rw [Cmd.cost_seq, Cmd.cost_seq]
        rw [hTHEN]
        have c4a : (Cmd.op (.copy rCUR rIN)).cost
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) ≤
            5 * (x.length + 1) := by
          have h := (Cmd.cost_le_flat (Cmd.op (.copy rCUR rIN))
            (by simp [Cmd.loopFree]) _ x.length (fun r hr => by
              have heq : (Cmd.op (.copy rCUR rIN)).costReads = [rIN] := by decide
              rw [heq] at hr
              have hr2 : r = rIN := List.mem_singleton.mp hr
              rw [hr2, h3IN, CookLevin.Lang.strBits_length])).1
          exact h
        have h4CUR : ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rCUR =
            EvalCnfCmd.encodeCnf (SATStr.cnfOf x) := by
          rw [copy_get_eq, h3IN]; exact henc
        have h4IN : ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rIN =
            EvalCnfCmd.encodeCnf (SATStr.cnfOf x) := by
          rw [Cmd.eval_get_of_not_writes _ _ _
            (by decide : rIN ∉ Cmd.writes (Cmd.op (.copy rCUR rIN))), h3IN]
          exact henc
        have h4V : ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get
            rVARACC = [] := by
          rw [Cmd.eval_get_of_not_writes _ _ _
            (by decide : rVARACC ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
          exact h3V
        have c4b : renameProg.cost ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) ≤
            (Cmd.op (.clear rJ)).flatK *
                ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) +
              (Cmd.op (.clear rOUT)).flatK *
                ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) +
              (setZero rSA).flatK *
                ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) +
              (setZero rSB).flatK *
                ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) +
              (1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (renameBody.flatK *
                    ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                      (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length +
                      1)) +
                (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) + 4 :=
          renameProg_cost (SATStr.cnfOf x) _ h4CUR h4IN
        obtain ⟨h5OUT, h5IN⟩ := renameProg_eval
          ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))
          (CookLevin.Lang.strBits x) (CookLevin.Lang.strBits_bit x)
          (by rw [copy_get_eq]; exact h3IN) (by
            rw [Cmd.eval_get_of_not_writes _ _ _
              (by decide : rIN ∉ Cmd.writes (Cmd.op (.copy rCUR rIN)))]
            exact h3IN)
        have h5V : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get
            rVARACC = List.replicate 0 1 := by
          rw [Cmd.eval_get_of_not_writes _ _ _
            (by decide : rVARACC ∉ Cmd.writes renameProg)]
          exact h4V
        have h5OUT' : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get
            rOUT = EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x)) := by
          rw [h5OUT, henc]
          exact congrArg Prod.fst (renRun_encodeCnf (SATStr.cnfOf x))
        have h5IN' : (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))).get
            rIN = EvalCnfCmd.encodeCnf (SATStr.cnfOf x) := by
          rw [h5IN]; exact henc
        have c4c : linksProg.cost (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))) ≤
            1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
              ((Cmd.op (.copy rCUR rIN)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rJ2)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rPREV)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rFIRST)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rHAS).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSA).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSB).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (linksBody.flatK *
                    (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                      (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) +
                      1)) +
                  (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                    (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) +
                (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                8) +
              (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length := by
          have h := linksProg_cost (SATStr.cnfOf x)
            (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))
            (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))) 0
            h5IN' h5OUT' h5V
            (by
              rw [occT, encodeCnf_append, List.length_append]
              exact Nat.le_add_right _ _)
            (by omega)
          rwa [h5IN'] at h
        have c5 : (Cmd.op (.copy 0 rOUT)).cost
            ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
              (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) ≤
            5 * ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length + 1) := by
          have h := (Cmd.cost_le_flat (Cmd.op (.copy 0 rOUT))
            (by simp [Cmd.loopFree]) _ ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length) (fun r hr => by
              have heq : (Cmd.op (.copy 0 rOUT)).costReads = [rOUT] := by decide
              rw [heq] at hr
              have hr2 : r = rOUT := List.mem_singleton.mp hr
              rw [hr2]
              have h4 : ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg) (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rOUT = EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x)) := by
                rw [Cmd.eval_ifBit_true _ _ _ _ h3WF']
                simp only [Cmd.eval_seq]
                have h6 := linksProg_eval
                  (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                    (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                      ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))))
                  (SATStr.cnfOf x)
                  (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))) 0
                  h5IN' h5OUT' h5V
                rw [h6.1, range_bridge, ← encodeCnf_append]
                have hoccT : occT 0 (SATStr.cnfOf x) =
                    renameCnf 0 (SATStr.cnfOf x) ++
                      (List.range ((varsList (SATStr.cnfOf x)).sum + 1)).flatMap
                        (fun v => cycleClauses 0 (posOf v (SATStr.cnfOf x))) := rfl
                rw [hoccT]
              rw [h4]
              exact Nat.le_add_right _ _)).1
          exact h
        dsimp only
        rw [hln] at c3
        have t1 : (Cmd.op (.copy rIN 0)).cost (CookLevin.Lang.certState x) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c1 (by
            have := term_le 5 (x.length + 1) h100_5 hX1
            simpa using this))
        have t2 : (Cmd.op (.copy rCUR rIN)).cost
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c2 (by
            have := term_le 5 (x.length + 1) h100_5 hX1
            simpa using this))
        have t3a : (setZero rSA).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t3b : (setZero rSB).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t3c : x.length * (wfBody.flatK * (x.length + 1)) ≤
            occCB * (x.length + 1) ^ 8 := by
          have e : x.length * (wfBody.flatK * (x.length + 1)) =
              wfBody.flatK * (x.length * (x.length + 1)) := by ring
          rw [e]
          exact term_le _ _ (hCB _ (by simp))
            (xbound_mid1 _ _ (Nat.le_add_right _ _))
        have t3d : x.length * x.length ≤ occCB * (x.length + 1) ^ 8 := by
          have e : x.length * x.length = 1 * (x.length * x.length) := by ring
          rw [e]
          exact term_le _ _ h100_1 (xbound_sq _ _ (Nat.le_add_right _ _))
        have t3e : (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
            Cmd.ifBit rSB (setZero rWF) nop).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t4a : (Cmd.op (.copy rCUR rIN)).cost
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c4a (by
            have := term_le 5 (x.length + 1) h100_5 hX1
            simpa using this))
        have t4b1 : (Cmd.op (.clear rJ)).flatK *
            ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.clear rJ)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.clear rJ)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.clear rJ)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.clear rJ)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.clear rJ)).flatK ≤
                100000 * (Cmd.op (.clear rJ)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX3
        have t4b2 : (Cmd.op (.clear rOUT)).flatK *
            ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.clear rOUT)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.clear rOUT)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.clear rOUT)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.clear rOUT)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.clear rOUT)).flatK ≤
                100000 * (Cmd.op (.clear rOUT)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX3
        have t4b3 : (setZero rSA).flatK *
            ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX3
        have t4b4 : (setZero rSB).flatK *
            ((EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX3
        have t4b5 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
            (renameBody.flatK *
              ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length +
                1)) ≤ occCB * (x.length + 1) ^ 8 := by
          have e : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
              (renameBody.flatK *
                ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                  (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length +
                  1)) =
              renameBody.flatK *
                ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (renameCnf 0 (SATStr.cnfOf x))).length +
                    1)) := by ring
          rw [e]
          exact term_le _ _ (hCB _ (by simp)) (xbound_mid2 _ _ _ henclen hOBr')
        have t4b6 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
            (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length ≤
            occCB * (x.length + 1) ^ 8 := by
          have e : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
              (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length =
              1 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) := by ring
          rw [e]
          exact term_le _ _ h100_1 (xbound_sq _ _ henclen)
        have t4c1 : (Cmd.op (.copy rCUR rIN)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.copy rCUR rIN)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.copy rCUR rIN)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.copy rCUR rIN)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.copy rCUR rIN)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.copy rCUR rIN)).flatK ≤
                100000 * (Cmd.op (.copy rCUR rIN)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX5
        have t4c2 : (Cmd.op (.clear rJ2)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.clear rJ2)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.clear rJ2)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.clear rJ2)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.clear rJ2)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.clear rJ2)).flatK ≤
                100000 * (Cmd.op (.clear rJ2)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX5
        have t4c3 : (Cmd.op (.clear rPREV)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.clear rPREV)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.clear rPREV)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.clear rPREV)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.clear rPREV)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.clear rPREV)).flatK ≤
                100000 * (Cmd.op (.clear rPREV)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX5
        have t4c4 : (Cmd.op (.clear rFIRST)).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 := by
          have hF : (100 : Nat) * (Cmd.op (.clear rFIRST)).flatK ≤ occCB := by
            have h1 : (100000 : Nat) * (Cmd.op (.clear rFIRST)).flatK ≤ occCB := by
              show 100000 * (Cmd.op (.clear rFIRST)).flatK ≤
                100000 * (1 + wfBody.flatK + renameBody.flatK + linksBody.flatK +
                  (setZero rSA).flatK + (setZero rSB).flatK + (setZero rHAS).flatK +
                  (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK +
                  (setOne rWF).flatK + (Cmd.ifBit rSA (setZero rWF) nop).flatK +
                  (Cmd.ifBit rSB (setZero rWF) nop).flatK +
                  (emitLink rPREV rFIRST).flatK +
                  (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
              refine Nat.mul_le_mul_left 100000 ?_
              have : (Cmd.op (.clear rFIRST)).flatK = 5 := rfl
              omega
            have h2 : (100 : Nat) * (Cmd.op (.clear rFIRST)).flatK ≤
                100000 * (Cmd.op (.clear rFIRST)).flatK := by omega
            exact h2.trans h1
          exact term_le _ _ hF hX5
        have t4c5 : (setZero rHAS).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX5
        have t4c6 : (setZero rSA).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX5
        have t4c7 : (setZero rSB).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX5
        have t4c8 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
            (linksBody.flatK *
              (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1)) ≤
            occCB * (x.length + 1) ^ 8 := by
          have e : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
              (linksBody.flatK *
                (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                  (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1)) =
              linksBody.flatK *
                ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) +
                    1)) := by ring
          rw [e]
          exact term_le _ _ (hCB _ (by simp)) (xbound_mid3 _ _ _ henclen hoccT)
        have t4c9 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
            (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length ≤
            occCB * (x.length + 1) ^ 8 := t4b6
        have t4c10 : (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
            (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
              (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX5
        have hPB' : ((Cmd.op (.copy rCUR rIN)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rJ2)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rPREV)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rFIRST)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rHAS).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSA).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSB).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (linksBody.flatK *
                    (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                      (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) +
                      1)) +
                  (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                    (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) +
                (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                8) ≤
            10 * (occCB * (x.length + 1) ^ 8) + 9 := by omega
        have hP8ge : (x.length + 1) ≤ occCB * (x.length + 1) ^ 8 :=
          (Nat.le_mul_of_pos_left _ (by omega)).trans
            (Nat.mul_le_mul_left occCB (Nat.le_self_pow (by norm_num) _))
        have hEncPB : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length * ((Cmd.op (.copy rCUR rIN)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rJ2)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rPREV)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rFIRST)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rHAS).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSA).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSB).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (linksBody.flatK *
                    (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                      (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) +
                      1)) +
                  (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                    (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) +
                (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                8) ≤
            10 * (occCB * (x.length + 1) ^ 9) +
              9 * (occCB * (x.length + 1) ^ 8) := by
          calc (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length * ((Cmd.op (.copy rCUR rIN)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rJ2)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rPREV)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (Cmd.op (.clear rFIRST)).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rHAS).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSA).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (setZero rSB).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                (1 + (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (linksBody.flatK *
                    (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                      (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) +
                      1)) +
                  (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                    (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length) +
                (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK *
                  (4 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length +
                    (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length) + 1) +
                8)
              ≤ (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (10 * (occCB * (x.length + 1) ^ 8) + 9) :=
                Nat.mul_le_mul_left _ hPB'
            _ = 10 * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                  (occCB * (x.length + 1) ^ 8)) +
                  9 * (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length := by ring
            _ ≤ 10 * (occCB * (x.length + 1) ^ 9) +
                  9 * (occCB * (x.length + 1) ^ 8) := by
                refine Nat.add_le_add ?_ ?_
                · have e1 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                      (occCB * (x.length + 1) ^ 8) =
                      occCB * ((EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                        (x.length + 1) ^ 8) := by ring
                  have e2 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                      (x.length + 1) ^ 8 ≤ (x.length + 1) * (x.length + 1) ^ 8 :=
                    Nat.mul_le_mul_right _ henclen
                  have e3 : (x.length + 1) * (x.length + 1) ^ 8 =
                      (x.length + 1) ^ 9 := (pow_succ' _ _).symm
                  have h9 : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length *
                      (occCB * (x.length + 1) ^ 8) ≤
                      occCB * (x.length + 1) ^ 9 := by
                    rw [e1]
                    refine (Nat.mul_le_mul_left occCB e2).trans ?_
                    rw [e3]
                  exact Nat.mul_le_mul_left 10 h9
                · exact Nat.mul_le_mul_left 9 (henclen.trans hP8ge)
        have hc4c : linksProg.cost (renameProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))))) ≤
            1 + 10 * (occCB * (x.length + 1) ^ 9) +
              10 * (occCB * (x.length + 1) ^ 8) :=
          c4c.trans (by omega)
        have t5 : (Cmd.op (.copy 0 rOUT)).cost
            ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
              (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c5 (by
            have := term_le 5 ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length + 1) h100_5 hX6
            simpa using this))
        refine (le_trans ?_ hB)
        clear hCB term_le hcost_full
        omega
    | false =>
        have h3WF' : (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))).get rWF ≠
            [1] := by simp [h3WF, hwf]
        rw [Cmd.cost_ifBit_false _ _ _ _ h3WF']
        have c4 : (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).cost
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)))) ≤
            (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK *
              (x.length + 1) := by
          have h := (Cmd.cost_le_flat
            (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))
            (by simp [Cmd.loopFree])
            (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
              ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))
            x.length (fun r hr => by
              simp [Cmd.costReads, Op.costReads] at hr)).1
          exact h
        have c5 : (Cmd.op (.copy 0 rOUT)).cost
            ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
              (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) ≤
            5 * ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length + 1) := by
          have h := (Cmd.cost_le_flat (Cmd.op (.copy 0 rOUT))
            (by simp [Cmd.loopFree]) _ ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length) (fun r hr => by
              have heq : (Cmd.op (.copy 0 rOUT)).costReads = [rOUT] := by decide
              rw [heq] at hr
              have hr2 : r = rOUT := List.mem_singleton.mp hr
              rw [hr2]
              have h4 : ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg) (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))).get rOUT = [0] := by
                rw [Cmd.eval_ifBit_false _ _ _ _ h3WF']
                simp [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq,
                  State.get_set_ne]
              rw [h4]
              have hocc1 : (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length =
                  1 := by
                have hcnf : SATStr.cnfOf x = [[]] :=
                  CnfWellFormed.parseTotal_of_not_wf _ hwf
                rw [hcnf]
                decide
              show (1 : Nat) ≤ (EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
                x.length
              omega)).1
          exact h
        dsimp only
        rw [hln] at c3
        have t1 : (Cmd.op (.copy rIN 0)).cost (CookLevin.Lang.certState x) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c1 (by
            have := term_le 5 (x.length + 1) h100_5 hX1
            simpa using this))
        have t2 : (Cmd.op (.copy rCUR rIN)).cost
            ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x)) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c2 (by
            have := term_le 5 (x.length + 1) h100_5 hX1
            simpa using this))
        have t3a : (setZero rSA).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t3b : (setZero rSB).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t3c : x.length * (wfBody.flatK * (x.length + 1)) ≤
            occCB * (x.length + 1) ^ 8 := by
          have e : x.length * (wfBody.flatK * (x.length + 1)) =
              wfBody.flatK * (x.length * (x.length + 1)) := by ring
          rw [e]
          exact term_le _ _ (hCB _ (by simp))
            (xbound_mid1 _ _ (Nat.le_add_right _ _))
        have t3d : x.length * x.length ≤ occCB * (x.length + 1) ^ 8 := by
          have e : x.length * x.length = 1 * (x.length * x.length) := by ring
          rw [e]
          exact term_le _ _ h100_1 (xbound_sq _ _ (Nat.le_add_right _ _))
        have t3e : (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;;
            Cmd.ifBit rSB (setZero rWF) nop).flatK * (x.length + 1) ≤
            occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t4 : (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK *
            (x.length + 1) ≤ occCB * (x.length + 1) ^ 8 :=
          term_le _ _ (hCB _ (by simp)) hX1
        have t5 : (Cmd.op (.copy 0 rOUT)).cost
            ((Cmd.ifBit rWF (Cmd.op (.copy rCUR rIN) ;; renameProg ;; linksProg)
              (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT))).eval
              (wfProg.eval ((Cmd.op (.copy rCUR rIN)).eval
                ((Cmd.op (.copy rIN 0)).eval (CookLevin.Lang.certState x))))) ≤
            occCB * (x.length + 1) ^ 8 :=
          (le_trans c5 (by
            have := term_le 5 ((EvalCnfCmd.encodeCnf (occT 0 (SATStr.cnfOf x))).length +
              x.length + 1) h100_5 hX6
            simpa using this))
        refine (le_trans ?_ hB)
        clear hCB term_le hcost_full
        omega
  · intro x
    by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
    · have h1 : encodable.size (occMap x) ≤ 2 * (occMap x).length :=
        size_le_two_mul_length _
      have h2 := occMap_length_le x hwf
      have h3 : x.length ≤ encodable.size x := length_le_size x
      have hCB1000 : (100000 : Nat) ≤ occCB := by
        show 100000 ≤ 100000 * (1 + wfBody.flatK + renameBody.flatK +
          linksBody.flatK + (setZero rSA).flatK + (setZero rSB).flatK +
          (setZero rHAS).flatK +
          (Cmd.ifBit rHAS (emitLink rPREV rFIRST) nop).flatK + (setOne rWF).flatK +
          (Cmd.ifBit rSA (setZero rWF) nop).flatK +
          (Cmd.ifBit rSB (setZero rWF) nop).flatK + (emitLink rPREV rFIRST).flatK +
          (Cmd.op (.clear rOUT) ;; Cmd.op (.appendZero rOUT)).flatK + (setOne rWF ;; Cmd.ifBit rSA (setZero rWF) nop ;; Cmd.ifBit rSB (setZero rWF) nop).flatK)
        refine Nat.le_mul_of_pos_right 100000 ?_
        omega
      have hpow : (x.length + 1) ^ 4 ≤ (encodable.size x + 1) ^ 9 :=
        (Nat.pow_le_pow_left (by omega) 4).trans
          (Nat.pow_le_pow_right (by omega) (by norm_num))
      have hchain : 2 * (occMap x).length ≤ 40 * occCB * (encodable.size x + 1) ^ 9 +
          40 * occCB * (encodable.size x + 1) ^ 8 + 20 := by
        have e1 : (100000 : Nat) * (x.length + 1) ^ 4 ≤
            occCB * (encodable.size x + 1) ^ 9 :=
          (Nat.mul_le_mul_left 100000 hpow).trans
            (Nat.mul_le_mul_right _ hCB1000)
        have e2 : (100000 : Nat) * (x.length + 1) ^ 4 ≥ 2 * (20 * (x.length + 1) ^ 4 + 1) := by
          have hP : (1 : Nat) ≤ (x.length + 1) ^ 4 :=
            Nat.one_le_pow 4 (x.length + 1) (by omega)
          omega
        have e3 : 2 * (occMap x).length ≤ 2 * (20 * (x.length + 1) ^ 4 + 1) := by
          omega
        have e1' : (100000 : Nat) * (x.length + 1) ^ 4 ≤
            40 * occCB * (encodable.size x + 1) ^ 9 := by
          have e1b : occCB * (encodable.size x + 1) ^ 9 ≤
              40 * occCB * (encodable.size x + 1) ^ 9 :=
            Nat.mul_le_mul_right _
              (Nat.le_mul_of_pos_left occCB (by norm_num : (0 : Nat) < 40))
          exact e1.trans e1b
        exact e3.trans (e2.trans (e1'.trans
          ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))
      dsimp only
      exact h1.trans hchain
    · have hfb : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = false := by
        cases h : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
        · rfl
        · exact absurd h hwf
      have hocc : occMap x = [false] := by simp [occMap, hfb]
      rw [hocc]
      have h1 : encodable.size [false] ≤ 2 := by
        have := size_le_two_mul_length [false]
        simpa using this
      dsimp only
      have h20 : (20 : Nat) ≤ 40 * occCB * (encodable.size x + 1) ^ 9 +
          40 * occCB * (encodable.size x + 1) ^ 8 + 20 := Nat.le_add_left _ _
      omega


/-- The reduction program as a polynomial-time computable language. -/
noncomputable def occPolyLang : CookLevin.Lang.PolyTimeComputableLang occMap where
  c := occCmd
  encodeIn := CookLevin.Lang.certState
  decodeOut := fun s => CookLevin.Lang.boolsOf (s.get 0)
  cost_bound := occCmd_cost.choose
  cost_bound_poly := occCmd_cost.choose_spec.1
  cost_bound_mono := occCmd_cost.choose_spec.2.1
  encBound := id
  encBound_poly := inOPoly_id
  encBound_mono := fun _ _ h => h
  encodeIn_size := fun x => by
    rw [CookLevin.Lang.State.size_certState]
    exact length_le_size x
  computes := fun x => by
    rw [occCmd_get0]
    exact boolsOf_strBits (occMap x)
  cost_le := occCmd_cost.choose_spec.2.2.1
  output_size_le := occCmd_cost.choose_spec.2.2.2
  enc_bit := fun x => by
    intro reg hreg z hz
    simp only [CookLevin.Lang.certState, List.mem_singleton] at hreg
    subst hreg
    exact CookLevin.Lang.strBits_bit x z hz
  regBound := 26
  usesBelow := occCmd_usesBelow
  width_le := fun x => by simp [CookLevin.Lang.certState]
  decode_agree := fun x m => by
    have hagr : CookLevin.Lang.AgreeBelow 26
        (CookLevin.Lang.certState x ++ List.replicate m [])
        (CookLevin.Lang.certState x) := fun r _ =>
      CookLevin.Lang.State.get_append_replicate_nil
        (CookLevin.Lang.certState x) m r
    have hev := Cmd.eval_agree occCmd 26 occCmd_usesBelow hagr
    rw [hev 0 (by omega)]

end PvsNP.Units.M3OccAux

theorem PvsNP.Units.m3_sat_to_3occ_sat :
    CookLevin.reducesPoly SATStr
      (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
        SAT (SATStr.cnfOf x)) := by
  obtain ⟨t, M, ht, hM, h1, hcomp⟩ :=
    PvsNP.Units.M3OccAux.occPolyLang.toMachine
      (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨PvsNP.Units.M3OccAux.occMap, t, M, ht, hM, h1, hcomp,
    PvsNP.Units.M3OccAux.occMap_iff⟩
