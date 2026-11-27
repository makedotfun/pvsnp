import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_grid_monotone_unsat

lemma imp_clause_iff (a : assgn) (u v : ℕ) :
    evalClause a [(false, u), (true, v)] = true ↔ (u ∈ a → v ∈ a) := by
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    evalLiteral, evalVar, decide_eq_true_eq]
  by_cases hu : u ∈ a <;> by_cases hv : v ∈ a <;> simp [hu, hv]

end PvsNP.Units.m3_y_grid_monotone_unsat

theorem PvsNP.Units.m3_y_grid_monotone_unsat :
    ∀ m n : ℕ,
      ¬ SAT ([(true, 0)] :: [(false, m * (n + 1) + n)] ::
        ((List.range m).flatMap (fun i => (List.range (n + 1)).map (fun j =>
            [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)])) ++
          (List.range (m + 1)).flatMap (fun i => (List.range n).map (fun j =>
            [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)])))) := by
  rintro m n ⟨a, ha⟩
  simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha
  rcases ha with ⟨h0c, hgoal, hrest⟩
  have hrest' : evalCnf a
      ((List.range m).flatMap (fun i => (List.range (n + 1)).map (fun j =>
          [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)])) ++
        (List.range (m + 1)).flatMap (fun i => (List.range n).map (fun j =>
          [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)]))) = true := hrest
  rw [evalCnf_app_iff] at hrest'
  rcases hrest' with ⟨hdown, hright⟩
  rw [evalCnf_clause_iff] at hdown hright
  have h0 : 0 ∈ a := by
    obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff a [(true, 0)]).mp h0c
    simp only [List.mem_singleton] at hl
    subst hl
    by_contra hnot
    simp [evalLiteral, evalVar, hnot] at ht
  have hmn_not : m * (n + 1) + n ∉ a := by
    obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff a [(false, m * (n + 1) + n)]).mp hgoal
    simp only [List.mem_singleton] at hl
    subst hl
    intro hin
    simp [evalLiteral, evalVar, hin] at ht
  have hcol0 : ∀ i ≤ m, i * (n + 1) + 0 ∈ a := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have hi0 : i * (n + 1) + 0 ∈ a := ih (by omega)
      have hcl : evalClause a [(false, i * (n + 1) + 0), (true, (i + 1) * (n + 1) + 0)] = true := by
        apply hdown
        simp only [List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨i, by omega, 0, by omega, rfl⟩
      exact (PvsNP.Units.m3_y_grid_monotone_unsat.imp_clause_iff a _ _).mp hcl hi0
  have hrowm : ∀ j ≤ n, m * (n + 1) + j ∈ a := by
    intro j hj
    induction j with
    | zero => exact hcol0 m le_rfl
    | succ j ih =>
      have hmj : m * (n + 1) + j ∈ a := ih (by omega)
      have hcl : evalClause a [(false, m * (n + 1) + j), (true, m * (n + 1) + j + 1)] = true := by
        apply hright
        simp only [List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨m, by omega, j, by omega, rfl⟩
      have hstep := (PvsNP.Units.m3_y_grid_monotone_unsat.imp_clause_iff a _ _).mp hcl hmj
      have heq : m * (n + 1) + j + 1 = m * (n + 1) + (j + 1) := by omega
      rwa [← heq]
  exact hmn_not (hrowm n le_rfl)
