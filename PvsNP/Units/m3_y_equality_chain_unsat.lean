import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_equality_chain_unsat_aux

theorem mem_of_evalLiteral_true {a : assgn} {v : var}
    (h : evalLiteral a (true, v) = true) : v ∈ a := by
  simp [evalLiteral, evalVar] at h
  exact h

theorem not_mem_of_evalLiteral_false {a : assgn} {v : var}
    (h : evalLiteral a (false, v) = true) : v ∉ a := by
  simp [evalLiteral, evalVar] at h
  exact h

end PvsNP.Units.m3_y_equality_chain_unsat_aux

open PvsNP.Units.m3_y_equality_chain_unsat_aux

theorem PvsNP.Units.m3_y_equality_chain_unsat :
    ∀ n : ℕ, ¬ SAT ([(true, 0)] :: [(false, n)] ::
      (List.range n).flatMap (fun i => [[(false, i), (true, i + 1)], [(true, i), (false, i + 1)]])) := by
  intro n ⟨a, ha⟩
  have ha' : evalCnf a ([(true, 0)] :: [(false, n)] ::
      (List.range n).flatMap (fun i => [[(false, i), (true, i + 1)], [(true, i), (false, i + 1)]])) = true := ha
  rw [evalCnf_clause_iff] at ha'
  -- The unit clause `[(true, 0)]` forces `0 ∈ a`.
  have h0 : (0 : var) ∈ a := by
    have h := ha' [(true, 0)] (by simp)
    rw [evalClause_literal_iff] at h
    obtain ⟨l, hl, hlt⟩ := h
    simp at hl
    subst hl
    exact mem_of_evalLiteral_true hlt
  -- The unit clause `[(false, n)]` forces `n ∉ a`.
  have hn : (n : var) ∉ a := by
    have h := ha' [(false, n)] (by simp)
    rw [evalClause_literal_iff] at h
    obtain ⟨l, hl, hlt⟩ := h
    simp at hl
    subst hl
    exact not_mem_of_evalLiteral_false hlt
  -- Each equivalence link `i ↔ i + 1` propagates membership forward.
  have hstep : ∀ i, i < n → i ∈ a → i + 1 ∈ a := by
    intro i hi hia
    have hmem : [(false, i), (true, i + 1)] ∈
        (List.range n).flatMap (fun i => [[(false, i), (true, i + 1)], [(true, i), (false, i + 1)]]) := by
      rw [List.mem_flatMap]
      exact ⟨i, List.mem_range.mpr hi, by simp⟩
    have h := ha' [(false, i), (true, i + 1)] (by simp [hmem])
    rw [evalClause_literal_iff] at h
    obtain ⟨l, hl, hlt⟩ := h
    simp at hl
    rcases hl with rfl | rfl
    · exact absurd hia (not_mem_of_evalLiteral_false hlt)
    · exact mem_of_evalLiteral_true hlt
  -- Induction along the chain: `0 ∈ a` gives `n ∈ a`, contradiction.
  have hall : ∀ k, k ≤ n → k ∈ a := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
        intro hk
        exact hstep k (by omega) (ih (by omega))
  exact hn (hall n le_rfl)
