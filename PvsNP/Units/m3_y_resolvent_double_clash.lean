import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_resolvent_double_clash :
    ∀ (C D : clause) (v w : var) (a : assgn), v ≠ w → (true, v) ∈ C → (false, v) ∈ D → (true, w) ∈ C → (false, w) ∈ D →
      evalClause a (C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v)))) = true := by
  intro C D v w a hne _ _ htw hfw
  refine (evalClause_literal_iff a _).mpr ?_
  by_cases hw : w ∈ a
  · refine ⟨(true, w), List.mem_append_left _ (List.mem_filter.mpr ⟨htw, ?_⟩), ?_⟩
    · simp only [decide_eq_true_eq, ne_eq, Prod.mk.injEq, true_and]
      exact hne.symm
    · simp [evalLiteral, evalVar, hw]
  · refine ⟨(false, w), List.mem_append_right _ (List.mem_filter.mpr ⟨hfw, ?_⟩), ?_⟩
    · simp only [decide_eq_true_eq, ne_eq, Prod.mk.injEq, true_and]
      exact hne.symm
    · simp [evalLiteral, evalVar, hw]
