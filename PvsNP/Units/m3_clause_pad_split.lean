import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_clause_pad_split

/-- Appending one literal to a clause: the evaluation is the old one, or the
new literal's. -/
theorem evalClause_append_singleton (a : assgn) (C : clause) (l : literal) :
    evalClause a (C ++ [l]) = (evalClause a C || evalLiteral a l) := by
  unfold evalClause
  rw [List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem statement : ∀ (N : cnf) (C : clause) (z : var),
    SAT ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) ↔ SAT (C :: N) := by
  intro N C z
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (C :: N) = true
    have ha' : evalCnf a ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    rw [evalCnf_clause_iff]
    have ha := ha'
    have h1 := ha _ List.mem_cons_self
    have h2 := ha _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hN : ∀ E ∈ N, evalClause a E = true :=
      fun E hE => ha E (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hE))
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h]
      rw [evalClause_append_singleton] at h1 h2
      rcases (Bool.or_eq_true_iff.mp h1) with hC | ht
      · exact hC
      · rcases (Bool.or_eq_true_iff.mp h2) with hC | hf
        · exact hC
        · exfalso
          have hzt : evalVar a z = true := of_decide_eq_true ht
          have hzf : evalVar a z = false := of_decide_eq_true hf
          rw [hzt] at hzf
          exact Bool.noConfusion hzf
    · exact hN E hE
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) = true
    have ha' : evalCnf a (C :: N) = true := ha
    rw [evalCnf_clause_iff] at ha'
    rw [evalCnf_clause_iff]
    have ha := ha'
    intro E hE
    rcases List.mem_cons.mp hE with h | hE
    · rw [h, evalClause_append_singleton]
      have hC := ha C List.mem_cons_self
      simp [hC]
    · rcases List.mem_cons.mp hE with h | hE
      · rw [h, evalClause_append_singleton]
        have hC := ha C List.mem_cons_self
        simp [hC]
      · exact ha E (List.mem_cons_of_mem _ hE)

end PvsNP.Units.m3_clause_pad_split

/-- Splitting a clause on a fresh padding literal (both signs) preserves satisfiability. -/
theorem PvsNP.Units.m3_clause_pad_split : ∀ (N : cnf) (C : clause) (z : var),
    SAT ((C ++ [(true, z)]) :: (C ++ [(false, z)]) :: N) ↔ SAT (C :: N) :=
  PvsNP.Units.m3_clause_pad_split.statement
