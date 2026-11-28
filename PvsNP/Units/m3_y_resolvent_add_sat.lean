import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_resolvent_add_sat :
    ∀ (N : cnf) (C D : clause) (v : var), C ∈ N → D ∈ N → (true, v) ∈ C → (false, v) ∈ D →
      (SAT ((C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v)))) :: N) ↔ SAT N) := by
  intro N C D v hCN hDN _ _
  constructor
  · rintro ⟨a, ha⟩
    have hall := (evalCnf_clause_iff a _).mp ha
    exact ⟨a, (evalCnf_clause_iff a N).mpr (fun E hE => hall E (List.mem_cons_of_mem _ hE))⟩
  · rintro ⟨a, ha⟩
    have hall := (evalCnf_clause_iff a N).mp ha
    refine ⟨a, (evalCnf_clause_iff a _).mpr ?_⟩
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hEN
    · refine (evalClause_literal_iff a _).mpr ?_
      by_cases hv : v ∈ a
      · obtain ⟨l, hlD, hlit⟩ := (evalClause_literal_iff a D).mp (hall D hDN)
        have hne : l ≠ (false, v) := by
          rintro rfl
          simp [evalLiteral, evalVar, hv] at hlit
        exact ⟨l, List.mem_append_right _ (List.mem_filter.mpr ⟨hlD, by simp [hne]⟩), hlit⟩
      · obtain ⟨l, hlC, hlit⟩ := (evalClause_literal_iff a C).mp (hall C hCN)
        have hne : l ≠ (true, v) := by
          rintro rfl
          simp [evalLiteral, evalVar, hv] at hlit
        exact ⟨l, List.mem_append_left _ (List.mem_filter.mpr ⟨hlC, by simp [hne]⟩), hlit⟩
    · exact hall E hEN
