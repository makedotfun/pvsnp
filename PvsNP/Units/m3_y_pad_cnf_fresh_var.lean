import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_pad_cnf_fresh_var

lemma evalClause_snoc (a : assgn) (C : clause) (l : literal) :
    evalClause a (C ++ [l]) = true ↔ evalClause a C = true ∨ evalLiteral a l = true := by
  simp only [evalClause_literal_iff, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨x, hx | rfl, ht⟩
    · exact Or.inl ⟨x, hx, ht⟩
    · exact Or.inr ht
  · rintro (⟨x, hx, ht⟩ | ht)
    · exact ⟨x, Or.inl hx, ht⟩
    · exact ⟨l, Or.inr rfl, ht⟩

end PvsNP.Units.m3_y_pad_cnf_fresh_var

theorem PvsNP.Units.m3_y_pad_cnf_fresh_var :
    ∀ (N : cnf) (k : ℕ) (z : var), (∀ C ∈ N, C.length ≤ k) →
      (∀ C ∈ N.flatMap (fun C => [C ++ [(true, z)], C ++ [(false, z)]]), C.length ≤ k + 1) ∧
        (SAT (N.flatMap (fun C => [C ++ [(true, z)], C ++ [(false, z)]])) ↔ SAT N) := by
  intro N k z hlen
  refine ⟨?_, ?_⟩
  · intro C' hC'
    rw [List.mem_flatMap] at hC'
    rcases hC' with ⟨C, hC, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> { simp only [List.length_append, List.length_singleton]; exact Nat.add_le_add_right (hlen C hC) 1 }
  · constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff] at ha ⊢
      intro C hC
      have h1 : C ++ [(true, z)] ∈ N.flatMap (fun D => [D ++ [(true, z)], D ++ [(false, z)]]) :=
        List.mem_flatMap.mpr ⟨C, hC, by simp⟩
      have h2 : C ++ [(false, z)] ∈ N.flatMap (fun D => [D ++ [(true, z)], D ++ [(false, z)]]) :=
        List.mem_flatMap.mpr ⟨C, hC, by simp⟩
      have e1 := (PvsNP.Units.m3_y_pad_cnf_fresh_var.evalClause_snoc a C (true, z)).mp (ha _ h1)
      have e2 := (PvsNP.Units.m3_y_pad_cnf_fresh_var.evalClause_snoc a C (false, z)).mp (ha _ h2)
      by_cases hz : z ∈ a
      · have hf : evalLiteral a (false, z) ≠ true := by simp [evalLiteral, evalVar, hz]
        exact e2.resolve_right hf
      · have ht : evalLiteral a (true, z) ≠ true := by simp [evalLiteral, evalVar, hz]
        exact e1.resolve_right ht
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [satisfiesCnf, evalCnf_clause_iff] at ha ⊢
      intro C' hC'
      rw [List.mem_flatMap] at hC'
      rcases hC' with ⟨C, hC, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact (PvsNP.Units.m3_y_pad_cnf_fresh_var.evalClause_snoc a C (true, z)).mpr (Or.inl (ha C hC))
      · exact (PvsNP.Units.m3_y_pad_cnf_fresh_var.evalClause_snoc a C (false, z)).mpr (Or.inl (ha C hC))
