import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_union

theorem PvsNP.Units.m2_z_p_range_union :
    ∀ (F : ℕ → Language Bool) (m : ℕ), (∀ i < m, F i ∈ PvsNP.P) →
      ({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ∈ PvsNP.P := by
  intro F m
  induction m with
  | zero =>
    intro _
    have hEq : ({x : List Bool | ∃ i < 0, x ∈ F i} : Language Bool) = (∅ : Set (List Bool)) := by
      ext x; simp
    rw [hEq]
    exact PvsNP.Units.m2_p_trivial.1
  | succ m ih =>
    intro hF
    have hprev := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have hlast := hF m (Nat.lt_succ_self m)
    have hUni := PvsNP.Units.m2_p_union _ _ hprev hlast
    have hEq : (({x : List Bool | ∃ i < m, x ∈ F i} : Language Bool) ⊔ F m) =
        ({x : List Bool | ∃ i < m + 1, x ∈ F i} : Language Bool) := by
      ext x
      show (∃ i < m, x ∈ F i) ∨ x ∈ F m ↔ ∃ i < m + 1, x ∈ F i
      constructor
      · rintro (⟨i, hi, hx⟩ | hx)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
        · exact ⟨m, Nat.lt_succ_self m, hx⟩
      · rintro ⟨i, hi, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl ⟨i, hlt, hx⟩
        · exact Or.inr hx
    rw [← hEq]
    exact hUni
