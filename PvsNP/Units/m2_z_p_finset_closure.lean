import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_union
import PvsNP.Units.m2_p_inter

theorem PvsNP.Units.m2_z_p_finset_closure :
    ∀ (S : Finset ℕ) (F : ℕ → Language Bool), (∀ i ∈ S, F i ∈ PvsNP.P) →
      ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.P ∧ ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool) ∈ PvsNP.P := by
  intro S F
  induction S using Finset.induction_on with
  | empty =>
    intro _
    constructor
    · have hEq : ({x : List Bool | ∃ i ∈ (∅ : Finset ℕ), x ∈ F i} : Language Bool) = (∅ : Set (List Bool)) := by
        ext x; simp
      rw [hEq]
      exact PvsNP.Units.m2_p_trivial.1
    · have hEq : ({x : List Bool | ∀ i ∈ (∅ : Finset ℕ), x ∈ F i} : Language Bool) = (Set.univ : Set (List Bool)) := by
        ext x; simp
      rw [hEq]
      exact PvsNP.Units.m2_p_trivial.2
  | @insert a S ha ih =>
    intro hF
    obtain ⟨hpu, hpi⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have haF := hF a (Finset.mem_insert_self a S)
    constructor
    · have hUni := PvsNP.Units.m2_p_union _ _ haF hpu
      have hEq : (F a ⊔ ({x : List Bool | ∃ i ∈ S, x ∈ F i} : Language Bool)) =
          ({x : List Bool | ∃ i ∈ insert a S, x ∈ F i} : Language Bool) := by
        ext x
        show x ∈ F a ∨ (∃ i ∈ S, x ∈ F i) ↔ ∃ i ∈ insert a S, x ∈ F i
        simp [Finset.mem_insert]
      rw [← hEq]
      exact hUni
    · have hInt := PvsNP.Units.m2_p_inter _ _ haF hpi
      have hEq : (F a ⊓ ({x : List Bool | ∀ i ∈ S, x ∈ F i} : Language Bool)) =
          ({x : List Bool | ∀ i ∈ insert a S, x ∈ F i} : Language Bool) := by
        ext x
        show x ∈ F a ∧ (∀ i ∈ S, x ∈ F i) ↔ ∀ i ∈ insert a S, x ∈ F i
        simp [Finset.mem_insert]
      rw [← hEq]
      exact hInt
