import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_diff
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np

/-
`m2_z_p_eq_np_iff_diff_p`: P = NP iff NP is closed under set difference.

Proof idea.
- Forward: if P = NP, rewrite every NP-membership as P-membership and apply the
  settled `m2_p_diff` (P is closed under set difference).
- Backward: take L₂ = ∅. The empty language is in P (`m2_p_trivial`) hence in NP
  (`m2_p_subset_np`), so the difference hypothesis gives
  `{x | x ∈ L₁ ∧ x ∉ ∅} = L₁ ∈ P` for every L₁ ∈ NP, i.e. NP ⊆ P; together with
  `m2_p_subset_np` (P ⊆ NP) this gives P = NP.
-/

theorem PvsNP.Units.m2_z_p_eq_np_iff_diff_p :
    PvsNP.P = PvsNP.NP ↔ ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
      ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) ∈ PvsNP.P := by
  constructor
  · intro h L₁ L₂ h₁ h₂
    rw [← h] at h₁ h₂
    exact PvsNP.Units.m2_p_diff L₁ L₂ h₁ h₂
  · intro hdiff
    refine Set.Subset.antisymm PvsNP.Units.m2_p_subset_np ?_
    intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ PvsNP.NP :=
      PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.1
    have h := hdiff L (∅ : Set (List Bool)) hL hempty
    have heq : ({x : List Bool | x ∈ L ∧ x ∉ (∅ : Set (List Bool))} : Language Bool) = L := by
      ext x
      exact ⟨fun hh => hh.1, fun hh => ⟨hh, by simp⟩⟩
    rw [← heq]
    exact h
