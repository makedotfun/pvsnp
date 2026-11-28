import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_trivial

theorem PvsNP.Units.m2_z_np_eq_conp_iff_union_conp :
    PvsNP.NP = PvsNP.coNP ↔ ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.coNP → L₁ ⊔ L₂ ∈ PvsNP.NP := by
  constructor
  · intro h L₁ L₂ h₁ h₂
    exact PvsNP.Units.m2_np_union L₁ L₂ h₁ (h ▸ h₂)
  · intro h
    have hempty : (⊥ : Language Bool) ∈ PvsNP.NP :=
      PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.1
    have hsub : ∀ L, L ∈ PvsNP.coNP → L ∈ PvsNP.NP := by
      intro L hL
      have := h ⊥ L hempty hL
      rwa [bot_sup_eq] at this
    apply Set.Subset.antisymm
    · intro L hL
      show Lᶜ ∈ PvsNP.NP
      apply hsub
      show Lᶜᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    · exact hsub
