import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_z_np_eq_conp_iff_inter_conp
import PvsNP.Units.m2_z_np_conp_range_closure

theorem PvsNP.Units.m2_z_np_eq_conp_iff_symm_diff : PvsNP.NP = PvsNP.coNP ↔ ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
  ({x : List Bool | (x ∈ L₁ ∧ x ∉ L₂) ∨ (x ∈ L₂ ∧ x ∉ L₁)} : Language Bool) ∈ PvsNP.NP := by
  constructor
  · intro h L₁ L₂ h1 h2
    have h1c : L₁ᶜ ∈ PvsNP.NP := by
      rw [h]
      show (L₁ᶜ)ᶜ ∈ PvsNP.NP
      rw [compl_compl]
      exact h1
    have h2c : L₂ᶜ ∈ PvsNP.NP := by
      rw [h]
      show (L₂ᶜ)ᶜ ∈ PvsNP.NP
      rw [compl_compl]
      exact h2
    have h_eq : ({x : List Bool | (x ∈ L₁ ∧ x ∉ L₂) ∨ (x ∈ L₂ ∧ x ∉ L₁)} : Language Bool) =
        (L₁ ⊓ L₂ᶜ) ⊔ (L₂ ⊓ L₁ᶜ) := rfl
    rw [h_eq]
    exact PvsNP.Units.m2_np_union _ _ (PvsNP.Units.m2_np_inter _ _ h1 h2c) (PvsNP.Units.m2_np_inter _ _ h2 h1c)
  · intro h
    have hTop : (⊤ : Language Bool) ∈ PvsNP.NP := by
      show (Set.univ : Language Bool) ∈ PvsNP.NP
      exact PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.2
    have hNP_sub : PvsNP.NP ⊆ PvsNP.coNP := by
      intro L hL
      show Lᶜ ∈ PvsNP.NP
      have h_eq : Lᶜ = ({x : List Bool | (x ∈ (⊤ : Language Bool) ∧ x ∉ L) ∨ (x ∈ L ∧ x ∉ (⊤ : Language Bool))} : Language Bool) := by
        ext x
        constructor
        · intro hx
          exact Or.inl ⟨Set.mem_univ x, hx⟩
        · rintro (⟨_, hx⟩ | ⟨_, htop⟩)
          · exact hx
          · exact False.elim (htop (Set.mem_univ x))
      rw [h_eq]
      exact h ⊤ L hTop hL
    apply Set.Subset.antisymm hNP_sub
    intro L hL
    have hLc : Lᶜ ∈ PvsNP.NP := hL
    have hLcc : (Lᶜ)ᶜ ∈ PvsNP.NP := hNP_sub hLc
    rwa [compl_compl] at hLcc
