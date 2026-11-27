import Mathlib
import PvsNP.Defs
import CookLevin

/-- Prove that for any language `L : Language Bool`, `L` is NP-hard if and only if for every language `L'` in coNP, `L'` is Karp-reducible to the complement of `L` (`Lᶜ`). -/
theorem PvsNP.Units.m2_nphard_iff_compl_conphard :
    ∀ L : Language Bool, PvsNP.NPHard L ↔ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
  intro L
  have h_imp : PvsNP.NPHard L → (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ) := by
    intro h_nphard L' hL'
    have h₁ : L'ᶜ ∈ PvsNP.NP := by
      simpa [PvsNP.coNP, Set.mem_compl_iff] using hL'
    have h₂ : PvsNP.KarpReducible L'ᶜ L := h_nphard L'ᶜ h₁
    rcases h₂ with ⟨f, hf, hL⟩
    have h₃ : PvsNP.KarpReducible L' Lᶜ := by
      refine' ⟨f, hf, _⟩
      intro x
      have h₅ : x ∈ L' ↔ x ∉ L'ᶜ := not_not.symm
      have h₆ : f x ∈ Lᶜ ↔ f x ∉ L := Iff.rfl
      have h₇ : x ∈ L' ↔ f x ∈ Lᶜ := by
        calc
          x ∈ L' ↔ x ∉ L'ᶜ := by rw [h₅]
          _ ↔ ¬(x ∈ L'ᶜ) := by simp
          _ ↔ ¬(f x ∈ L) := by
            have h₈ : x ∈ L'ᶜ ↔ f x ∈ L := hL x
            rw [h₈]
            <;> simp
          _ ↔ f x ∉ L := by simp
          _ ↔ f x ∈ Lᶜ := by rw [h₆]
      exact h₇
    exact h₃
  have h_conv : (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ) → PvsNP.NPHard L := by
    intro h_conp L' hL'
    have h₁ : L'ᶜ ∈ PvsNP.coNP := by
      simpa [PvsNP.coNP, Set.mem_compl_iff] using hL'
    have h₂ : PvsNP.KarpReducible L'ᶜ Lᶜ := h_conp L'ᶜ h₁
    rcases h₂ with ⟨f, hf, hL⟩
    have h₃ : PvsNP.KarpReducible L' L := by
      refine' ⟨f, hf, _⟩
      intro x
      have h₅ : x ∈ L' ↔ x ∉ L'ᶜ := not_not.symm
      have h₆ : f x ∈ L ↔ f x ∉ Lᶜ := not_not.symm
      have h₇ : x ∈ L' ↔ f x ∈ L := by
        calc
          x ∈ L' ↔ x ∉ L'ᶜ := by rw [h₅]
          _ ↔ ¬(x ∈ L'ᶜ) := by simp
          _ ↔ ¬(f x ∈ Lᶜ) := by
            have h₈ : x ∈ L'ᶜ ↔ f x ∈ Lᶜ := hL x
            rw [h₈]
            <;> simp
          _ ↔ f x ∉ Lᶜ := by simp
          _ ↔ f x ∈ L := by rw [h₆]
      exact h₇
    exact h₃
  have h_main : PvsNP.NPHard L ↔ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
    constructor
    · intro h
      exact h_imp h
    · intro h
      exact h_conv h
  exact h_main
