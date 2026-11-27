import Mathlib
import PvsNP.Defs
import CookLevin

/-- A language is NP-hard if and only if every coNP language Karp-reduces to its
complement: the same reduction function works on both sides, because reducing the
complement of `L'` to `L` and reducing `L'` to the complement of `L` are the same
pointwise statement read contrapositively. -/
theorem PvsNP.Units.m2_nphard_iff_compl_conphard :
    ∀ L : Language Bool, PvsNP.NPHard L ↔
      ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
  have key : ∀ (M : Language Bool) (y : List Bool), (y ∈ Mᶜ) ↔ (y ∉ M) :=
    fun M y => Iff.rfl
  intro L
  constructor
  · intro h L' hL'
    obtain ⟨f, hf, hred⟩ := h L'ᶜ hL'
    refine ⟨f, hf, fun x => ?_⟩
    have hx := hred x
    rw [key L' x] at hx
    rw [key L (f x)]
    simpa only [not_not] using not_congr hx
  · intro h L' hL'
    have hmem : L'ᶜ ∈ PvsNP.coNP := by
      show (L'ᶜ)ᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    obtain ⟨f, hf, hred⟩ := h L'ᶜ hmem
    refine ⟨f, hf, fun x => ?_⟩
    have hx := hred x
    rw [key L' x, key L (f x)] at hx
    simpa only [not_not] using not_congr hx
