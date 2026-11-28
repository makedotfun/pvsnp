import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_ite_polytime

theorem PvsNP.Units.m2_karp_splice_p :
    ∀ L₁ L₂ L₃ E : Language Bool, PvsNP.KarpReducible L₁ L₂ → E ∈ PvsNP.P → L₃ ∈ PvsNP.P →
      (∃ y : List Bool, y ∈ L₂) → (∃ z : List Bool, z ∉ L₂) →
        PvsNP.KarpReducible ({x : List Bool | (x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)} : Language Bool) L₂ := by
  intro L₁ L₂ L₃ E h12 hE h3 ⟨y, hy⟩ ⟨z, hz⟩
  obtain ⟨f₁, hf₁c, hf₁m⟩ := h12
  obtain ⟨cE, hcEc, hcEm⟩ := hE
  obtain ⟨c3, hc3c, hc3m⟩ := h3
  have hg3c : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if c3 x = true then y else z) :=
    PvsNP.Units.m2_ite_polytime c3 (fun _ => y) (fun _ => z) hc3c
      (PvsNP.Units.m2_const_polytime y) (PvsNP.Units.m2_const_polytime z)
  refine ⟨fun x => if cE x = true then f₁ x else (if c3 x = true then y else z),
    PvsNP.Units.m2_ite_polytime cE f₁ (fun x => if c3 x = true then y else z) hcEc hf₁c hg3c, ?_⟩
  intro x
  change ((x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)) ↔
    (if cE x = true then f₁ x else if c3 x = true then y else z) ∈ L₂
  cases hce : cE x
  · have hnE : x ∉ E := fun hx => Bool.noConfusion (((hcEm x).mp hx).symm.trans hce)
    cases hc3 : c3 x
    · have hn3 : x ∉ L₃ := fun hx => Bool.noConfusion (((hc3m x).mp hx).symm.trans hc3)
      exact ⟨fun h => h.elim (fun h1 => absurd h1.1 hnE) (fun h2 => absurd h2.2 hn3),
        fun h => absurd h hz⟩
    · have hy3 : x ∈ L₃ := (hc3m x).mpr hc3
      exact ⟨fun _ => hy, fun _ => Or.inr ⟨hnE, hy3⟩⟩
  · have hyE : x ∈ E := (hcEm x).mpr hce
    exact ⟨fun h => (hf₁m x).mp (h.elim (fun h1 => h1.2) (fun h2 => absurd hyE h2.1)),
      fun h => Or.inl ⟨hyE, (hf₁m x).mpr h⟩⟩
