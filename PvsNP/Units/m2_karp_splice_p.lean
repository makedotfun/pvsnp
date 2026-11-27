import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_const_polytime

theorem PvsNP.Units.m2_karp_splice_p :
    ∀ L₁ L₂ L₃ E : Language Bool,
      PvsNP.KarpReducible L₁ L₂ → E ∈ PvsNP.P → L₃ ∈ PvsNP.P →
        (∃ y : List Bool, y ∈ L₂) → (∃ z : List Bool, z ∉ L₂) →
          PvsNP.KarpReducible
            ({x : List Bool | (x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)} : Language Bool) L₂ := by
  intro L₁ L₂ L₃ E ⟨f₁, hf₁, hiff₁⟩ ⟨dE, hdE, hiffE⟩ ⟨d₃, hd₃, hiff₃⟩ ⟨y, hy⟩ ⟨z, hz⟩
  let g₃ : List Bool → List Bool := fun x => if d₃ x = true then y else z
  have hg₃ : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g₃ :=
    PvsNP.Units.m2_ite_polytime d₃ (fun _ => y) (fun _ => z) hd₃
      (PvsNP.Units.m2_const_polytime y) (PvsNP.Units.m2_const_polytime z)
  let F : List Bool → List Bool := fun x => if dE x = true then f₁ x else g₃ x
  have hF : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F :=
    PvsNP.Units.m2_ite_polytime dE f₁ g₃ hdE hf₁ hg₃
  refine ⟨F, hF, fun x => ?_⟩
  by_cases hxE : x ∈ E
  · have hdEx : dE x = true := (hiffE x).mp hxE
    have hFx : F x = f₁ x := by simp [F, hdEx]
    rw [hFx]
    change ((x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)) ↔ f₁ x ∈ L₂
    rw [ ← hiff₁ x]
    exact ⟨fun h => h.elim (fun h1 => h1.2) (fun h2 => absurd hxE h2.1),
      fun h1 => Or.inl ⟨hxE, h1⟩⟩
  · have hdEx : dE x ≠ true := fun h => hxE ((hiffE x).mpr h)
    have hFx : F x = g₃ x := by simp [F, hdEx]
    rw [hFx]
    by_cases hx₃ : x ∈ L₃
    · have hd₃x : d₃ x = true := (hiff₃ x).mp hx₃
      have hg₃x : g₃ x = y := by simp [g₃, hd₃x]
      rw [hg₃x]
      change ((x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)) ↔ y ∈ L₂
      exact ⟨fun _ => hy, fun _ => Or.inr ⟨hxE, hx₃⟩⟩
    · have hd₃x : d₃ x ≠ true := fun h => hx₃ ((hiff₃ x).mpr h)
      have hg₃x : g₃ x = z := by simp [g₃, hd₃x]
      rw [hg₃x]
      change ((x ∈ E ∧ x ∈ L₁) ∨ (x ∉ E ∧ x ∈ L₃)) ↔ z ∈ L₂
      exact ⟨fun h => h.elim (fun h1 => absurd h1.1 hxE) (fun h2 => absurd h2.2 hx₃),
        fun h => absurd h hz⟩
