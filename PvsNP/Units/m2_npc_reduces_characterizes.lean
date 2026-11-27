import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_karp_compl_iff

theorem PvsNP.Units.m2_npc_reduces_characterizes :
    ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ∀ L : Language Bool,
      (L ∈ PvsNP.NP ↔ PvsNP.KarpReducible L L₀) ∧
        (L ∈ PvsNP.coNP ↔ PvsNP.KarpReducible L L₀ᶜ) := by
  intro L₀ hL₀ L
  constructor
  · constructor
    · intro hL
      exact hL₀.2 L hL
    · intro hred
      exact PvsNP.Units.m2_np_down_closed L L₀ hred hL₀.1
  · constructor
    · intro hL
      have hc : Lᶜ ∈ PvsNP.NP := hL
      have := (PvsNP.Units.m2_karp_compl_iff Lᶜ L₀).mp (hL₀.2 Lᶜ hc)
      simpa using this
    · intro hred
      have hred1 : PvsNP.KarpReducible Lᶜ L₀ᶜᶜ :=
        (PvsNP.Units.m2_karp_compl_iff L L₀ᶜ).mp hred
      have hred0 : PvsNP.KarpReducible Lᶜ L₀ := by
        simpa using hred1
      show Lᶜ ∈ PvsNP.NP
      exact PvsNP.Units.m2_np_down_closed Lᶜ L₀ hred0 hL₀.1
