import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

theorem PvsNP.Units.m2_z_p_cofinite :
    ∀ S : Finset (List Bool), ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.P ∧
      ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.NP ∧
        ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.coNP := by
  intro S
  have hfin : ({x : List Bool | x ∈ S} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite S
  have hcompl : ({x : List Bool | x ∉ S} : Language Bool) =
      ({x : List Bool | x ∈ S} : Language Bool)ᶜ := by
    ext x
    rfl
  have hP : ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.P := by
    rw [hcompl]
    exact PvsNP.Units.m2_p_compl ({x : List Bool | x ∈ S} : Language Bool) hfin
  have hNP : ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np hP
  have hcoNP : ({x : List Bool | x ∉ S} : Language Bool) ∈ PvsNP.coNP := by
    show ({x : List Bool | x ∉ S} : Language Bool)ᶜ ∈ PvsNP.NP
    rw [hcompl, compl_compl]
    exact PvsNP.Units.m2_p_subset_np hfin
  exact ⟨hP, hNP, hcoNP⟩
