import Mathlib
import PvsNP.Defs

set_option autoImplicit false

namespace PvsNP.Units.m2_p_eq_np_conp

private def boolNotEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

private theorem p_compl (L : Language Bool) (hL : L ∈ PvsNP.P) : Lᶜ ∈ PvsNP.P := by
  obtain ⟨f, ⟨c⟩, hiff⟩ := hL
  refine ⟨fun x => !(f x), ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet.trans boolNotEquiv
    time := c.time
    outputsFun := fun x => by
      have h := c.outputsFun x
      have heq : List.map (c.outputAlphabet.trans boolNotEquiv).invFun (PvsNP.encodeAnswer (!(f x))) =
          List.map c.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)) := by
        simp [PvsNP.encodeAnswer, Computability.encodeBool, boolNotEquiv]
      simpa only [heq] using h }⟩, fun x => ?_⟩
  change ¬ (x ∈ L) ↔ !(f x) = true
  rw [hiff x]
  cases f x <;> simp

end PvsNP.Units.m2_p_eq_np_conp

theorem PvsNP.Units.m2_p_eq_np_conp :
    PvsNP.P = PvsNP.NP → PvsNP.NP = PvsNP.coNP := by
  intro h
  ext L
  constructor
  · intro hL
    show Lᶜ ∈ PvsNP.NP
    rw [← h] at hL ⊢
    exact PvsNP.Units.m2_p_eq_np_conp.p_compl L hL
  · intro hL
    have hLc : Lᶜ ∈ PvsNP.NP := hL
    rw [← h] at hLc ⊢
    have hLcc := PvsNP.Units.m2_p_eq_np_conp.p_compl Lᶜ hLc
    simpa [compl_compl] using hLcc
