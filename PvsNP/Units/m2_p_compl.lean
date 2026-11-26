import Mathlib
import PvsNP.Defs

set_option autoImplicit false

namespace PvsNP.Units.m2_p_compl

private def boolNotEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

theorem p_compl (L : Language Bool) (hL : L ∈ PvsNP.P) : Lᶜ ∈ PvsNP.P := by
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

end PvsNP.Units.m2_p_compl

theorem PvsNP.Units.m2_p_compl :
    ∀ L : Language Bool, L ∈ PvsNP.P → Lᶜ ∈ PvsNP.P :=
  PvsNP.Units.m2_p_compl.p_compl
