import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.m2_polytime_comp

/-!
# tf_fun_add_const: adding the constant 5 to a binary value is polytime

Composition of two settled units of github.com/makedotfun/pvsnp
(Apache License 2.0), which this file imports:

* `tf_fun_succ`: `fun x => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1)`
  is `PvsNP.PolyTimeComputable` (settled statement, read from the campaign
  API);
* `m2_polytime_comp`: polytime computability is closed under composition.

Adding 5 is the successor function composed with itself five times: after
the first successor the value is in canonical `Nat.bits` form, and the value
of `Nat.bits n` is `n`, so the iterates add one each time.

RISK MARKER (the one step not verifiable by hand): the Mathlib identity
`Nat.ofDigits 2 ((Nat.bits n).map Bool.toNat) = n`, isolated as `val_bits`
below; its proof goes through `Nat.digits` (`Nat.ofDigits_digits`). If a
name or signature differs in the campaign's Mathlib, this is the single
lemma to repair at `desk check` time. Everything else in the file is a
direct composition of the two settled theorems above.

Verified by hand, line by line (no lease is held for this unit, so
`desk check --build` could not be run); every step is a complete proof.
-/

namespace PvsNP.Units.tf_fun_add_const

/-- The binary value of the canonical bit representation of `n` is `n`. -/
theorem val_bits (n : ℕ) :
    Nat.ofDigits 2 ((Nat.bits n).map Bool.toNat) = n := by
  have hmap : (Nat.bits n).map Bool.toNat = Nat.digits 2 n := by
    simp [Nat.bits, Nat.digits, Bool.toNat]
  rw [hmap]
  exact Nat.ofDigits_digits 2 (by norm_num) n

/-- Adding 5 is the fivefold self-composition of the successor function. -/
theorem fun_eq :
    (fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 5)) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1)) ∘
        ((fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1)) ∘
          ((fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1)) ∘
            ((fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1)) ∘
              (fun x : List Bool => Nat.bits (Nat.ofDigits 2 (x.map Bool.toNat) + 1))))) := by
  funext x
  simp only [Function.comp_apply]
  rw [val_bits, val_bits, val_bits, val_bits]
  congr 1
  omega

end PvsNP.Units.tf_fun_add_const

/-- Adding the constant 5 to a binary value is computable in polynomial
time (TM2): five successors, composed with the settled composition lemma
`m2_polytime_comp` over the settled successor unit `tf_fun_succ`. -/
theorem PvsNP.Units.tf_fun_add_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
  rw [PvsNP.Units.tf_fun_add_const.fun_eq]
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_succ
    (PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_succ
      (PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_succ
        (PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_succ
          PvsNP.Units.tf_fun_succ)))
