import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_binary_half_double
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_polytime_comp

/-- Writing the bit length of a binary numeral in unary takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_bit_length_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))).length true) := by
  have hstrip : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.m2_tm_binary_half_double.stripLSB :=
    PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
  have hun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun l : List Bool => List.replicate (l.length / 1) true) :=
    PvsNP.Units.m2_tm_unary_div_const 1
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString _ _ hstrip hun
  have heq :
      ((fun l : List Bool => List.replicate (l.length / 1) true) ∘
        PvsNP.Units.m2_tm_binary_half_double.stripLSB) =
      (fun x : List Bool => List.replicate (Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))).length true) := by
    funext x
    simp only [Function.comp_apply, Nat.div_one,
      PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits,
      PvsNP.Units.m2_tm_binary_half_double.val]
  rwa [heq] at hcomp
