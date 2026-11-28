import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_sqrt
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

/-- The integer square root of a length, in binary, takes polynomial time: take the
square root in unary (m2_tm_unary_sqrt), then convert the unary length to binary
(m2_unary_to_binary_polytime), composed by m2_polytime_comp. -/
theorem PvsNP.Units.m2_tm_y_binary_sqrt_length :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.sqrt x.length)) := by
  have hsqrt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (Nat.sqrt x.length) true) := by
    apply PvsNP.Units.m2_tm_unary_sqrt
  have hbits : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits x.length) := by
    apply PvsNP.Units.m2_unary_to_binary_polytime
  have heq : (fun x : List Bool => Nat.bits (Nat.sqrt x.length)) =
      (fun x : List Bool => Nat.bits x.length) ∘
        (fun x : List Bool => List.replicate (Nat.sqrt x.length) true) := by
    funext x
    simp [Function.comp_apply, List.length_replicate]
  rw [heq]
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (Nat.sqrt x.length) true)
    (fun x : List Bool => Nat.bits x.length) hsqrt hbits
