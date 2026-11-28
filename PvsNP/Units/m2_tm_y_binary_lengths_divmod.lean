import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_divmod
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

/-- Dividing one length by another with remainder, in binary, takes polynomial time (TM2).

Each conjunct is the composition of the corresponding conjunct of the settled unit
`m2_tm_unary_divmod` (unary quotient / remainder of the two lengths) with the settled unit
`m2_unary_to_binary_polytime` (unary length to binary digits), composed by the settled unit
`m2_polytime_comp`; `(List.replicate n true).length = n` identifies the composite with the
posted function. Division by zero is Mathlib's: `n / 0 = 0` and `n % 0 = n`, as in the
unary unit. -/
theorem PvsNP.Units.m2_tm_y_binary_lengths_divmod :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (p.1.length / p.2.length)) ∧
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (p.1.length % p.2.length)) := by
  constructor
  · have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.length / p.2.length) true)
      (fun x : List Bool => Nat.bits x.length)
      PvsNP.Units.m2_tm_unary_divmod.1
      PvsNP.Units.m2_unary_to_binary_polytime
    have hEq : (fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (p.1.length / p.2.length) true)
        = fun p : List Bool × List Bool => Nat.bits (p.1.length / p.2.length) := by
      funext p
      simp [List.length_replicate]
    rw [hEq] at h
    exact h
  · have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true)
      (fun x : List Bool => Nat.bits x.length)
      PvsNP.Units.m2_tm_unary_divmod.2
      PvsNP.Units.m2_unary_to_binary_polytime
    have hEq : (fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (p.1.length % p.2.length) true)
        = fun p : List Bool × List Bool => Nat.bits (p.1.length % p.2.length) := by
      funext p
      simp [List.length_replicate]
    rw [hEq] at h
    exact h
