import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_binary_eq
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.m2_reverse_polytime,
PvsNP.Units.m2_prod_map_polytime, PvsNP.Units.m2_tm_binary_eq and
PvsNP.Units.m2_polytime_comp of github.com/makedotfun/pvsnp:
reverse both strings, then test equality of the binary values.
-/

/-- Testing two binary numerals written most significant bit first for equal
value takes polynomial time (TM2): reverse both strings, then compare the
values read least significant bit first. -/
theorem PvsNP.Units.m2_tm_y_msb_eq :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.reverse.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (p.2.reverse.map Bool.toNat))) := by
  have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse)) :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x.reverse)
      (fun x : List Bool => x.reverse)
      PvsNP.Units.m2_reverse_polytime PvsNP.Units.m2_reverse_polytime
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse))
    (fun q : List Bool × List Bool =>
      decide (Nat.ofDigits (2 : ℕ) (q.1.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (q.2.map Bool.toNat)))
    hg PvsNP.Units.m2_tm_binary_eq
  exact h
