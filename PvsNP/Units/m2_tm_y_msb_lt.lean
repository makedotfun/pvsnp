import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_tm_binary_lt

theorem PvsNP.Units.m2_tm_y_msb_lt :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.reverse.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.2.reverse.map Bool.toNat))) :=
  PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_prod_map_polytime _ _ PvsNP.Units.m2_reverse_polytime PvsNP.Units.m2_reverse_polytime)
    PvsNP.Units.m2_tm_binary_lt
