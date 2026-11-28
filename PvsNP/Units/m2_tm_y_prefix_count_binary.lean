import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_polytime_comp

import PvsNP.Units.m2_take_drop_length_polytime

import PvsNP.Units.m2_tm_count_binary


set_option autoImplicit false


/-- The number of trues among the first |x| bits of y, in binary, takes
polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_y_prefix_count_binary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits ((p.2.take p.1.length).count true)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    (fun x : List Bool => Nat.bits (x.count true))
    (PvsNP.Units.m2_take_drop_length_polytime).1
    PvsNP.Units.m2_tm_count_binary
