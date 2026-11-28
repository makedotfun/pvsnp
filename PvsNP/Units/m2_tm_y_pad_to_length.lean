import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_unary_monus
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_y_pad_to_length

/-- The padding block `1 ^ (|y| - |x|)` is polytime: the monus machine after swapping the pair. -/
theorem pad_part :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.2.length - p.1.length) true) := by
  have h := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_tm_unary_monus
  convert h using 1
  funext p
  simp only [Function.comp]

end PvsNP.Units.m2_tm_y_pad_to_length

theorem PvsNP.Units.m2_tm_y_pad_to_length :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ List.replicate (p.2.length - p.1.length) true) := by
  have hfork : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, List.replicate (p.2.length - p.1.length) true)) :=
    PvsNP.Units.m2_tm_pair_fork_polytime _ _
      PvsNP.Units.m2_pair_split_polytime.1
      PvsNP.Units.m2_tm_y_pad_to_length.pad_part
  have h := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    hfork PvsNP.Units.m2_pair_split_polytime.2.2
  convert h using 1
  funext p
  simp only [Function.comp]
