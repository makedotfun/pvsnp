import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.tf_fun_ones_unary

namespace PvsNP.Units.m2_tm_y_take_drop_count

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Replace the first component by its number of true bits, written in unary. -/
theorem count_first_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (List.replicate (p.1.count true) true, p.2)) := by
  exact cpt_first PvsNP.Units.tf_fun_ones_unary

/-- The unary counter has exactly the length needed by the length-based operations. -/
theorem take_drop_count_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.2.take (p.1.count true)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.2.drop (p.1.count true)) := by
  constructor
  · have h : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          p.2.take (List.replicate (p.1.count true) true).length) :=
      cpt_comp count_first_polytime PvsNP.Units.m2_take_drop_length_polytime.1
    simpa only [List.length_replicate] using h
  · have h : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          p.2.drop (List.replicate (p.1.count true) true).length) :=
      cpt_comp count_first_polytime PvsNP.Units.m2_take_drop_length_polytime.2
    simpa only [List.length_replicate] using h

end PvsNP.Units.m2_tm_y_take_drop_count

theorem PvsNP.Units.m2_tm_y_take_drop_count :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.2.take (p.1.count true)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.2.drop (p.1.count true)) :=
  PvsNP.Units.m2_tm_y_take_drop_count.take_drop_count_polytime
