import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_unary_min_max
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.tf_fun_ones_unary (counting trues in unary),
PvsNP.Units.m2_prod_map_polytime (`both`), PvsNP.Units.m2_tm_unary_min_max
(min/max of two unary numerals), and PvsNP.Units.m2_polytime_comp
of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.m2_tm_y_count_min_max_unary

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          List.replicate (min (p.1.count true) (p.2.count true)) true) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          List.replicate (max (p.1.count true) (p.2.count true)) true) := by
  have hboth : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool =>
        (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true)) :=
    PvsNP.Units.m2_prod_map_polytime.both _ _
      PvsNP.Units.tf_fun_ones_unary PvsNP.Units.tf_fun_ones_unary
  have hmin : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      ((fun q : List Bool × List Bool =>
        List.replicate (min q.1.length q.2.length) true) ∘
        (fun p : List Bool × List Bool =>
          (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      _ _ hboth PvsNP.Units.m2_tm_unary_min_max.1
  have hmax : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      ((fun q : List Bool × List Bool =>
        List.replicate (max q.1.length q.2.length) true) ∘
        (fun p : List Bool × List Bool =>
          (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      _ _ hboth PvsNP.Units.m2_tm_unary_min_max.2
  have heq_min : ((fun q : List Bool × List Bool =>
        List.replicate (min q.1.length q.2.length) true) ∘
        (fun p : List Bool × List Bool =>
          (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))) =
      (fun p : List Bool × List Bool =>
        List.replicate (min (p.1.count true) (p.2.count true)) true) := by
    funext ⟨a, b⟩
    simp [List.length_replicate]
  have heq_max : ((fun q : List Bool × List Bool =>
        List.replicate (max q.1.length q.2.length) true) ∘
        (fun p : List Bool × List Bool =>
          (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))) =
      (fun p : List Bool × List Bool =>
        List.replicate (max (p.1.count true) (p.2.count true)) true) := by
    funext ⟨a, b⟩
    simp [List.length_replicate]
  exact ⟨by rwa [heq_min] at hmin, by rwa [heq_max] at hmax⟩

end PvsNP.Units.m2_tm_y_count_min_max_unary

theorem PvsNP.Units.m2_tm_y_count_min_max_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          List.replicate (min (p.1.count true) (p.2.count true)) true) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool =>
          List.replicate (max (p.1.count true) (p.2.count true)) true) :=
  PvsNP.Units.m2_tm_y_count_min_max_unary.main
