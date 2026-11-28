import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_count_le_pair

end PvsNP.Units.m2_tm_count_le_pair

/-- Comparing the numbers of trues of two strings takes polynomial time. -/
theorem PvsNP.Units.m2_tm_count_le_pair :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => decide (p.1.count true ≤ p.2.count true)) := by
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))
    (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length))
    (PvsNP.Units.m2_prod_map_polytime _ _ PvsNP.Units.tf_fun_ones_unary PvsNP.Units.tf_fun_ones_unary)
    PvsNP.Units.m2_len_le_polytime
  have heq : (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length)) ∘
      (fun p : List Bool × List Bool => (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))
      = (fun p : List Bool × List Bool => decide (p.1.count true ≤ p.2.count true)) := by
    funext p
    simp [List.length_replicate]
  rw [heq] at hcomp
  exact hcomp
