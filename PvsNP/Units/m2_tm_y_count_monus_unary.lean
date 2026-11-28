import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_y_count_monus_unary

theorem drop_replicate_true : ∀ (n k : ℕ),
    (List.replicate n true).drop k = List.replicate (n - k) true := by
  intro n k
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.replicate_succ, ih k]

end PvsNP.Units.m2_tm_y_count_monus_unary

/-- The difference of the numbers of trues of two strings, cut off at zero, in
unary takes polynomial time: count the trues of both strings in unary by the
settled unit `tf_fun_ones_unary` on both components (settled unit
`m2_prod_map_polytime`), swap the pair (settled unit
`m2_tm_pair_swap_polytime`), then drop as many trues from the first count as
the second count has (second conjunct of the settled unit
`m2_take_drop_length_polytime`), composed by the settled unit
`m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_y_count_monus_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.count true - p.2.count true) true) := by
  have hmap := PvsNP.Units.m2_prod_map_polytime
    (fun x : List Bool => List.replicate (x.count true) true)
    (fun x : List Bool => List.replicate (x.count true) true)
    PvsNP.Units.tf_fun_ones_unary PvsNP.Units.tf_fun_ones_unary
  have hswap := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodePair
    (fun p : List Bool × List Bool =>
      (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true))
    (fun p : List Bool × List Bool => (p.2, p.1))
    hmap PvsNP.Units.m2_tm_pair_swap_polytime
  have hdrop := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    ((fun p : List Bool × List Bool => (p.2, p.1)) ∘
      (fun p : List Bool × List Bool =>
        (List.replicate (p.1.count true) true, List.replicate (p.2.count true) true)))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    hswap PvsNP.Units.m2_take_drop_length_polytime.2
  convert hdrop using 1
  funext p
  simp only [Function.comp_apply, List.length_replicate]
  exact (PvsNP.Units.m2_tm_y_count_monus_unary.drop_replicate_true _ _).symm
