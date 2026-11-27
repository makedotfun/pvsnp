import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed

namespace PvsNP.Units.m2_tm_y_count_product_unary
open PvsNP.Units.m2_np_down_closed PvsNP.Units.m2_np_down_closed.PEqualNP.Library.Machines

theorem filterMap_true_eq : ∀ x : List Bool,
    List.replicate (x.count true) true = x.filterMap (fun b => if b then some true else none)
  | [] => rfl
  | false :: xs => by simpa [List.count_cons] using filterMap_true_eq xs
  | true :: xs => by
    simp only [List.count_cons_self, List.replicate_succ, List.filterMap_cons, ite_true]
    exact congrArg (List.cons true) (filterMap_true_eq xs)

theorem cpt_count_true :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.count true) true) :=
  filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) filterMap_true_eq

theorem main_cpt :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.count true * p.2.count true) true) := by
  have h1 := cpt_comp (cpt_first cpt_count_true) (cpt_second cpt_count_true)
  have h2 := cpt_comp h1 mul_polyTime
  simpa only [List.length_replicate] using h2

end PvsNP.Units.m2_tm_y_count_product_unary

theorem PvsNP.Units.m2_tm_y_count_product_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.count true * p.2.count true) true) :=
  PvsNP.Units.m2_tm_y_count_product_unary.main_cpt
