import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_mul_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_y_falses_times_trues_unary

private theorem count_false_eq (x : List Bool) :
    x.count false = (x.map not).count true := by
  induction x with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih]

private theorem map_not_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (List.map not) := by
  have h := PvsNP.Units.m2_transducer_polytime Unit
    (fun _ b => ((), some (!b)))
    (fun _ => none)
    (fun _ x => x.map not)
    (fun _ => rfl)
    (fun _ b x => rfl)
    ()
  exact h

private theorem falses_unary_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count false) true) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (List.map not) (fun x : List Bool => List.replicate (x.count true) true)
    map_not_polyTime PvsNP.Units.tf_fun_ones_unary
  have heq : ((fun x : List Bool => List.replicate (x.count true) true) ∘ List.map not) =
      (fun x : List Bool => List.replicate (x.count false) true) := by
    funext x
    simp [count_false_eq]
  rwa [heq] at h

end PvsNP.Units.m2_tm_y_falses_times_trues_unary

/-- Computing `1^(#false(x) * #true(x))` in unary is polynomial-time (TM2): pair `1^(#false(x))`
and `1^(#true(x))`, then multiply their lengths. -/
theorem PvsNP.Units.m2_tm_y_falses_times_trues_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count false * x.count true) true) := by
  have hpair := PvsNP.Units.m2_pair_build_polytime
    (fun x : List Bool => List.replicate (x.count false) true)
    (fun x : List Bool => List.replicate (x.count true) true)
    PvsNP.Units.m2_tm_y_falses_times_trues_unary.falses_unary_polyTime
    PvsNP.Units.tf_fun_ones_unary
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool =>
      (List.replicate (x.count false) true, List.replicate (x.count true) true))
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
    hpair PvsNP.Units.m2_mul_polytime
  have heq :
      ((fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true) ∘
        (fun x : List Bool =>
          (List.replicate (x.count false) true, List.replicate (x.count true) true))) =
      (fun x : List Bool => List.replicate (x.count false * x.count true) true) := by
    funext x
    simp [List.length_replicate]
  rwa [heq] at hcomp
