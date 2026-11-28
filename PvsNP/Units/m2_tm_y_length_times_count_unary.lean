import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.tf_fun_ones_unary

import PvsNP.Units.m2_pair_build_polytime

import PvsNP.Units.m2_mul_polytime

import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_length_times_count_unary

/-- Pair a string with its true-count in unary: the identity machine on the
first component and the settled unit `tf_fun_ones_unary` on the second,
combined by `m2_pair_build_polytime`. -/
theorem pair_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, List.replicate (x.count true) true)) :=
  PvsNP.Units.m2_pair_build_polytime id
    (fun x : List Bool => List.replicate (x.count true) true)
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
    PvsNP.Units.tf_fun_ones_unary

end PvsNP.Units.m2_tm_y_length_times_count_unary

/-- The length of a string times its number of trues, in unary, takes polynomial
time (TM2): pair `x` with its true-count in unary, then multiply the two unary
numbers (`m2_mul_polytime`), composed by `m2_polytime_comp`. The second
component's length is the true-count (`List.length_replicate`). -/
theorem PvsNP.Units.m2_tm_y_length_times_count_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length * x.count true) true) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeString
    (fun x : List Bool => (x, List.replicate (x.count true) true))
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
    PvsNP.Units.m2_tm_y_length_times_count_unary.pair_polyTime
    PvsNP.Units.m2_mul_polytime
  have he : ((fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true) ∘
      (fun x : List Bool => (x, List.replicate (x.count true) true)))
      = (fun x : List Bool => List.replicate (x.length * x.count true) true) := by
    funext x
    simp only [Function.comp_apply, List.length_replicate]
  rwa [he] at h
