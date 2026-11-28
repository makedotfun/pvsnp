import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_linear_clock
import PvsNP.Units.m2_polytime_iff_time_poly
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_unary_add

/-- The unary clock `x ↦ replicate x.length true` is polynomial-time computable:
the settled linear clock bounds its running time by `c * n + c`, which is the
evaluation of the polynomial `C c * X + C c`, and the settled time-polynomial
characterisation turns that bound back into polynomial-time computability. -/
theorem clock_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) := by
  obtain ⟨c, M, hM⟩ := PvsNP.Units.m2_linear_clock
  refine (PvsNP.Units.m2_polytime_iff_time_poly PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)).2 ?_
  refine ⟨Polynomial.C c * Polynomial.X + Polynomial.C c, M, fun n => ?_⟩
  have h := hM n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h ⊢
  exact h

end PvsNP.Units.m2_tm_unary_add

/-- Writing the sum of two lengths in unary takes polynomial time (TM2):
join the two parts of the pair (the third conjunct of the settled unit
`m2_pair_split_polytime`), then run the unary clock on the joined string;
the joined string's length is the sum of the two lengths
(`List.length_append`), and the two steps compose by the settled unit
`m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_unary_add :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        List.replicate (p.1.length + p.2.length) true) := by
  have hjoin := PvsNP.Units.m2_pair_split_polytime.2.2
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair
    PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1 ++ p.2)
    (fun x : List Bool => List.replicate x.length true)
    hjoin PvsNP.Units.m2_tm_unary_add.clock_polytime
  have hfun : (fun x : List Bool => List.replicate x.length true) ∘
        (fun p : List Bool × List Bool => p.1 ++ p.2) =
      (fun p : List Bool × List Bool =>
        List.replicate (p.1.length + p.2.length) true) := by
    funext p
    simp [List.length_append]
  rwa [hfun] at hcomp
