import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.tf_fun_rotate
import PvsNP.Units.tf_fun_rotate_all
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp

/-- Rotating a binary string by its number of trues takes polynomial time (TM2): write the
count in unary (the settled unit `tf_fun_ones_unary`), pair it with the input, and iterate
rotate-by-one that many times (the settled units `tf_fun_rotate` and `m2_iterate_polytime`);
iterating rotate-by-one `k` times is rotate-by-`k` (`tf_fun_rotate_all.rotate_iter`). -/
theorem PvsNP.Units.tf_fun_rotate_count :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate (x.count true)) := by
  have hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate 1) :=
    PvsNP.Units.tf_fun_rotate
  have hlen : ∀ y : List Bool, ((fun x : List Bool => x.rotate 1) y).length ≤ y.length + 0 := by
    intro y
    simp [List.length_rotate]
  have hiter := PvsNP.Units.m2_iterate_polytime (fun x : List Bool => x.rotate 1) 0 hg hlen
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    PvsNP.Units.m2_pair_build_polytime.cpt_id
  have hones : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count true) true) :=
    PvsNP.Units.tf_fun_ones_unary
  have hpair := PvsNP.Units.m2_pair_build_polytime.cpt_pair hid hones
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeString
    (fun x : List Bool => (x, List.replicate (x.count true) true))
    (fun p : List Bool × List Bool => (fun x : List Bool => x.rotate 1)^[p.2.length] p.1)
    hpair hiter
  have hfun : (fun p : List Bool × List Bool =>
        (fun x : List Bool => x.rotate 1)^[p.2.length] p.1) ∘
      (fun x : List Bool => (x, List.replicate (x.count true) true)) =
      fun x : List Bool => x.rotate (x.count true) := by
    funext x
    simp only [Function.comp_apply, List.length_replicate]
    exact PvsNP.Units.tf_fun_rotate_all.rotate_iter (x.count true) x
  rw [← hfun]
  exact hcomp
