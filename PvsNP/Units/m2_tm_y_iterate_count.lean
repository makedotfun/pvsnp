import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_prod_map_polytime

import PvsNP.Units.tf_fun_ones_unary

import PvsNP.Units.m2_iterate_polytime

import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_y_iterate_count

end PvsNP.Units.m2_tm_y_iterate_count

/-- Iterating a length-bounded polynomial-time map as many times as a string has trues
takes polynomial time (TM2).

Replace the counter string `y` by the unary string `1^(y.count true)` (the settled unit
`tf_fun_ones_unary`, paired with the identity by the settled unit `m2_prod_map_polytime`),
then iterate by the settled unit `m2_iterate_polytime` (`List.length_replicate` turns the
unary length back into the count), composed by the settled unit `m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_y_iterate_count :
    ∀ (g : List Bool → List Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
        (∀ y : List Bool, (g y).length ≤ y.length + k) →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
            (fun p : List Bool × List Bool => g^[p.2.count true] p.1) := by
  intro g k hg hk
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, List.replicate (p.2.count true) true)) :=
    PvsNP.Units.m2_prod_map_polytime.both (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.count true) true)
      PvsNP.Units.m2_prod_map_polytime.ident
      PvsNP.Units.tf_fun_ones_unary
  have hiter : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    PvsNP.Units.m2_iterate_polytime g k hg hk
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.1, List.replicate (p.2.count true) true))
    (fun p : List Bool × List Bool => g^[p.2.length] p.1)
    hpair hiter
  have hfun : (fun p : List Bool × List Bool => g^[p.2.length] p.1) ∘
        (fun p : List Bool × List Bool => (p.1, List.replicate (p.2.count true) true)) =
          fun p : List Bool × List Bool => g^[p.2.count true] p.1 := by
    funext p
    simp [Function.comp_apply, List.length_replicate]
  rw [hfun] at hcomp
  exact hcomp
