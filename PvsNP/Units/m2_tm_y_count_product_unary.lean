import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_mul_polytime
import PvsNP.Units.m2_polytime_comp

/-- The product of the numbers of trues of two strings, in unary, takes polynomial time (TM2).

The settled unit `tf_fun_ones_unary` writes the number of trues of each string in unary.
The settled unit `m2_prod_map_polytime` applies that map to each part of the pair.
The settled unit `m2_mul_polytime` then multiplies the two unary lengths
(`List.length_replicate`). The settled unit `m2_polytime_comp` composes those maps. -/
theorem PvsNP.Units.m2_tm_y_count_product_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.count true * p.2.count true) true) := by
  let ones : List Bool → List Bool := fun x => List.replicate (x.count true) true
  let f : List Bool × List Bool → List Bool × List Bool :=
    fun p => (ones p.1, ones p.2)
  let g : List Bool × List Bool → List Bool :=
    fun q => List.replicate (q.1.length * q.2.length) true
  have hf : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair f :=
    PvsNP.Units.m2_prod_map_polytime.both ones ones
      PvsNP.Units.tf_fun_ones_unary PvsNP.Units.tf_fun_ones_unary
  have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g :=
    PvsNP.Units.m2_mul_polytime
  have hgf : (fun p : List Bool × List Bool =>
      List.replicate (p.1.count true * p.2.count true) true) = g ∘ f := by
    funext p
    simp [Function.comp, f, g, ones, List.length_replicate]
  rw [hgf]
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString f g hf hg
