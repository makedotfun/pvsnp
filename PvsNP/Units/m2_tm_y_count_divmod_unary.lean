import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_tm_unary_mod_const
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

/-- Dividing the number of trues by a fixed `k`, with remainder, in unary
takes polynomial time (TM2): first write the count of trues in unary
(settled `tf_fun_ones_unary`), then divide that length by `k` in unary
(settled `m2_tm_unary_div_const`) or take its remainder by `k` in unary
(settled `m2_tm_unary_mod_const`), composed by the settled
`m2_polytime_comp` (`List.length_replicate` turns the length of the unary
count back into the count itself). -/
theorem PvsNP.Units.m2_tm_y_count_divmod_unary : ∀ k : ℕ,
  PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.count true / k) true) ∧
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.count true % k) true) := by
  intro k
  constructor
  · have heq : (fun x : List Bool => List.replicate (x.count true / k) true) =
        (fun y : List Bool => List.replicate (y.length / k) true) ∘
          (fun x : List Bool => List.replicate (x.count true) true) := by
      funext x
      simp [List.length_replicate]
    rw [heq]
    exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.tf_fun_ones_unary (PvsNP.Units.m2_tm_unary_div_const k)
  · have heq : (fun x : List Bool => List.replicate (x.count true % k) true) =
        (fun y : List Bool => List.replicate (y.length % k) true) ∘
          (fun x : List Bool => List.replicate (x.count true) true) := by
      funext x
      simp [List.length_replicate]
    rw [heq]
    exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.tf_fun_ones_unary (PvsNP.Units.m2_tm_unary_mod_const k)
