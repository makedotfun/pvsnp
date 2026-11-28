import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_drop_all
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

/-- Writing the length of a string minus one in binary takes polynomial time: drop one
element (so the length drops by one), then convert the unary length to binary. -/
theorem PvsNP.Units.m2_tm_length_pred_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.length - 1)) := by
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop 1) := by
    apply PvsNP.Units.tf_fun_drop_all
  have hbits : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits x.length) := by
    apply PvsNP.Units.m2_unary_to_binary_polytime
  have heq : (fun x : List Bool => Nat.bits (x.length - 1)) =
      (fun x : List Bool => Nat.bits x.length) ∘ (fun x : List Bool => x.drop 1) := by
    funext x
    simp [Function.comp_apply, List.length_drop]
  rw [heq]
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.drop 1) (fun x : List Bool => Nat.bits x.length) hdrop hbits
