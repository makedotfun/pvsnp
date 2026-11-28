import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_flatmap

set_option autoImplicit false

/-!
Doubling every bit is the settled unit `tf_fun_flatmap`; appending the constant `[false, true]`
is `cpt_app2` with `cpt_const` from `fr_ladner`.
-/

theorem PvsNP.Units.m2_tm_list_code_single :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.flatMap (fun b : Bool => [b, b]) ++ [false, true]) := by
  have hu : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.flatMap (fun b : Bool => [b, b])) :=
    PvsNP.Units.tf_fun_flatmap
  have h := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2 hu
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [false, true])
  exact h
