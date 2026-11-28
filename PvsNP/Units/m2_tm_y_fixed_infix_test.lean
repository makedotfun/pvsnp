import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_infix_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_fixed_infix_test

theorem main : ∀ w : List Bool,
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (w <:+: x)) := by
  intro w
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) := ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hP := PvsNP.Units.m2_pair_build_polytime (fun _ => w) (fun x => x)
    (PvsNP.Units.m2_const_polytime w) hid
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    _ _ hP PvsNP.Units.m2_tm_infix_polytime

end PvsNP.Units.m2_tm_y_fixed_infix_test

theorem PvsNP.Units.m2_tm_y_fixed_infix_test :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => decide (w <:+: x)) :=
  PvsNP.Units.m2_tm_y_fixed_infix_test.main
