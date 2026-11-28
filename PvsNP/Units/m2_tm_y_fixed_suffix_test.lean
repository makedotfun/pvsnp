import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_tm_suffix_polytime
import PvsNP.Units.m2_polytime_comp

/-- Testing whether a fixed string `w` is a suffix of `x` is polynomial-time computable. -/
theorem PvsNP.Units.m2_tm_y_fixed_suffix_test :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => w.isSuffixOf x) := by
  intro w
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (w, x)) :=
    PvsNP.Units.m2_pair_build_polytime (fun _ => w) id
      (PvsNP.Units.m2_const_polytime w) ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x : List Bool => (w, x)) (fun p : List Bool × List Bool => p.1.isSuffixOf p.2)
    hpair PvsNP.Units.m2_tm_suffix_polytime
