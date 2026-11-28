import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_destutter_polytime
import PvsNP.Units.m2_linear_clock
import PvsNP.Units.m2_tm_polytime_of_power_bound
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_run_count_unary

end PvsNP.Units.m2_tm_y_run_count_unary

/-- The number of runs of equal bits of a string, in unary, takes polynomial
time: collapse each run to one bit (destutter), then write one true per bit
(a linear clock, hence polynomial-time at k = 1), composed. -/
theorem PvsNP.Units.m2_tm_y_run_count_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.destutter (· ≠ ·)).length true) := by
  obtain ⟨c, M, hM⟩ := PvsNP.Units.m2_linear_clock
  have hClock : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) :=
    PvsNP.Units.m2_tm_polytime_of_power_bound PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) c 1
      ⟨M, fun n => by rw [pow_one]; exact hM n⟩
  have h : (fun x : List Bool => List.replicate (x.destutter (· ≠ ·)).length true)
      = (fun y : List Bool => List.replicate y.length true) ∘
        (fun x : List Bool => x.destutter (· ≠ ·)) := by
    funext x
    simp only [Function.comp_apply]
  rw [h]
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x.destutter (· ≠ ·))
    (fun y : List Bool => List.replicate y.length true)
    PvsNP.Units.m2_tm_destutter_polytime hClock
