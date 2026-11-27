import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.tl_lang_val_pow_p

namespace PvsNP.Units.tl_lang_val_tri_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.tl_lang_val_pow_p

def triMap (x : List Bool) : List Bool :=
  true :: false :: false :: x

theorem triMap_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString triMap :=
  cpt_cons1 true (cpt_cons1 false (cpt_cons1 false cpt_id))

theorem val_triMap (x : List Bool) : val (triMap x) = 8 * val x + 1 := by
  unfold triMap
  rw [val_cons, val_cons, val_cons]
  simp only [Bool.toNat_true, Bool.toNat_false]
  ring

theorem tri_iff_sq (V : ℕ) :
    (∃ k : ℕ, 2 * V = k * (k + 1)) ↔ ∃ m : ℕ, 8 * V + 1 = m ^ 2 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨2 * k + 1, ?_⟩
    have h4 : 8 * V = 4 * (k * (k + 1)) := by omega
    nlinarith
  · rintro ⟨m, hm⟩
    have hodd : m % 2 = 1 := by
      by_contra heven
      have hm0 : m % 2 = 0 := by omega
      have hdiv : m = 2 * (m / 2) := by omega
      rw [hdiv] at hm
      have h4 : (2 * (m / 2)) ^ 2 = 4 * ((m / 2) ^ 2) := by ring
      omega
    refine ⟨m / 2, ?_⟩
    have hm_eq : m = 2 * (m / 2) + 1 := by omega
    rw [hm_eq] at hm
    nlinarith

theorem val_tri_main :
    ({x : List Bool | ∃ k : ℕ, 2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k * (k + 1)} :
      Language Bool) ∈ PvsNP.P := by
  refine PvsNP.Units.m2_pair_build_polytime.p_down_closed
    ⟨triMap, triMap_poly, fun x => ?_⟩ PvsNP.Units.tl_lang_val_pow_p
  change (∃ k : ℕ, 2 * val x = k * (k + 1)) ↔ ∃ m : ℕ, val (triMap x) = m ^ 2
  rw [val_triMap]
  exact tri_iff_sq (val x)

end PvsNP.Units.tl_lang_val_tri_p

theorem PvsNP.Units.tl_lang_val_tri_p :
    ({x : List Bool | ∃ k : ℕ, 2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k * (k + 1)} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_tri_p.val_tri_main
