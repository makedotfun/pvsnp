import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_np_in_exp
import PvsNP.Units.m2_eb_final
import PvsNP.Units.tl_lang_composite_np

namespace PvsNP.Units.m2_x_composite_in_exp

theorem exp_bound (k n : ℕ) : n ^ k + k ≤ (k + 1) * (n + 1) ^ k := by
  have h1 : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
  have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
  nlinarith

end PvsNP.Units.m2_x_composite_in_exp

theorem PvsNP.Units.m2_x_composite_in_exp : ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
  (∀ x : List Bool, x ∈ ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨f, hf, M, k, hk⟩ := PvsNP.Units.fr_np_in_exp _ PvsNP.Units.tl_lang_composite_np
  obtain ⟨j, hj⟩ := PvsNP.Units.m2_eb_final M.time ⟨k + 1, k, fun n =>
    (hk n).trans (Nat.pow_le_pow_right (by norm_num)
      (PvsNP.Units.m2_x_composite_in_exp.exp_bound k n))⟩
  exact ⟨j, f, M, hf, hj⟩
