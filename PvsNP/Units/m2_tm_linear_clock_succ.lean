import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_linear_clock
import PvsNP.Units.m2_cons_true_time
import PvsNP.Units.m2_tm_timed_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_linear_clock_succ

end PvsNP.Units.m2_tm_linear_clock_succ

/-- Writing `n + 1` trues for an input of length `n` takes linear time: first write `n` trues
(the settled `m2_linear_clock`), then put one more `true` in front (the settled
`m2_cons_true_time`), composed by the settled `m2_tm_timed_comp` with `len n = n`.
`List.replicate (n + 1) true` is `true :: List.replicate n true` by definition, and
`c = c₀ + 5` bounds `(c₀ * n + c₀) + 2 * n + 2 + (2 * n + 3)`. -/
theorem PvsNP.Units.m2_tm_linear_clock_succ :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (x.length + 1) true)),
      ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨c₀, M₁, hM₁⟩ := PvsNP.Units.m2_linear_clock
  obtain ⟨M₂, hM₂⟩ := PvsNP.Units.m2_cons_true_time
  have hmono : Monotone (fun n : ℕ => 2 * n + 3) := by
    intro a b h
    show 2 * a + 3 ≤ 2 * b + 3
    omega
  have hlen : ∀ x : List Bool,
      ((fun x : List Bool => List.replicate x.length true) x).length ≤ (fun n : ℕ => n) x.length := by
    intro x
    simp
  obtain ⟨M, hM⟩ := PvsNP.Units.m2_tm_timed_comp
    (fun x : List Bool => List.replicate x.length true) (fun y : List Bool => true :: y)
    (fun n : ℕ => c₀ * n + c₀) (fun n : ℕ => 2 * n + 3) (fun n : ℕ => n)
    hmono hlen ⟨M₁, fun n => hM₁ n⟩ ⟨M₂, fun n => hM₂ n⟩
  have hbound : ∀ n : ℕ,
      (c₀ * n + c₀) + 2 * n + 2 + (2 * n + 3) ≤ (c₀ + 5) * n + (c₀ + 5) := by
    intro n
    have h5 : (c₀ + 5) * n = c₀ * n + 5 * n := by ring
    rw [h5]
    omega
  show ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => true :: List.replicate x.length true)),
    ∀ n : ℕ, M.time n ≤ c * n + c
  exact ⟨c₀ + 5, M, fun n => (hM n).trans (hbound n)⟩
