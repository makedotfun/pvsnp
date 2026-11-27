import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-!
# The strings whose binary value is divisible by three are in P

A one-pass weighted automaton: the state carries the running value modulo three together
with the weight `2^i` of the next bit reduced modulo three (a flag: `false` is `1`,
`true` is `2`). Reading a bit adds the bit times the weight and doubles the weight, so
after the whole string the first component is `Nat.ofDigits 2 (x.map Bool.toNat)`
reduced modulo three. Decided by the settled unit `m2_dfa_in_p`.
-/

namespace PvsNP.Units.tl_lang_val_mod_p

/-- The weight `2^i` of the bit at position `i`, reduced modulo three, carried as a flag:
`false` is `1`, `true` is `2`. -/
def wt (w : Bool) : ℕ := if w then 2 else 1

/-- One input bit: add the bit times the current weight (modulo three), then double the
weight (modulo three), which flips the flag. -/
def step : Fin 3 × Bool → Bool → Fin 3 × Bool
  | (a, false), false => (a, true)
  | (a, false), true => (a + 1, true)
  | (a, true), false => (a, false)
  | (a, true), true => (a + 2, false)

/-- Reading a prefix leaves, in the first component, the seed plus the prefix's value
(the seed's weight times `Nat.ofDigits 2` of the prefix), all reduced modulo three. -/
theorem key (x : List Bool) (s : Fin 3 × Bool) :
    (x.foldl step s).1.val
      = (s.1.val + wt s.2 * Nat.ofDigits 2 (x.map Bool.toNat)) % 3 := by
  induction x generalizing s with
  | nil =>
      simp only [List.foldl_nil, wt, Nat.ofDigits_nil, mul_zero, add_zero,
        Nat.mod_eq_of_lt s.1.isLt]
  | cons b l ih =>
      rw [List.foldl_cons, ih (step s b)]
      obtain ⟨a, w⟩ := s
      cases w <;> cases b <;>
        simp only [step, wt, Fin.val_add, Nat.add_mod_left, List.map_cons,
          Nat.ofDigits_cons, mul_add, Bool.not_true, Bool.not_false, if_true, if_false,
          Bool.toNat, Nat.mul_one, Nat.mul_zero, Nat.mul_comm] <;>
        omega

end PvsNP.Units.tl_lang_val_mod_p

/-- The strings whose binary value is divisible by three are in P: the weighted automaton
above tracks the value modulo three in one pass, decided by the settled unit
`m2_dfa_in_p`. -/
theorem PvsNP.Units.tl_lang_val_mod_p :
    ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 = 0} : Language Bool) ∈
      PvsNP.P := by
  have heq : ({x : List Bool | Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) % 3 = 0} :
      Language Bool)
      = {x : List Bool | (fun s : Fin 3 × Bool => decide (s.1.val = 0))
          (List.foldl step ((0 : Fin 3), false) x) = true} := by
    ext x
    have hk := key x ((0 : Fin 3), false)
    simp only [Set.mem_setOf_eq, decide_eq_true_eq] at *
    rw [hk]
    simp only [wt, if_false, Fin.val_zero, Nat.zero_add, one_mul]
  rw [heq]
  exact PvsNP.Units.m2_dfa_in_p (Fin 3 × Bool) step ((0 : Fin 3), false)
    (fun s => decide (s.1.val = 0))
