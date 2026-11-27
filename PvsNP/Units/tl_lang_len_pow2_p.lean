import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_down_closed

/-!
# The strings whose length is a power of two are in P

The reduction writes the input's length in binary (`m2_unary_to_binary_polytime`), and a
three-state automaton over the binary digits, adapted from the settled unit
`tl_lang_count_pow2_p`, accepts exactly the powers of two (`m2_dfa_in_p`); P is closed
downward under Karp reductions (`m2_p_down_closed`).
-/

namespace PvsNP.Units.tl_lang_len_pow2_p

/-- The automaton reading a number least significant bit first: `some false` while only
zeros have been read, `some true` right after the first one, `none` (dead) after anything
read past that one. -/
def step : Option Bool → Bool → Option Bool
  | some false, false => some false
  | some false, true => some true
  | _, _ => none

/-- The accepting state: exactly one `true` was read, and it came last. -/
def acc (q : Option Bool) : Bool := decide (q = some true)

theorem step_none (b : Bool) : step none b = none := by cases b <;> rfl

theorem step_some_true (b : Bool) : step (some true) b = none := by cases b <;> rfl

theorem step_ff : step (some false) false = some false := rfl

theorem step_ft : step (some false) true = some true := rfl

/-- The dead state is a sink. -/
theorem foldl_none (l : List Bool) : l.foldl step none = none := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.foldl_cons, step_none, ih]

/-- Once the one has been read, only the empty rest (the number zero) is accepted. -/
theorem foldl_some_true (n : ℕ) :
    (Nat.bits n).foldl step (some true) = some true ↔ n = 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Nat.bit0_bits m (by omega), List.foldl_cons, step_some_true, foldl_none]
      constructor
      · intro h
        cases h
      · intro h
        omega
  · rw [Nat.bit1_bits m, List.foldl_cons, step_some_true, foldl_none]
    constructor
    · intro h
      cases h
    · intro h
      omega

/-- The automaton accepts the binary digits of `n` exactly when `n` is a power of two. -/
theorem accept_bits (n : ℕ) :
    (Nat.bits n).foldl step (some false) = some true ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · constructor
        · intro h
          simp at h
        · rintro ⟨k, hk⟩
          have hpos := Nat.two_pow_pos k
          omega
      · rw [Nat.bit0_bits m (by omega), List.foldl_cons, step_ff, ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [Nat.pow_succ]
          omega
        · rintro ⟨k, hk⟩
          cases k with
          | zero =>
            rw [Nat.pow_zero] at hk
            omega
          | succ k =>
            rw [Nat.pow_succ] at hk
            exact ⟨k, by omega⟩
    · rw [Nat.bit1_bits m, List.foldl_cons, step_ft, foldl_some_true m]
      constructor
      · intro hm
        refine ⟨0, ?_⟩
        rw [Nat.pow_zero]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero =>
          rw [Nat.pow_zero] at hk
          omega
        | succ k =>
          rw [Nat.pow_succ] at hk
          omega

/-- The accepting form of `accept_bits`. -/
theorem acc_bits (n : ℕ) :
    acc ((Nat.bits n).foldl step (some false)) = true ↔ ∃ k : ℕ, n = 2 ^ k := by
  unfold acc
  rw [decide_eq_true_eq]
  exact accept_bits n

end PvsNP.Units.tl_lang_len_pow2_p

/-- The strings whose length is a power of two are in P: write the length in binary (the
settled unit `m2_unary_to_binary_polytime`), then run the three-state automaton above
accepting `0…01` least significant bit first, which is in P by the settled unit
`m2_dfa_in_p`; P is closed downward under Karp reductions (the settled unit
`m2_p_down_closed`). -/
theorem PvsNP.Units.tl_lang_len_pow2_p :
    ({x : List Bool | ∃ k : ℕ, x.length = 2 ^ k} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_p_down_closed _ _
    ⟨fun x : List Bool => Nat.bits x.length,
      PvsNP.Units.m2_unary_to_binary_polytime,
      fun x => (PvsNP.Units.tl_lang_len_pow2_p.acc_bits x.length).symm⟩
    (PvsNP.Units.m2_dfa_in_p (Option Bool) PvsNP.Units.tl_lang_len_pow2_p.step (some false)
      PvsNP.Units.tl_lang_len_pow2_p.acc)
