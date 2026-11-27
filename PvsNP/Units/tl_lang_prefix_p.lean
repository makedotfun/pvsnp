import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

namespace PvsNP.Units.tl_lang_prefix_p

/-- The states of the prefix scan: `s0` nothing read, `s1` read `[true]`,
    `s2` read `[true, true]` (accepting), `s3` dead. -/
inductive St | s0 | s1 | s2 | s3
  deriving DecidableEq, Fintype

/-- One step of the prefix scan. -/
def step : St → Bool → St
  | .s0, true => .s1
  | .s0, false => .s3
  | .s1, true => .s2
  | .s1, false => .s3
  | .s2, _ => .s2
  | .s3, _ => .s3

/-- Accept when the prefix `[true, true]` was read. -/
def acc (q : St) : Bool := decide (q = .s2)

theorem step_s0_true : step .s0 true = .s1 := rfl

theorem step_s0_false : step .s0 false = .s3 := rfl

theorem step_s1_true : step .s1 true = .s2 := rfl

theorem step_s1_false : step .s1 false = .s3 := rfl

theorem step_s2 (b : Bool) : step .s2 b = .s2 := by cases b <;> rfl

theorem step_s3 (b : Bool) : step .s3 b = .s3 := by cases b <;> rfl

theorem foldl_s2 (x : List Bool) : x.foldl step .s2 = .s2 := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [List.foldl_cons, step_s2, ih]

theorem foldl_s3 (x : List Bool) : x.foldl step .s3 = .s3 := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [List.foldl_cons, step_s3, ih]

/-- The automaton accepts exactly the strings starting with `[true, true]`. -/
theorem foldl_eq_s2_iff (x : List Bool) :
    x.foldl step .s0 = .s2 ↔ [true, true] <+: x := by
  cases x with
  | nil => simp
  | cons b x =>
    cases x with
    | nil =>
      cases b with
      | false =>
        have h1 : ([false] : List Bool).foldl step .s0 = .s3 := by
          simp [step_s0_false]
        have h2 : ¬ ([true, true] <+: [false]) := fun h => by
          have hle := h.length_le
          simp at hle
        rw [h1]
        simp [h2]
      | true =>
        have h1 : ([true] : List Bool).foldl step .s0 = .s1 := by
          simp [step_s0_true]
        have h2 : ¬ ([true, true] <+: [true]) := fun h => by
          have hle := h.length_le
          simp at hle
        rw [h1]
        simp [h2]
    | cons c rest =>
      cases b with
      | false =>
        have h1 : (false :: c :: rest).foldl step .s0 = .s3 := by
          simp [step_s0_false, step_s3, foldl_s3]
        have h2 : ¬ ([true, true] <+: false :: c :: rest) := by
          rintro ⟨t, h⟩
          simp at h
        rw [h1]
        simp [h2]
      | true =>
        cases c with
        | false =>
          have h1 : (true :: false :: rest).foldl step .s0 = .s3 := by
            simp [step_s0_true, step_s1_false, step_s3, foldl_s3]
          have h2 : ¬ ([true, true] <+: true :: false :: rest) := by
            rintro ⟨t, h⟩
            simp at h
          rw [h1]
          simp [h2]
        | true =>
          have h1 : (true :: true :: rest).foldl step .s0 = .s2 := by
            simp [step_s0_true, step_s1_true, step_s2, foldl_s2]
          have h2 : [true, true] <+: true :: true :: rest := ⟨rest, rfl⟩
          rw [h1]
          simp [h2]

end PvsNP.Units.tl_lang_prefix_p

/-- The strings beginning with `[true, true]` are in P: a four-state automaton
    reading the first two bits, decided by the settled unit `m2_dfa_in_p`. -/
theorem PvsNP.Units.tl_lang_prefix_p :
    ({x : List Bool | [true, true] <+: x} : Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | [true, true] <+: x} : Language Bool)
      = {x : List Bool |
          PvsNP.Units.tl_lang_prefix_p.acc
            (x.foldl PvsNP.Units.tl_lang_prefix_p.step
              PvsNP.Units.tl_lang_prefix_p.St.s0) = true} := by
    ext x
    simp only [Set.mem_setOf_eq, PvsNP.Units.tl_lang_prefix_p.acc, decide_eq_true_eq]
    exact PvsNP.Units.tl_lang_prefix_p.foldl_eq_s2_iff x
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p PvsNP.Units.tl_lang_prefix_p.St
    PvsNP.Units.tl_lang_prefix_p.step PvsNP.Units.tl_lang_prefix_p.St.s0
    PvsNP.Units.tl_lang_prefix_p.acc
