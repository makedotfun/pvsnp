import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_prefix_p

/-- DFA states: nothing of the prefix matched yet, `[true]` matched,
`[true, true]` matched (accepting), dead. -/
inductive St
  | s0 | s1 | s2 | s3
  deriving DecidableEq

instance : Fintype St where
  elems := {St.s0, St.s1, St.s2, St.s3}
  complete := by
    intro x
    cases x <;> simp

/-- Transition of the prefix DFA. -/
def δ : St → Bool → St
  | .s0, false => .s3
  | .s0, true => .s1
  | .s1, false => .s3
  | .s1, true => .s2
  | .s2, _ => .s2
  | .s3, _ => .s3

/-- Accept only in the matched state. -/
def F : St → Bool
  | .s2 => true
  | _ => false

/-- The accepting state is absorbing. -/
theorem foldl_s2 (y : List Bool) : y.foldl δ St.s2 = St.s2 := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    have h : δ St.s2 b = St.s2 := by cases b <;> rfl
    rw [List.foldl_cons, h]
    exact ih

/-- The dead state is absorbing. -/
theorem foldl_s3 (y : List Bool) : y.foldl δ St.s3 = St.s3 := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    have h : δ St.s3 b = St.s3 := by cases b <;> rfl
    rw [List.foldl_cons, h]
    exact ih

/-- The DFA accepts exactly the strings beginning with `[true, true]`. -/
theorem correct (x : List Bool) :
    F (x.foldl δ St.s0) = true ↔ [true, true] <+: x := by
  cases x with
  | nil =>
    refine iff_of_false ?_ ?_
    · simp [F]
    · rintro ⟨u, hu⟩
      simp at hu
  | cons a x =>
    cases x with
    | nil =>
      cases a with
      | false =>
        have e : δ St.s0 false = St.s3 := rfl
        rw [List.foldl_cons, e]
        refine iff_of_false ?_ ?_
        · simp [F]
        · rintro ⟨u, hu⟩
          simp at hu
      | true =>
        have e : δ St.s0 true = St.s1 := rfl
        rw [List.foldl_cons, e]
        refine iff_of_false ?_ ?_
        · simp [F]
        · rintro ⟨u, hu⟩
          simp at hu
    | cons b t =>
      cases a with
      | false =>
        have e : δ St.s0 false = St.s3 := rfl
        have e3 : δ St.s3 b = St.s3 := by cases b <;> rfl
        rw [List.foldl_cons, List.foldl_cons, e, e3, foldl_s3]
        refine iff_of_false ?_ ?_
        · simp [F]
        · rintro ⟨u, hu⟩
          simp at hu
      | true =>
        cases b with
        | false =>
          have e1 : δ St.s0 true = St.s1 := rfl
          have e2 : δ St.s1 false = St.s3 := rfl
          rw [List.foldl_cons, List.foldl_cons, e1, e2, foldl_s3]
          refine iff_of_false ?_ ?_
          · simp [F]
          · rintro ⟨u, hu⟩
            simp at hu
        | true =>
          have e1 : δ St.s0 true = St.s1 := rfl
          have e2 : δ St.s1 true = St.s2 := rfl
          rw [List.foldl_cons, List.foldl_cons, e1, e2, foldl_s2]
          exact iff_of_true rfl ⟨t, rfl⟩

end PvsNP.Units.tl_lang_prefix_p

open PvsNP.Units.tl_lang_prefix_p

theorem PvsNP.Units.tl_lang_prefix_p :
    ({x : List Bool | [true, true] <+: x} : Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | [true, true] <+: x} : Language Bool)
      = {x : List Bool | F (x.foldl δ St.s0) = true} := by
    ext x
    exact (correct x).symm
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p St δ St.s0 F
