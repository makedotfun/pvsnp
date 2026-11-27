import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_pair_add

namespace PvsNP.Units.tf_fun_pair_land

open Turing
open PvsNP.Units.tf_fun_pair_add (stripZeros stripSteps stripSteps_le ofDigits_append_singleton stripZeros_reverse_eq_bits)

theorem flip_bind_some {α : Type} (f : α → Option α) (a : α) :
    flip bind f (some a) = f a := rfl

theorem bit_testBit_zero (b : Bool) (m : ℕ) :
    Nat.testBit (b.toNat + 2 * m) 0 = b := by
  cases b <;> simp [Nat.testBit_zero]

theorem bit_testBit_succ (b : Bool) (m k : ℕ) :
    Nat.testBit (b.toNat + 2 * m) (k + 1) = Nat.testBit m k := by
  rw [Nat.testBit_succ]
  have hd : (b.toNat + 2 * m) / 2 = m := by cases b <;> dsimp [Bool.toNat] <;> omega
  rw [hd]

theorem and_step (a b : Bool) (m n : ℕ) :
    (a.toNat + 2 * m) &&& (b.toNat + 2 * n) = (a && b).toNat + 2 * (m &&& n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_and, bit_testBit_zero, bit_testBit_zero, bit_testBit_zero]
  | succ k =>
    rw [Nat.testBit_and, bit_testBit_succ, bit_testBit_succ, bit_testBit_succ, Nat.testBit_and]

def binAndAcc : List Bool → List Bool → List Bool → List Bool
  | [], [], acc => acc
  | _ :: xs, [], acc => binAndAcc xs [] (false :: acc)
  | [], _ :: ys, acc => binAndAcc [] ys (false :: acc)
  | a :: xs, b :: ys, acc => binAndAcc xs ys ((a && b) :: acc)

theorem binAndAcc_val (x y acc : List Bool) :
    Nat.ofDigits (2 : ℕ) ((binAndAcc x y acc).reverse.map Bool.toNat) =
      Nat.ofDigits (2 : ℕ) (acc.reverse.map Bool.toNat) +
        2 ^ acc.length *
          (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) &&& Nat.ofDigits (2 : ℕ) (y.map Bool.toNat)) := by
  induction x generalizing y acc with
  | nil =>
    induction y generalizing acc with
    | nil =>
      simp [binAndAcc]
    | cons b ys ihy =>
      simp only [binAndAcc, List.map_nil, Nat.ofDigits_nil, Nat.zero_and, mul_zero, Nat.add_zero]
      rw [ihy (false :: acc)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, Bool.toNat_false,
        ofDigits_append_singleton, List.map_nil, Nat.ofDigits_nil, Nat.zero_and, mul_zero, Nat.add_zero]
  | cons a xs ihx =>
    cases y with
    | nil =>
      simp only [binAndAcc, List.map_nil, Nat.ofDigits_nil, Nat.and_zero, mul_zero, Nat.add_zero]
      rw [ihx [] (false :: acc)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, Bool.toNat_false,
        ofDigits_append_singleton, List.map_nil, Nat.ofDigits_nil, Nat.and_zero, mul_zero, Nat.add_zero]
    | cons b ys =>
      simp only [binAndAcc, List.map_cons, Nat.ofDigits_cons]
      rw [ihx ys ((a && b) :: acc)]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, ofDigits_append_singleton,
        List.length_map, List.length_reverse, List.length_cons, Nat.pow_succ]
      rw [and_step a b (Nat.ofDigits 2 (xs.map Bool.toNat)) (Nat.ofDigits 2 (ys.map Bool.toNat))]
      ring

theorem binAndAcc_len_le (x y acc : List Bool) :
    (binAndAcc x y acc).length ≤ acc.length + max x.length y.length := by
  induction x generalizing y acc with
  | nil =>
    induction y generalizing acc with
    | nil => simp [binAndAcc]
    | cons b ys ihy =>
      simp only [binAndAcc]
      have h := ihy (false :: acc)
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega
  | cons a xs ihx =>
    cases y with
    | nil =>
      simp only [binAndAcc]
      have h := ihx [] (false :: acc)
      simp only [List.length_cons, List.length_nil] at h ⊢
      omega
    | cons b ys =>
      simp only [binAndAcc]
      have h := ihx ys ((a && b) :: acc)
      simp only [List.length_cons] at h ⊢
      omega

theorem stripZeros_binAndAcc_eq (x y : List Bool) :
    (stripZeros (binAndAcc x y [])).reverse =
      Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) &&& Nat.ofDigits (2 : ℕ) (y.map Bool.toNat)) := by
  rw [stripZeros_reverse_eq_bits, binAndAcc_val]
  simp

inductive SStk
  | inp | rx | ry | sx | sy | out
  deriving DecidableEq

instance : Fintype SStk where
  elems := {.inp, .rx, .ry, .sx, .sy, .out}
  complete x := by cases x <;> simp

inductive SLbl
  | split | revX | revY | doOp | strip | revOut
  deriving DecidableEq

instance : Fintype SLbl where
  elems := {.split, .revX, .revY, .doOp, .strip, .revOut}
  complete x := by cases x <;> simp

abbrev SΓ : SStk → Type
  | .inp => Bool ⊕ Bool
  | _ => Bool

abbrev Sσ : Type := Option (Bool ⊕ Bool) × Option Bool × Option Bool

def initσ : Sσ := (none, none, none)

def sProg : SLbl → TM2.Stmt SΓ SLbl Sσ
  | .split =>
    .pop .inp (fun _ o => (o, none, none))
      (.branch (fun st => st.1.isSome)
        (.branch (fun st => match st.1 with | some (Sum.inl _) => true | _ => false)
          (.push .rx (fun st => match st.1 with | some (Sum.inl a) => a | _ => false)
            (.load (fun _ => initσ) (.goto fun _ => .split)))
          (.push .ry (fun st => match st.1 with | some (Sum.inr b) => b | _ => false)
            (.load (fun _ => initσ) (.goto fun _ => .split))))
        (.load (fun _ => initσ) (.goto fun _ => .revX)))
  | .revX =>
    .pop .rx (fun _ o => (none, o, none))
      (.branch (fun st => st.2.1.isSome)
        (.push .sx (fun st => st.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revX)))
        (.load (fun _ => initσ) (.goto fun _ => .revY)))
  | .revY =>
    .pop .ry (fun _ o => (none, o, none))
      (.branch (fun st => st.2.1.isSome)
        (.push .sy (fun st => st.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revY)))
        (.load (fun _ => initσ) (.goto fun _ => .doOp)))
  | .doOp =>
    .pop .sx (fun _ o => (none, o, none))
      (.pop .sy (fun st o => (none, st.2.1, o))
        (.branch (fun st => st.2.1.isSome || st.2.2.isSome)
          (.push .rx (fun st => st.2.1.getD false && st.2.2.getD false)
            (.load (fun _ => initσ) (.goto fun _ => .doOp)))
          (.load (fun _ => initσ) (.goto fun _ => .strip))))
  | .strip =>
    .pop .rx (fun _ o => (none, o, none))
      (.branch (fun st => st.2.1.isSome)
        (.branch (fun st => st.2.1.getD false)
          (.push .out (fun _ => true)
            (.load (fun _ => initσ) (.goto fun _ => .revOut)))
          (.load (fun _ => initσ) (.goto fun _ => .strip)))
        (.load (fun _ => initσ) .halt))
  | .revOut =>
    .pop .rx (fun _ o => (none, o, none))
      (.branch (fun st => st.2.1.isSome)
        (.push .out (fun st => st.2.1.getD false)
          (.load (fun _ => initσ) (.goto fun _ => .revOut)))
        (.load (fun _ => initσ) .halt))

def sTM : FinTM2 where
  K := SStk
  k₀ := .inp
  k₁ := .out
  Γ := SΓ
  Λ := SLbl
  main := .split
  σ := Sσ
  initialState := initσ
  m := sProg

abbrev SCfg : Type := TM2.Cfg SΓ SLbl Sσ

def mkStk (i : List (Bool ⊕ Bool)) (rx ry sx sy o : List Bool) : ∀ k, List (SΓ k)
  | .inp => i
  | .rx => rx
  | .ry => ry
  | .sx => sx
  | .sy => sy
  | .out => o

theorem upd_inp (i i' : List (Bool ⊕ Bool)) (rx ry sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .inp i' = mkStk i' rx ry sx sy o := by
  funext k; cases k <;> rfl

theorem upd_rx (i : List (Bool ⊕ Bool)) (rx rx' ry sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .rx rx' = mkStk i rx' ry sx sy o := by
  funext k; cases k <;> rfl

theorem upd_ry (i : List (Bool ⊕ Bool)) (rx ry ry' sx sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .ry ry' = mkStk i rx ry' sx sy o := by
  funext k; cases k <;> rfl

theorem upd_sx (i : List (Bool ⊕ Bool)) (rx ry sx sx' sy o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .sx sx' = mkStk i rx ry sx' sy o := by
  funext k; cases k <;> rfl

theorem upd_sy (i : List (Bool ⊕ Bool)) (rx ry sx sy sy' o : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .sy sy' = mkStk i rx ry sx sy' o := by
  funext k; cases k <;> rfl

theorem upd_out (i : List (Bool ⊕ Bool)) (rx ry sx sy o o' : List Bool) :
    Function.update (mkStk i rx ry sx sy o) .out o' = mkStk i rx ry sx sy o' := by
  funext k; cases k <;> rfl

theorem initList_sTM (i : List (Bool ⊕ Bool)) :
    initList sTM i = (⟨some .split, initσ, mkStk i [] [] [] [] []⟩ : SCfg) := by
  unfold initList; congr 1; funext k; cases k <;> rfl

theorem haltList_sTM (o : List Bool) :
    haltList sTM o = (⟨none, initσ, mkStk [] [] [] [] [] o⟩ : SCfg) := by
  unfold haltList; congr 1; funext k; cases k <;> rfl

theorem step_split_inl (a : Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk (Sum.inl a :: rest) rx ry [] [] []⟩ : SCfg) =
      some ⟨some .split, initσ, mkStk rest (a :: rx) ry [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true]
  rw [upd_inp, upd_rx]; rfl

theorem step_split_inr (b : Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk (Sum.inr b :: rest) rx ry [] [] []⟩ : SCfg) =
      some ⟨some .split, initσ, mkStk rest rx (b :: ry) [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Bool.cond_false]
  rw [upd_inp, upd_ry]; rfl

theorem step_split_nil (rx ry : List Bool) :
    TM2.step sProg (⟨some .split, initσ, mkStk [] rx ry [] [] []⟩ : SCfg) =
      some ⟨some .revX, initσ, mkStk [] rx ry [] [] []⟩ := by
  simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_inp]

theorem loop_split_inl (x : List Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    (flip bind (TM2.step sProg))^[x.length]
        (some (⟨some .split, initσ, mkStk (x.map Sum.inl ++ rest) rx ry [] [] []⟩ : SCfg)) =
      some ⟨some .split, initσ, mkStk rest (x.reverse ++ rx) ry [] [] []⟩ := by
  induction x generalizing rx with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .split, initσ, mkStk (Sum.inl a :: (xs.map Sum.inl ++ rest)) rx ry [] [] []⟩ : SCfg)) =
        some ⟨some .split, initσ, mkStk (xs.map Sum.inl ++ rest) (a :: rx) ry [] [] []⟩ :=
      step_split_inl a (xs.map Sum.inl ++ rest) rx ry
    rw [e, ih (a :: rx)]; simp

theorem loop_split_inr (y : List Bool) (rx ry : List Bool) :
    (flip bind (TM2.step sProg))^[y.length + 1]
        (some (⟨some .split, initσ, mkStk (y.map Sum.inr) rx ry [] [] []⟩ : SCfg)) =
      some ⟨some .revX, initσ, mkStk [] rx (y.reverse ++ ry) [] [] []⟩ := by
  induction y generalizing ry with
  | nil => exact step_split_nil rx ry
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .split, initσ, mkStk (Sum.inr b :: ys.map Sum.inr) rx ry [] [] []⟩ : SCfg)) =
        some ⟨some .split, initσ, mkStk (ys.map Sum.inr) rx (b :: ry) [] [] []⟩ :=
      step_split_inr b (ys.map Sum.inr) rx ry
    rw [e, ih (b :: ry)]; simp

theorem loop_revX (rx ry sx : List Bool) :
    (flip bind (TM2.step sProg))^[rx.length + 1]
        (some (⟨some .revX, initσ, mkStk [] rx ry sx [] []⟩ : SCfg)) =
      some ⟨some .revY, initσ, mkStk [] [] ry (rx.reverse ++ sx) [] []⟩ := by
  induction rx generalizing sx with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil, List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_rx]
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revX, initσ, mkStk [] (a :: xs) ry sx [] []⟩ : SCfg)) =
        some ⟨some .revX, initσ, mkStk [] xs ry (a :: sx) [] []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_rx, upd_sx]; rfl
    rw [e, ih (a :: sx)]; simp

theorem loop_revY (ry sx sy : List Bool) :
    (flip bind (TM2.step sProg))^[ry.length + 1]
        (some (⟨some .revY, initσ, mkStk [] [] ry sx sy []⟩ : SCfg)) =
      some ⟨some .doOp, initσ, mkStk [] [] [] sx (ry.reverse ++ sy) []⟩ := by
  induction ry generalizing sy with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil, List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_ry]
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revY, initσ, mkStk [] [] (b :: ys) sx sy []⟩ : SCfg)) =
        some ⟨some .revY, initσ, mkStk [] [] ys sx (b :: sy) []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_ry, upd_sy]; rfl
    rw [e, ih (b :: sy)]; simp

theorem loop_doOp (sx sy acc : List Bool) :
    (flip bind (TM2.step sProg))^[max sx.length sy.length + 1]
        (some (⟨some .doOp, initσ, mkStk [] acc [] sx sy []⟩ : SCfg)) =
      some ⟨some .strip, initσ, mkStk [] (binAndAcc sx sy acc) [] [] [] []⟩ := by
  induction sx generalizing sy acc with
  | nil =>
    induction sy generalizing acc with
    | nil =>
      simp only [List.length_nil, max_self, Nat.zero_add, Function.iterate_one, binAndAcc, flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux]
      rw [upd_sx]
      simp only [mkStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.or_self, Bool.cond_false]
      rw [upd_sy]
    | cons b ys ihy =>
      have hmax : max ([] : List Bool).length (b :: ys).length + 1 =
          (max ([] : List Bool).length ys.length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doOp, initσ, mkStk [] acc [] [] (b :: ys) []⟩ : SCfg)) =
          some ⟨some .doOp, initσ, mkStk [] (false :: acc) [] [] ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.false_or, Bool.cond_true,
          Option.getD_some, Option.getD_none, Bool.false_and]
        rw [upd_sy]; simp only [mkStk]; rw [upd_rx]
      rw [e, ihy (false :: acc)]
      simp only [binAndAcc]
  | cons a xs ihx =>
    cases sy with
    | nil =>
      have hmax : max (a :: xs).length ([] : List Bool).length + 1 =
          (max xs.length ([] : List Bool).length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doOp, initσ, mkStk [] acc [] (a :: xs) [] []⟩ : SCfg)) =
          some ⟨some .doOp, initσ, mkStk [] (false :: acc) [] xs [] []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.cond_true,
          Option.getD_some, Option.getD_none, Bool.and_false]
        rw [upd_sy]; simp only [mkStk]; rw [upd_rx]
      rw [e, ihx [] (false :: acc)]
      simp only [binAndAcc]
    | cons b ys =>
      have hmax : max (a :: xs).length (b :: ys).length + 1 =
          (max xs.length ys.length + 1) + 1 := by simp only [List.length_cons]; omega
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .doOp, initσ, mkStk [] acc [] (a :: xs) (b :: ys) []⟩ : SCfg)) =
          some ⟨some .doOp, initσ, mkStk [] ((a && b) :: acc) [] xs ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.or_self,
          Bool.cond_true, Option.getD_some]
        rw [upd_sy]; simp only [mkStk]; rw [upd_rx]
      rw [e, ihx ys ((a && b) :: acc)]
      simp only [binAndAcc]

theorem loop_revOut (rx out : List Bool) :
    (flip bind (TM2.step sProg))^[rx.length + 1]
        (some (⟨some .revOut, initσ, mkStk [] rx [] [] [] out⟩ : SCfg)) =
      some ⟨none, initσ, mkStk [] [] [] [] [] (rx.reverse ++ out)⟩ := by
  induction rx generalizing out with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil, List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_rx]
  | cons b xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sProg)
        (some (⟨some .revOut, initσ, mkStk [] (b :: xs) [] [] [] out⟩ : SCfg)) =
        some ⟨some .revOut, initσ, mkStk [] xs [] [] [] (b :: out)⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_rx, upd_out]; rfl
    rw [e, ih (b :: out)]; simp

theorem loop_strip (r : List Bool) :
    (flip bind (TM2.step sProg))^[stripSteps r]
        (some (⟨some .strip, initσ, mkStk [] r [] [] [] []⟩ : SCfg)) =
      some ⟨none, initσ, mkStk [] [] [] [] [] (stripZeros r).reverse⟩ := by
  induction r with
  | nil =>
    simp only [stripSteps, Function.iterate_one, stripZeros, List.reverse_nil, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_rx]
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [stripSteps, stripZeros]
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .strip, initσ, mkStk [] (false :: rest) [] [] [] []⟩ : SCfg)) =
          some ⟨some .strip, initσ, mkStk [] rest [] [] [] []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
          Option.isSome_some, Bool.cond_true, Option.getD_some, Bool.cond_false]
        rw [upd_rx]
      rw [e]; exact ih
    | true =>
      simp only [stripSteps, stripZeros, List.reverse_cons]
      have hst : rest.length + 2 = (rest.length + 1) + 1 := rfl
      rw [hst, Function.iterate_succ_apply]
      have e : flip bind (TM2.step sProg)
          (some (⟨some .strip, initσ, mkStk [] (true :: rest) [] [] [] []⟩ : SCfg)) =
          some ⟨some .revOut, initσ, mkStk [] rest [] [] [] [true]⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
          Option.isSome_some, Bool.cond_true, Option.getD_some]
        rw [upd_rx, upd_out]; rfl
      rw [e]; exact loop_revOut rest [true]

theorem sTM_run (x y : List Bool) :
    (flip bind (TM2.step sProg))^[
        stripSteps (binAndAcc x y []) +
        (max x.length y.length + 1) +
        (y.length + 1) +
        (x.length + 1) +
        (y.length + 1) +
        x.length]
        (some (initList sTM (PvsNP.encodePair (x, y)))) =
      some (haltList sTM (stripZeros (binAndAcc x y [])).reverse) := by
  have henc : PvsNP.encodePair (x, y) = x.map Sum.inl ++ y.map Sum.inr := by
    simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
  refine (congrArg (fun c => (flip bind (TM2.step sProg))^[
      stripSteps (binAndAcc x y []) + (max x.length y.length + 1) +
      (y.length + 1) + (x.length + 1) + (y.length + 1) + x.length]
      (some c)) (initList_sTM (PvsNP.encodePair (x, y)))).trans
    (Eq.trans ?_ (congrArg some (haltList_sTM (stripZeros (binAndAcc x y [])).reverse)).symm)
  rw [henc]
  rw [Function.iterate_add_apply, loop_split_inl x (y.map Sum.inr) [] []]
  rw [List.append_nil]
  rw [Function.iterate_add_apply, loop_split_inr y x.reverse []]
  rw [List.append_nil]
  have hrevX := loop_revX x.reverse y.reverse []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevX
  rw [Function.iterate_add_apply, hrevX]
  have hrevY := loop_revY y.reverse x []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevY
  rw [Function.iterate_add_apply, hrevY]
  rw [Function.iterate_add_apply, loop_doOp x y []]
  exact loop_strip (binAndAcc x y [])

theorem pair_land_aux :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) &&& Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  ⟨{
    tm := sTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 6
    outputsFun := fun p =>
      { steps :=
          stripSteps (binAndAcc p.1 p.2 []) +
          (max p.1.length p.2.length + 1) +
          (p.2.length + 1) +
          (p.1.length + 1) +
          (p.2.length + 1) +
          p.1.length
        evals_in_steps := by
          have hm1 : List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair p) =
              PvsNP.encodePair p := by simp
          have hm2 : List.map (Equiv.refl Bool).invFun
              (PvsNP.encodeString (Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) &&&
                Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) =
              (stripZeros (binAndAcc p.1 p.2 [])).reverse := by
            simp [PvsNP.encodeString, Computability.encodingList, stripZeros_binAndAcc_eq]
          exact (congrArg (fun i => (flip bind (TM2.step sProg))^[
              stripSteps (binAndAcc p.1 p.2 []) + (max p.1.length p.2.length + 1) +
              (p.2.length + 1) + (p.1.length + 1) + (p.2.length + 1) + p.1.length]
              (some (initList sTM i))) hm1).trans
            ((sTM_run p.1 p.2).trans
              (congrArg (fun o => some (haltList sTM o)) hm2.symm))
        steps_le_m := by
          have hlen : (PvsNP.encodePair p).length = p.1.length + p.2.length := by
            simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
          have hs1 := stripSteps_le (binAndAcc p.1 p.2 [])
          have hs2 := binAndAcc_len_le p.1 p.2 []
          simp only [List.length_nil, Nat.zero_add] at hs2
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, hlen]
          omega } }⟩

end PvsNP.Units.tf_fun_pair_land

theorem PvsNP.Units.tf_fun_pair_land :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) &&& Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.tf_fun_pair_land.pair_land_aux
