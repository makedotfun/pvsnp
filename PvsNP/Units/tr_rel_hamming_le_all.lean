import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.tr_rel_hamming_le_all

open Turing

theorem flip_bind_some {α : Type} (f : α → Option α) (a : α) :
    flip bind f (some a) = f a := rfl

def bumpMis (d : ℕ) (m : Fin (d + 2)) (diff : Bool) : Fin (d + 2) :=
  if diff then ⟨min (m.val + 1) (d + 1), by omega⟩ else m

def hamDec (d : ℕ) : List Bool → List Bool → Fin (d + 2) → Bool
  | [], [], m => decide (m.val ≤ d)
  | _ :: _, [], _ => false
  | [], _ :: _, _ => false
  | a :: xs, b :: ys, m => hamDec d xs ys (bumpMis d m (a != b))

theorem hamDec_iff (d : ℕ) (x y : List Bool) (m : Fin (d + 2)) :
    (x.length = y.length ∧ m.val + (List.zipWith (fun a b => a != b) x y).count true ≤ d) ↔
      hamDec d x y m = true := by
  induction x generalizing y m with
  | nil =>
    cases y with
    | nil =>
      simp [hamDec]
    | cons b ys =>
      simp [hamDec]
  | cons a xs ih =>
    cases y with
    | nil =>
      simp [hamDec]
    | cons b ys =>
      simp only [hamDec, List.length_cons, Nat.succ.injEq, List.zipWith_cons_cons, ← ih]
      cases hdiff : (a != b) with
      | false =>
        simp [bumpMis]
      | true =>
        simp only [bumpMis, ↓reduceIte, List.count_cons_self]
        omega

inductive SStk
  | inp | rx | ry | sx | sy | out
  deriving DecidableEq

instance : Fintype SStk where
  elems := {.inp, .rx, .ry, .sx, .sy, .out}
  complete x := by cases x <;> simp

inductive SLbl
  | split | revX | revY | doCmp | drain
  deriving DecidableEq

instance : Fintype SLbl where
  elems := {.split, .revX, .revY, .doCmp, .drain}
  complete x := by cases x <;> simp

abbrev SΓ : SStk → Type
  | .inp => Bool ⊕ Bool
  | _ => Bool

abbrev Sσ (d : ℕ) : Type := Fin (d + 2) × Option (Bool ⊕ Bool) × Option Bool × Option Bool

def zeroFin (d : ℕ) : Fin (d + 2) := ⟨0, by omega⟩

def initσ (d : ℕ) : Sσ d := (zeroFin d, none, none, none)

def sProg (d : ℕ) : SLbl → TM2.Stmt SΓ SLbl (Sσ d)
  | .split =>
    .pop .inp (fun _ o => (zeroFin d, o, none, none))
      (.branch (fun st => st.2.1.isSome)
        (.branch (fun st => match st.2.1 with | some (Sum.inl _) => true | _ => false)
          (.push .rx (fun st => match st.2.1 with | some (Sum.inl a) => a | _ => false)
            (.load (fun _ => initσ d) (.goto fun _ => .split)))
          (.push .ry (fun st => match st.2.1 with | some (Sum.inr b) => b | _ => false)
            (.load (fun _ => initσ d) (.goto fun _ => .split))))
        (.load (fun _ => initσ d) (.goto fun _ => .revX)))
  | .revX =>
    .pop .rx (fun _ o => (zeroFin d, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.push .sx (fun st => st.2.2.1.getD false)
          (.load (fun _ => initσ d) (.goto fun _ => .revX)))
        (.load (fun _ => initσ d) (.goto fun _ => .revY)))
  | .revY =>
    .pop .ry (fun _ o => (zeroFin d, none, o, none))
      (.branch (fun st => st.2.2.1.isSome)
        (.push .sy (fun st => st.2.2.1.getD false)
          (.load (fun _ => initσ d) (.goto fun _ => .revY)))
        (.load (fun _ => initσ d) (.goto fun _ => .doCmp)))
  | .doCmp =>
    .pop .sx (fun st o => (st.1, none, o, none))
      (.pop .sy (fun st o => (st.1, none, st.2.2.1, o))
        (.branch (fun st => st.2.2.1.isSome && st.2.2.2.isSome)
          (.load (fun st => (bumpMis d st.1 (st.2.2.1.getD false != st.2.2.2.getD false), none, none, none))
            (.goto fun _ => .doCmp))
          (.branch (fun st => st.2.2.1.isSome || st.2.2.2.isSome)
            (.load (fun _ => initσ d) (.goto fun _ => .drain))
            (.push .out (fun st => decide (st.1.val ≤ d))
              (.load (fun _ => initσ d) .halt)))))
  | .drain =>
    .pop .sx (fun _ o => (zeroFin d, none, o, none))
      (.pop .sy (fun st o => (zeroFin d, none, st.2.2.1, o))
        (.branch (fun st => st.2.2.1.isSome || st.2.2.2.isSome)
          (.load (fun _ => initσ d) (.goto fun _ => .drain))
          (.push .out (fun _ => false)
            (.load (fun _ => initσ d) .halt))))

def sTM (d : ℕ) : FinTM2 where
  K := SStk
  k₀ := .inp
  k₁ := .out
  Γ := SΓ
  Λ := SLbl
  main := .split
  σ := Sσ d
  initialState := initσ d
  m := sProg d

abbrev SCfg (d : ℕ) : Type := TM2.Cfg SΓ SLbl (Sσ d)

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

theorem initList_sTM (d : ℕ) (i : List (Bool ⊕ Bool)) :
    initList (sTM d) i = (⟨some .split, initσ d, mkStk i [] [] [] [] []⟩ : SCfg d) := by
  unfold initList; congr 1; funext k; cases k <;> rfl

theorem haltList_sTM (d : ℕ) (o : List Bool) :
    haltList (sTM d) o = (⟨none, initσ d, mkStk [] [] [] [] [] o⟩ : SCfg d) := by
  unfold haltList; congr 1; funext k; cases k <;> rfl

theorem loop_split_inl (d : ℕ) (x : List Bool) (rest : List (Bool ⊕ Bool)) (rx ry : List Bool) :
    (flip bind (TM2.step (sProg d)))^[x.length]
        (some (⟨some .split, initσ d, mkStk (x.map Sum.inl ++ rest) rx ry [] [] []⟩ : SCfg d)) =
      some ⟨some .split, initσ d, mkStk rest (x.reverse ++ rx) ry [] [] []⟩ := by
  induction x generalizing rx with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append]
    have e : flip bind (TM2.step (sProg d))
        (some (⟨some .split, initσ d, mkStk (Sum.inl a :: (xs.map Sum.inl ++ rest)) rx ry [] [] []⟩ : SCfg d)) =
        some ⟨some .split, initσ d, mkStk (xs.map Sum.inl ++ rest) (a :: rx) ry [] [] []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true]
      rw [upd_inp, upd_rx]; rfl
    rw [e, ih (a :: rx)]; simp

theorem loop_split_inr (d : ℕ) (y : List Bool) (rx ry : List Bool) :
    (flip bind (TM2.step (sProg d)))^[y.length + 1]
        (some (⟨some .split, initσ d, mkStk (y.map Sum.inr) rx ry [] [] []⟩ : SCfg d)) =
      some ⟨some .revX, initσ d, mkStk [] rx (y.reverse ++ ry) [] [] []⟩ := by
  induction y generalizing ry with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.map_nil, List.reverse_nil,
      List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_inp]
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons]
    have e : flip bind (TM2.step (sProg d))
        (some (⟨some .split, initσ d, mkStk (Sum.inr b :: ys.map Sum.inr) rx ry [] [] []⟩ : SCfg d)) =
        some ⟨some .split, initσ d, mkStk (ys.map Sum.inr) rx (b :: ry) [] [] []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Bool.cond_false]
      rw [upd_inp, upd_ry]; rfl
    rw [e, ih (b :: ry)]; simp

theorem loop_revX (d : ℕ) (rx ry sx : List Bool) :
    (flip bind (TM2.step (sProg d)))^[rx.length + 1]
        (some (⟨some .revX, initσ d, mkStk [] rx ry sx [] []⟩ : SCfg d)) =
      some ⟨some .revY, initσ d, mkStk [] [] ry (rx.reverse ++ sx) [] []⟩ := by
  induction rx generalizing sx with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil, List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_rx]
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (sProg d))
        (some (⟨some .revX, initσ d, mkStk [] (a :: xs) ry sx [] []⟩ : SCfg d)) =
        some ⟨some .revX, initσ d, mkStk [] xs ry (a :: sx) [] []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_rx, upd_sx]; rfl
    rw [e, ih (a :: sx)]; simp

theorem loop_revY (d : ℕ) (ry sx sy : List Bool) :
    (flip bind (TM2.step (sProg d)))^[ry.length + 1]
        (some (⟨some .revY, initσ d, mkStk [] [] ry sx sy []⟩ : SCfg d)) =
      some ⟨some .doCmp, initσ d, mkStk [] [] [] sx (ry.reverse ++ sy) []⟩ := by
  induction ry generalizing sy with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil, List.nil_append, flip_bind_some]
    simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
    rw [upd_ry]
  | cons b ys ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (sProg d))
        (some (⟨some .revY, initσ d, mkStk [] [] (b :: ys) sx sy []⟩ : SCfg d)) =
        some ⟨some .revY, initσ d, mkStk [] [] ys sx (b :: sy) []⟩ := by
      rw [flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_ry, upd_sy]; rfl
    rw [e, ih (b :: sy)]; simp

theorem loop_drain (d : ℕ) (sx sy : List Bool) :
    (flip bind (TM2.step (sProg d)))^[max sx.length sy.length + 1]
        (some (⟨some .drain, initσ d, mkStk [] [] [] sx sy []⟩ : SCfg d)) =
      some ⟨none, initσ d, mkStk [] [] [] [] [] [false]⟩ := by
  induction sx generalizing sy with
  | nil =>
    induction sy with
    | nil =>
      simp only [List.length_nil, max_self, Nat.zero_add, Function.iterate_one, flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux]
      rw [upd_sx]
      simp only [mkStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.or_self, Bool.cond_false]
      rw [upd_sy, upd_out]; rfl
    | cons b ys ihy =>
      have hmax : max ([] : List Bool).length (b :: ys).length + 1 =
          (max ([] : List Bool).length ys.length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .drain, initσ d, mkStk [] [] [] [] (b :: ys) []⟩ : SCfg d)) =
          some ⟨some .drain, initσ d, mkStk [] [] [] [] ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.false_or, Bool.cond_true]
        rw [upd_sy]
      rw [e, ihy]
  | cons a xs ihx =>
    cases sy with
    | nil =>
      have hmax : max (a :: xs).length ([] : List Bool).length + 1 =
          (max xs.length ([] : List Bool).length + 1) + 1 := by simp
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .drain, initσ d, mkStk [] [] [] (a :: xs) [] []⟩ : SCfg d)) =
          some ⟨some .drain, initσ d, mkStk [] [] [] xs [] []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.true_or, Bool.cond_true]
        rw [upd_sy]
      rw [e, ihx []]
    | cons b ys =>
      have hmax : max (a :: xs).length (b :: ys).length + 1 =
          (max xs.length ys.length + 1) + 1 := by simp only [List.length_cons]; omega
      rw [hmax, Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .drain, initσ d, mkStk [] [] [] (a :: xs) (b :: ys) []⟩ : SCfg d)) =
          some ⟨some .drain, initσ d, mkStk [] [] [] xs ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.or_self, Bool.cond_true]
        rw [upd_sy]
      rw [e, ihx ys]

def cmpSteps : List Bool → List Bool → ℕ
  | [], [] => 1
  | a :: xs, [] => (a :: xs).length + 1
  | [], b :: ys => (b :: ys).length + 1
  | _ :: xs, _ :: ys => cmpSteps xs ys + 1

theorem cmpSteps_le (x y : List Bool) : cmpSteps x y ≤ x.length + y.length + 1 := by
  induction x generalizing y with
  | nil => cases y <;> simp [cmpSteps]
  | cons a xs ih =>
    cases y with
    | nil => simp [cmpSteps]
    | cons b ys =>
      simp only [cmpSteps, List.length_cons]
      have h := ih ys
      omega

theorem loop_doCmp (d : ℕ) (sx sy : List Bool) (m : Fin (d + 2)) :
    (flip bind (TM2.step (sProg d)))^[cmpSteps sx sy]
        (some (⟨some .doCmp, (m, none, none, none), mkStk [] [] [] sx sy []⟩ : SCfg d)) =
      some ⟨none, initσ d, mkStk [] [] [] [] [] [hamDec d sx sy m]⟩ := by
  induction sx generalizing sy m with
  | nil =>
    cases sy with
    | nil =>
      simp only [cmpSteps, Function.iterate_one, hamDec, flip_bind_some]
      simp only [TM2.step, sProg, TM2.stepAux]
      rw [upd_sx]
      simp only [mkStk, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.and_self,
        Bool.or_self, Bool.cond_false]
      rw [upd_sy, upd_out]; rfl
    | cons b ys =>
      simp only [cmpSteps, List.length_cons, hamDec]
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .doCmp, (m, none, none, none), mkStk [] [] [] [] (b :: ys) []⟩ : SCfg d)) =
          some ⟨some .drain, initσ d, mkStk [] [] [] [] ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.false_and, Bool.false_or,
          Bool.cond_false, Bool.cond_true]
        rw [upd_sy]
      rw [e]
      have hd := loop_drain d [] ys
      simpa using hd
  | cons a xs ihx =>
    cases sy with
    | nil =>
      simp only [cmpSteps, List.length_cons, hamDec]
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .doCmp, (m, none, none, none), mkStk [] [] [] (a :: xs) [] []⟩ : SCfg d)) =
          some ⟨some .drain, initσ d, mkStk [] [] [] xs [] []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
          Option.isSome_some, Option.isSome_none, Bool.and_false, Bool.true_or,
          Bool.cond_false, Bool.cond_true]
        rw [upd_sy]
      rw [e]
      have hd := loop_drain d xs []
      simpa using hd
    | cons b ys =>
      simp only [cmpSteps, hamDec]
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step (sProg d))
          (some (⟨some .doCmp, (m, none, none, none), mkStk [] [] [] (a :: xs) (b :: ys) []⟩ : SCfg d)) =
          some ⟨some .doCmp, (bumpMis d m (a != b), none, none, none), mkStk [] [] [] xs ys []⟩ := by
        rw [flip_bind_some]
        simp only [TM2.step, sProg, TM2.stepAux]
        rw [upd_sx]
        simp only [mkStk, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.and_self,
          Bool.cond_true, Option.getD_some]
        rw [upd_sy]
      rw [e, ihx ys (bumpMis d m (a != b))]

theorem sTM_run (d : ℕ) (x y : List Bool) :
    (flip bind (TM2.step (sProg d)))^[
        cmpSteps x y +
        (y.length + 1) +
        (x.length + 1) +
        (y.length + 1) +
        x.length]
        (some (initList (sTM d) (PvsNP.encodePair (x, y)))) =
      some (haltList (sTM d) [hamDec d x y (zeroFin d)]) := by
  have henc : PvsNP.encodePair (x, y) = x.map Sum.inl ++ y.map Sum.inr := by
    simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
  refine (congrArg (fun c => (flip bind (TM2.step (sProg d)))^[
      cmpSteps x y + (y.length + 1) + (x.length + 1) + (y.length + 1) + x.length]
      (some c)) (initList_sTM d (PvsNP.encodePair (x, y)))).trans
    (Eq.trans ?_ (congrArg some (haltList_sTM d [hamDec d x y (zeroFin d)])).symm)
  rw [henc]
  rw [Function.iterate_add_apply, loop_split_inl d x (y.map Sum.inr) [] []]
  rw [List.append_nil]
  rw [Function.iterate_add_apply, loop_split_inr d y x.reverse []]
  rw [List.append_nil]
  have hrevX := loop_revX d x.reverse y.reverse []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevX
  rw [Function.iterate_add_apply, hrevX]
  have hrevY := loop_revY d y.reverse x []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hrevY
  rw [Function.iterate_add_apply, hrevY]
  exact loop_doCmp d x y (zeroFin d)

theorem hamming_polytime (d : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => hamDec d p.1 p.2 (zeroFin d)) :=
  ⟨{
    tm := sTM d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 3 * Polynomial.X + Polynomial.C 4
    outputsFun := fun p =>
      { steps :=
          cmpSteps p.1 p.2 +
          (p.2.length + 1) +
          (p.1.length + 1) +
          (p.2.length + 1) +
          p.1.length
        evals_in_steps := by
          have hm1 : List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair p) =
              PvsNP.encodePair p := by simp
          have hm2 : List.map (Equiv.refl Bool).invFun
              (PvsNP.encodeAnswer (hamDec d p.1 p.2 (zeroFin d))) =
              [hamDec d p.1 p.2 (zeroFin d)] := rfl
          exact (congrArg (fun i => (flip bind (TM2.step (sProg d)))^[
              cmpSteps p.1 p.2 + (p.2.length + 1) + (p.1.length + 1) + (p.2.length + 1) + p.1.length]
              (some (initList (sTM d) i))) hm1).trans
            ((sTM_run d p.1 p.2).trans
              (congrArg (fun o => some (haltList (sTM d) o)) hm2.symm))
        steps_le_m := by
          have hlen : (PvsNP.encodePair p).length = p.1.length + p.2.length := by
            simp [PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]
          have hs := cmpSteps_le p.1 p.2
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, hlen]
          omega } }⟩

end PvsNP.Units.tr_rel_hamming_le_all

theorem PvsNP.Units.tr_rel_hamming_le_all :
    ∀ d : ℕ, ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧ (List.zipWith (fun a b => a != b) p.1 p.2).count true ≤ d) ↔
          f p = true := by
  intro d
  refine ⟨fun p => PvsNP.Units.tr_rel_hamming_le_all.hamDec d p.1 p.2
      (PvsNP.Units.tr_rel_hamming_le_all.zeroFin d),
    PvsNP.Units.tr_rel_hamming_le_all.hamming_polytime d,
    fun p => ?_⟩
  have h := PvsNP.Units.tr_rel_hamming_le_all.hamDec_iff d p.1 p.2
    (PvsNP.Units.tr_rel_hamming_le_all.zeroFin d)
  simpa [PvsNP.Units.tr_rel_hamming_le_all.zeroFin] using h
