import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_subsequence_test

open Turing

inductive SK : Type
  | inp | tmp | u | v | out
  deriving DecidableEq

instance : Fintype SK :=
  Fintype.ofList [.inp, .tmp, .u, .v, .out] (fun x => by cases x <;> simp)

abbrev SΓ : SK → Type
  | .inp => Bool ⊕ Bool
  | .tmp => Bool ⊕ Bool
  | .u => Bool
  | .v => Bool
  | .out => Bool

inductive SL : Type
  | rev | split | nextU | find (a : Bool) | cleanV | cleanU
  deriving DecidableEq

instance : Fintype SL :=
  Fintype.ofList [.rev, .split, .nextU, .find false, .find true, .cleanV, .cleanU]
    (fun x => by cases x with | find a => cases a <;> simp | _ => simp)

abbrev Sσ : Type := Option (Bool ⊕ Bool)

def getSym : Sσ → Bool ⊕ Bool
  | some s => s
  | none => Sum.inl false

def getBit : Sσ → Bool
  | some (Sum.inl a) => a
  | some (Sum.inr b) => b
  | none => false

def subProg : SL → TM2.Stmt SΓ SL Sσ
  | .rev =>
    .pop .inp (fun _ o => o)
      (.branch Option.isSome
        (.push .tmp getSym (.goto fun _ => .rev))
        (.load (fun _ => none) (.goto fun _ => .split)))
  | .split =>
    .pop .tmp (fun _ o => o)
      (.branch Option.isSome
        (.branch (fun s => (getSym s).isLeft)
          (.push .u getBit (.goto fun _ => .split))
          (.push .v getBit (.goto fun _ => .split)))
        (.load (fun _ => none) (.goto fun _ => .nextU)))
  | .nextU =>
    .pop .u (fun _ o => o.map Sum.inl)
      (.branch Option.isSome
        (.branch getBit (.goto fun _ => .find true) (.goto fun _ => .find false))
        (.goto fun _ => .cleanV))
  | .find a =>
    .pop .v (fun _ o => o.map Sum.inr)
      (.branch Option.isSome
        (.branch (fun s => getBit s == a)
          (.goto fun _ => .nextU)
          (.goto fun _ => .find a))
        (.goto fun _ => .cleanU))
  | .cleanV =>
    .pop .v (fun _ o => o.map Sum.inr)
      (.branch Option.isSome
        (.goto fun _ => .cleanV)
        (.push .out (fun _ => true) (.load (fun _ => none) .halt)))
  | .cleanU =>
    .pop .u (fun _ o => o.map Sum.inl)
      (.branch Option.isSome
        (.goto fun _ => .cleanU)
        (.push .out (fun _ => false) (.load (fun _ => none) .halt)))

abbrev subTM : FinTM2 where
  K := SK
  k₀ := .inp
  k₁ := .out
  Γ := SΓ
  Λ := SL
  main := .rev
  σ := Sσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := subProg

def sstk (i t : List (Bool ⊕ Bool)) (u v o : List Bool) : ∀ k, List (SΓ k)
  | .inp => i
  | .tmp => t
  | .u => u
  | .v => v
  | .out => o

@[simp] lemma sstk_inp (i i' t : List (Bool ⊕ Bool)) (u v o : List Bool) :
    Function.update (sstk i t u v o) .inp i' = sstk i' t u v o := by
  funext k; cases k <;> simp [sstk]

@[simp] lemma sstk_tmp (i t t' : List (Bool ⊕ Bool)) (u v o : List Bool) :
    Function.update (sstk i t u v o) .tmp t' = sstk i t' u v o := by
  funext k; cases k <;> simp [sstk]

@[simp] lemma sstk_u (i t : List (Bool ⊕ Bool)) (u u' v o : List Bool) :
    Function.update (sstk i t u v o) .u u' = sstk i t u' v o := by
  funext k; cases k <;> simp [sstk]

@[simp] lemma sstk_v (i t : List (Bool ⊕ Bool)) (u v v' o : List Bool) :
    Function.update (sstk i t u v o) .v v' = sstk i t u v' o := by
  funext k; cases k <;> simp [sstk]

@[simp] lemma sstk_out (i t : List (Bool ⊕ Bool)) (u v o o' : List Bool) :
    Function.update (sstk i t u v o) .out o' = sstk i t u v o' := by
  funext k; cases k <;> simp [sstk]

abbrev SCfg : Type := TM2.Cfg SΓ SL Sσ
abbrev sStep : Option SCfg → Option SCfg := flip bind (TM2.step subProg)

lemma rev_loop :
    ∀ (i t : List (Bool ⊕ Bool)) (s : Sσ),
      sStep^[i.length + 1] (some ⟨some .rev, s, sstk i t [] [] []⟩) =
        some ⟨some .split, none, sstk [] (i.reverse ++ t) [] [] []⟩
  | [], t, s => by
    simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
  | x :: xs, t, s => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .rev, s, sstk (x :: xs) t [] [] []⟩) =
        some ⟨some .rev, some x, sstk xs (x :: t) [] [] []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getSym]
    rw [h1, rev_loop xs (x :: t) (some x)]
    simp [List.reverse_cons, List.append_assoc]

lemma split_inr :
    ∀ (r : List Bool) (t : List (Bool ⊕ Bool)) (u v : List Bool) (s : Sσ),
      sStep^[r.length] (some ⟨some .split, s, sstk [] (r.map Sum.inr ++ t) u v []⟩) =
        some ⟨some .split, if r = [] then s else some (Sum.inr r.getLast!), sstk [] t u (r.reverse ++ v) []⟩
  | [], t, u, v, s => by simp
  | b :: rs, t, u, v, s => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .split, s, sstk [] (Sum.inr b :: (rs.map Sum.inr ++ t)) u v []⟩) =
        some ⟨some .split, some (Sum.inr b), sstk [] (rs.map Sum.inr ++ t) u (b :: v) []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getSym, getBit]
    change sStep^[rs.length] (sStep (some ⟨some .split, s, sstk [] (Sum.inr b :: (rs.map Sum.inr ++ t)) u v []⟩)) = _
    rw [h1, split_inr rs t u (b :: v) (some (Sum.inr b))]
    cases rs with
    | nil => simp
    | cons b' rs' => simp [List.reverse_cons, List.append_assoc]

lemma split_inl :
    ∀ (l : List Bool) (u v : List Bool) (s : Sσ),
      sStep^[l.length + 1] (some ⟨some .split, s, sstk [] (l.map Sum.inl) u v []⟩) =
        some ⟨some .nextU, none, sstk [] [] (l.reverse ++ u) v []⟩
  | [], u, v, s => by
    simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
  | a :: ls, u, v, s => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .split, s, sstk [] (Sum.inl a :: ls.map Sum.inl) u v []⟩) =
        some ⟨some .split, some (Sum.inl a), sstk [] (ls.map Sum.inl) (a :: u) v []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getSym, getBit]
    change sStep^[ls.length + 1] (sStep (some ⟨some .split, s, sstk [] (Sum.inl a :: ls.map Sum.inl) u v []⟩)) = _
    rw [h1, split_inl ls (a :: u) v (some (Sum.inl a))]
    simp [List.reverse_cons, List.append_assoc]

lemma cleanV_loop :
    ∀ (v : List Bool) (s : Sσ),
      sStep^[v.length + 1] (some ⟨some .cleanV, s, sstk [] [] [] v []⟩) =
        some ⟨none, none, sstk [] [] [] [] [true]⟩
  | [], s => by
    simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
  | b :: vs, s => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .cleanV, s, sstk [] [] [] (b :: vs) []⟩) =
        some ⟨some .cleanV, some (Sum.inr b), sstk [] [] [] vs []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
    rw [h1, cleanV_loop vs (some (Sum.inr b))]

lemma cleanU_loop :
    ∀ (u : List Bool) (s : Sσ),
      sStep^[u.length + 1] (some ⟨some .cleanU, s, sstk [] [] u [] []⟩) =
        some ⟨none, none, sstk [] [] [] [] [false]⟩
  | [], s => by
    simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
  | a :: us, s => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .cleanU, s, sstk [] [] (a :: us) [] []⟩) =
        some ⟨some .cleanU, some (Sum.inl a), sstk [] [] us [] []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
    rw [h1, cleanU_loop us (some (Sum.inl a))]

lemma sublist_cons_iff (a b : Bool) (us vs : List Bool) :
    List.Sublist (a :: us) (b :: vs) ↔ (if b = a then List.Sublist us vs else List.Sublist (a :: us) vs) := by
  by_cases hba : b = a
  · subst hba
    simp only [↓reduceIte]
    constructor
    · intro h
      cases h with
      | cons _ h' => exact (List.sublist_cons_self b us).trans h'
      | cons_cons _ h' => exact h'
    · exact List.Sublist.cons_cons b
  · simp only [hba, ↓reduceIte]
    constructor
    · intro h
      cases h with
      | cons _ h' => exact h'
      | cons_cons _ _ => exact absurd rfl hba
    · exact List.Sublist.cons b

theorem nextU_run :
    ∀ (u v : List Bool) (s : Sσ),
      sStep^[u.length + v.length + 2] (some ⟨some .nextU, s, sstk [] [] u v []⟩) =
        some ⟨none, none, sstk [] [] [] [] [decide (List.Sublist u v)]⟩ := by
  intro u
  induction u with
  | nil =>
    intro v s
    simp only [List.length_nil, Nat.zero_add, List.nil_sublist, decide_true]
    rw [show v.length + 2 = (v.length + 1) + 1 by omega, Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .nextU, s, sstk [] [] [] v []⟩) =
        some ⟨some .cleanV, none, sstk [] [] [] v []⟩ := by
      simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
    rw [h1, cleanV_loop v none]
  | cons a us ih =>
    have hfind : ∀ (v : List Bool) (s : Sσ),
        sStep^[us.length + v.length + 2] (some ⟨some (.find a), s, sstk [] [] us v []⟩) =
          some ⟨none, none, sstk [] [] [] [] [decide (List.Sublist (a :: us) v)]⟩ := by
      intro v
      induction v with
      | nil =>
        intro s
        have hsub : ¬ List.Sublist (a :: us) [] := by simp
        simp only [List.length_nil, Nat.add_zero, hsub, decide_false]
        rw [show us.length + 2 = (us.length + 1) + 1 by omega, Function.iterate_succ_apply]
        have h1 : sStep (some ⟨some (.find a), s, sstk [] [] us [] []⟩) =
            some ⟨some .cleanU, none, sstk [] [] us [] []⟩ := by
          simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk]
        rw [h1, cleanU_loop us none]
      | cons b vs ihv =>
        intro s
        rw [List.length_cons, show us.length + (vs.length + 1) + 2 = (us.length + vs.length + 2) + 1 by omega,
          Function.iterate_succ_apply]
        by_cases hba : b = a
        · subst hba
          have h1 : sStep (some ⟨some (.find b), s, sstk [] [] us (b :: vs) []⟩) =
              some ⟨some .nextU, some (Sum.inr b), sstk [] [] us vs []⟩ := by
            simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getBit]
          rw [h1, ih vs (some (Sum.inr b))]
          have hiff := sublist_cons_iff b b us vs
          simp only [↓reduceIte] at hiff
          rw [decide_eq_decide.mpr hiff.symm]
        · have hbeq : (b == a) = false := beq_false_of_ne hba
          have h1 : sStep (some ⟨some (.find a), s, sstk [] [] us (b :: vs) []⟩) =
              some ⟨some (.find a), some (Sum.inr b), sstk [] [] us vs []⟩ := by
            simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getBit, hbeq]
          rw [h1, ihv (some (Sum.inr b))]
          have hiff := sublist_cons_iff a b us vs
          simp only [hba, ↓reduceIte] at hiff
          rw [decide_eq_decide.mpr hiff.symm]
    intro v s
    rw [List.length_cons, show us.length + 1 + v.length + 2 = (us.length + v.length + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have h1 : sStep (some ⟨some .nextU, s, sstk [] [] (a :: us) v []⟩) =
        some ⟨some (.find a), some (Sum.inl a), sstk [] [] us v []⟩ := by
      cases a <;> simp [sStep, flip, TM2.step, subProg, TM2.stepAux, sstk, getBit]
    rw [h1, hfind v (some (Sum.inl a))]

lemma init_eq (l : List (Bool ⊕ Bool)) :
    (initList subTM l : SCfg) = ⟨some .rev, none, sstk l [] [] [] []⟩ := by
  unfold initList subTM
  congr 1
  funext k
  cases k <;> simp [sstk]

lemma halt_eq (o : List Bool) :
    (haltList subTM o : SCfg) = ⟨none, none, sstk [] [] [] [] o⟩ := by
  unfold haltList subTM
  congr 1
  funext k
  cases k <;> simp [sstk]

lemma full_run (u v : List Bool) :
    sStep^[(((u.length + v.length + 2) + (u.length + 1)) + v.length) + ((u.length + v.length) + 1)]
      (some (initList subTM (u.map Sum.inl ++ v.map Sum.inr) : SCfg)) =
      some (haltList subTM [decide (List.Sublist u v)] : SCfg) := by
  rw [init_eq, halt_eq,
    Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
  have hrev := rev_loop (u.map Sum.inl ++ v.map Sum.inr) [] none
  have hlen : (u.map Sum.inl ++ v.map Sum.inr).length = u.length + v.length := by simp
  rw [hlen, List.append_nil] at hrev
  rw [hrev]
  have hr : (u.map Sum.inl ++ v.map Sum.inr).reverse =
      v.reverse.map Sum.inr ++ u.reverse.map Sum.inl := by
    simp [List.reverse_append, List.map_reverse]
  rw [hr]
  have hsp1 := split_inr v.reverse (u.reverse.map Sum.inl) [] [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hsp1
  rw [hsp1]
  have hsp2 := split_inl u.reverse [] v (if v.reverse = [] then none else some (Sum.inr v.reverse.getLast!))
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hsp2
  rw [hsp2]
  exact nextU_run u v none

noncomputable def subseqPoly :
    TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) where
  tm := subTM
  inputAlphabet := Equiv.refl (Bool ⊕ Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 4
  outputsFun p := by
    rcases p with ⟨u, v⟩
    have henc : PvsNP.encodePair (u, v) = u.map Sum.inl ++ v.map Sum.inr := rfl
    have hm1 : List.map (Equiv.refl (Bool ⊕ Bool)).invFun (PvsNP.encodePair (u, v)) =
        u.map Sum.inl ++ v.map Sum.inr := List.map_id _
    have hm2 : List.map (Equiv.refl Bool).invFun [decide (List.Sublist u v)] =
        [decide (List.Sublist u v)] := List.map_id _
    let tot := (((u.length + v.length + 2) + (u.length + 1)) + v.length) + ((u.length + v.length) + 1)
    refine ⟨⟨tot, ?_⟩, ?_⟩
    · refine (congrArg (fun l => (flip bind subTM.step)^[tot] (some (initList subTM l))) hm1).trans ?_
      refine Eq.trans ?_ (congrArg (fun l => some (haltList subTM l)) hm2.symm)
      exact full_run u v
    · have hplen : (PvsNP.encodePair (u, v)).length = u.length + v.length := by
        rw [henc]
        simp
      simp only [tot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hplen]
      omega

end PvsNP.Units.m2_tm_y_subsequence_test

theorem PvsNP.Units.m2_tm_y_subsequence_test :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) :=
  ⟨PvsNP.Units.m2_tm_y_subsequence_test.subseqPoly⟩
