import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_inversions_unary

open Turing

inductive IK : Type
  | inp | ones | tmp | out
  deriving DecidableEq

instance : Fintype IK :=
  Fintype.ofList [.inp, .ones, .tmp, .out] (fun x => by cases x <;> simp)

abbrev IΓ : IK → Type := fun _ => Bool

inductive IL : Type
  | outer | copy1 | copy2 | clean
  deriving DecidableEq

instance : Fintype IL :=
  Fintype.ofList [.outer, .copy1, .copy2, .clean] (fun x => by cases x <;> simp)

abbrev Iσ : Type := Option Bool

def invProg : IL → TM2.Stmt IΓ IL Iσ
  | .outer =>
    .pop .inp (fun _ o => o)
      (.branch Option.isSome
        (.branch (fun s => s == some true)
          (.push .ones (fun _ => true) (.goto fun _ => .outer))
          (.goto fun _ => .copy1))
        (.goto fun _ => .clean))
  | .copy1 =>
    .pop .ones (fun _ o => o)
      (.branch Option.isSome
        (.push .tmp (fun _ => true) (.push .out (fun _ => true) (.goto fun _ => .copy1)))
        (.goto fun _ => .copy2))
  | .copy2 =>
    .pop .tmp (fun _ o => o)
      (.branch Option.isSome
        (.push .ones (fun _ => true) (.goto fun _ => .copy2))
        (.goto fun _ => .outer))
  | .clean =>
    .pop .ones (fun _ o => o)
      (.branch Option.isSome
        (.goto fun _ => .clean)
        (.load (fun _ => none) .halt))

abbrev invTM : FinTM2 where
  K := IK
  k₀ := .inp
  k₁ := .out
  Γ := IΓ
  Λ := IL
  main := .outer
  σ := Iσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := invProg

def istk (i c t o : List Bool) : ∀ k, List (IΓ k)
  | .inp => i
  | .ones => c
  | .tmp => t
  | .out => o

@[simp] lemma istk_inp (i i' c t o : List Bool) :
    Function.update (istk i c t o) .inp i' = istk i' c t o := by
  funext k; cases k <;> simp [istk]

@[simp] lemma istk_ones (i c c' t o : List Bool) :
    Function.update (istk i c t o) .ones c' = istk i c' t o := by
  funext k; cases k <;> simp [istk]

@[simp] lemma istk_tmp (i c t t' o : List Bool) :
    Function.update (istk i c t o) .tmp t' = istk i c t' o := by
  funext k; cases k <;> simp [istk]

@[simp] lemma istk_out (i c t o o' : List Bool) :
    Function.update (istk i c t o) .out o' = istk i c t o' := by
  funext k; cases k <;> simp [istk]

abbrev ICfg : Type := TM2.Cfg IΓ IL Iσ
abbrev iStep : Option ICfg → Option ICfg := flip bind (TM2.step invProg)
abbrev rep (n : ℕ) : List Bool := List.replicate n true

lemma rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

lemma copy1_loop (xs : List Bool) :
    ∀ (k t m : ℕ) (s : Iσ),
      iStep^[k + 1] (some ⟨some .copy1, s, istk xs (rep k) (rep t) (rep m)⟩) =
        some ⟨some .copy2, none, istk xs [] (rep (k + t)) (rep (k + m))⟩
  | 0, t, m, s => by
    simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk, rep]
  | k + 1, t, m, s => by
    rw [Function.iterate_succ_apply, ← rep_succ k]
    have h1 : iStep (some ⟨some .copy1, s, istk xs (true :: rep k) (rep t) (rep m)⟩) =
        some ⟨some .copy1, some true, istk xs (rep k) (rep (t + 1)) (rep (m + 1))⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk]
      rfl
    rw [h1, copy1_loop xs k (t + 1) (m + 1) (some true)]
    rw [show k + (t + 1) = k + 1 + t by omega, show k + (m + 1) = k + 1 + m by omega]

lemma copy2_loop (xs : List Bool) (m : ℕ) :
    ∀ (k c : ℕ) (s : Iσ),
      iStep^[k + 1] (some ⟨some .copy2, s, istk xs (rep c) (rep k) (rep m)⟩) =
        some ⟨some .outer, none, istk xs (rep (k + c)) [] (rep m)⟩
  | 0, c, s => by
    simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk, rep]
  | k + 1, c, s => by
    rw [Function.iterate_succ_apply, ← rep_succ k]
    have h1 : iStep (some ⟨some .copy2, s, istk xs (rep c) (true :: rep k) (rep m)⟩) =
        some ⟨some .copy2, some true, istk xs (rep (c + 1)) (rep k) (rep m)⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk]
      rfl
    rw [h1, copy2_loop xs m k (c + 1) (some true)]
    rw [show k + (c + 1) = k + 1 + c by omega]

lemma clean_loop (m : ℕ) :
    ∀ (k : ℕ) (s : Iσ),
      iStep^[k + 1] (some ⟨some .clean, s, istk [] (rep k) [] (rep m)⟩) =
        some ⟨none, none, istk [] [] [] (rep m)⟩
  | 0, s => by
    simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk, rep]
  | k + 1, s => by
    rw [Function.iterate_succ_apply, ← rep_succ k]
    have h1 : iStep (some ⟨some .clean, s, istk [] (true :: rep k) [] (rep m)⟩) =
        some ⟨some .clean, some true, istk [] (rep k) [] (rep m)⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk]
    rw [h1, clean_loop m k (some true)]

def invAcc (k m : ℕ) : List Bool → ℕ
  | [] => m
  | true :: xs => invAcc (k + 1) m xs
  | false :: xs => invAcc k (k + m) xs

def invSteps (k : ℕ) : List Bool → ℕ
  | [] => (k + 1) + 1
  | true :: xs => invSteps (k + 1) xs + 1
  | false :: xs => invSteps k xs + (k + 1) + (k + 1) + 1

lemma outer_run :
    ∀ (xs : List Bool) (k m : ℕ) (s : Iσ),
      iStep^[invSteps k xs] (some ⟨some .outer, s, istk xs (rep k) [] (rep m)⟩) =
        some ⟨none, none, istk [] [] [] (rep (invAcc k m xs))⟩
  | [], k, m, s => by
    simp only [invSteps, invAcc]
    rw [Function.iterate_succ_apply]
    have h1 : iStep (some ⟨some .outer, s, istk [] (rep k) [] (rep m)⟩) =
        some ⟨some .clean, none, istk [] (rep k) [] (rep m)⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk]
    rw [h1, clean_loop m k none]
  | true :: xs, k, m, s => by
    simp only [invSteps, invAcc]
    rw [Function.iterate_succ_apply]
    have h1 : iStep (some ⟨some .outer, s, istk (true :: xs) (rep k) [] (rep m)⟩) =
        some ⟨some .outer, some true, istk xs (rep (k + 1)) [] (rep m)⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk]
      rfl
    rw [h1, outer_run xs (k + 1) m (some true)]
  | false :: xs, k, m, s => by
    simp only [invSteps, invAcc]
    rw [Function.iterate_succ_apply, Function.iterate_add_apply, Function.iterate_add_apply]
    have h1 : iStep (some ⟨some .outer, s, istk (false :: xs) (rep k) [] (rep m)⟩) =
        some ⟨some .copy1, some false, istk xs (rep k) (rep 0) (rep m)⟩ := by
      simp [iStep, flip, TM2.step, invProg, TM2.stepAux, istk, rep]
    rw [h1, copy1_loop xs k 0 m (some false)]
    have hc2 := copy2_loop xs (k + m) k 0 none
    simp only [Nat.add_zero, rep, List.replicate_zero] at hc2 ⊢
    rw [hc2, outer_run xs k (k + m) none]

lemma invSteps_bound :
    ∀ (xs : List Bool) (k : ℕ),
      invSteps k xs ≤ (xs.length + 1) * (2 * (k + xs.length) + 3)
  | [], k => by
    simp [invSteps]
    omega
  | true :: xs, k => by
    have ih := invSteps_bound xs (k + 1)
    simp only [invSteps, List.length_cons]
    have hle : 2 * (k + 1 + xs.length) + 3 = 2 * (k + (xs.length + 1)) + 3 := by omega
    rw [hle] at ih
    nlinarith
  | false :: xs, k => by
    have ih := invSteps_bound xs k
    simp only [invSteps, List.length_cons]
    nlinarith

def invSum (x : List Bool) : ℕ :=
  ((List.range x.length).map (fun j => if x.getD j false = true then 0 else (x.take j).count true)).sum

lemma count_false_eq_sum :
    ∀ (xs : List Bool),
      ((List.range xs.length).map (fun i => if xs.getD i false = true then 0 else 1)).sum =
        xs.count false
  | [] => rfl
  | b :: xs => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    have hstep : ((fun i => if (b :: xs).getD i false = true then 0 else 1) ∘ (· + 1)) =
        (fun i => if xs.getD i false = true then 0 else 1) := by
      funext i; rfl
    rw [hstep, count_false_eq_sum xs]
    cases b
    · simp only [List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte, List.count_cons_self]
      omega
    · simp only [List.getD_cons_zero, ↓reduceIte, Nat.zero_add]
      simp

lemma sum_add_map {α : Type} (f g : α → ℕ) :
    ∀ l : List α, (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_add_map f g l]
    omega

lemma invSum_true (xs : List Bool) :
    invSum (true :: xs) = xs.count false + invSum xs := by
  unfold invSum
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
  have h0 : (if (true :: xs).getD 0 false = true then 0 else ((true :: xs).take 0).count true) = 0 := rfl
  have hstep : ((fun j => if (true :: xs).getD j false = true then 0 else ((true :: xs).take j).count true) ∘ (· + 1)) =
      (fun i => (if xs.getD i false = true then 0 else 1) +
        (if xs.getD i false = true then 0 else (xs.take i).count true)) := by
    funext i
    simp only [Function.comp_apply, List.getD_cons_succ, List.take_succ_cons, List.count_cons_self]
    cases xs.getD i false
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp
  rw [h0, Nat.zero_add, hstep, sum_add_map, count_false_eq_sum]

lemma invSum_false (xs : List Bool) :
    invSum (false :: xs) = invSum xs := by
  unfold invSum
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
  have h0 : (if (false :: xs).getD 0 false = true then 0 else ((false :: xs).take 0).count true) = 0 := rfl
  have hstep : ((fun j => if (false :: xs).getD j false = true then 0 else ((false :: xs).take j).count true) ∘ (· + 1)) =
      (fun i => if xs.getD i false = true then 0 else (xs.take i).count true) := by
    funext i
    simp [Function.comp_apply]
  rw [h0, Nat.zero_add, hstep]

lemma invAcc_eq :
    ∀ (xs : List Bool) (k m : ℕ),
      invAcc k m xs = m + k * xs.count false + invSum xs
  | [], k, m => by simp [invAcc, invSum]
  | true :: xs, k, m => by
    simp only [invAcc, invAcc_eq xs (k + 1) m, invSum_true, List.count_cons, beq_iff_eq,
      Bool.true_eq_false, ↓reduceIte, Nat.add_zero]
    ring
  | false :: xs, k, m => by
    simp only [invAcc, invAcc_eq xs k (k + m), invSum_false, List.count_cons, beq_self_eq_true,
      ↓reduceIte]
    ring

lemma init_eq (x : List Bool) :
    (initList invTM x : ICfg) = ⟨some .outer, none, istk x [] [] []⟩ := by
  unfold initList invTM
  congr 1
  funext k
  cases k <;> simp [istk]

lemma halt_eq (o : List Bool) :
    (haltList invTM o : ICfg) = ⟨none, none, istk [] [] [] o⟩ := by
  unfold haltList invTM
  congr 1
  funext k
  cases k <;> simp [istk]

noncomputable def invPoly :
    TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (invSum x) true) where
  tm := invTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
  outputsFun x := by
    refine ⟨⟨invSteps 0 x, ?_⟩, ?_⟩
    · have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := List.map_id
      refine (congrArg (fun l => (flip bind invTM.step)^[invSteps 0 x] (some (initList invTM l))) (hm x)).trans ?_
      refine Eq.trans ?_ (congrArg (fun l => some (haltList invTM l)) (hm (rep (invSum x))).symm)
      show iStep^[invSteps 0 x] (some (initList invTM x : ICfg)) =
        some (haltList invTM (rep (invSum x)) : ICfg)
      rw [init_eq, halt_eq]
      have hrun := outer_run x 0 0 none
      have hacc := invAcc_eq x 0 0
      simp only [Nat.zero_add, Nat.zero_mul] at hacc
      rw [hacc] at hrun
      exact hrun
    · have hb := invSteps_bound x 0
      have hlen : (PvsNP.encodeString x).length = x.length := rfl
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.eval_X, hlen, Nat.zero_add] at hb ⊢
      nlinarith

end PvsNP.Units.m2_tm_y_inversions_unary

theorem PvsNP.Units.m2_tm_y_inversions_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        List.replicate ((List.range x.length).map (fun j => if x.getD j false = true then 0 else (x.take j).count true)).sum true) :=
  ⟨PvsNP.Units.m2_tm_y_inversions_unary.invPoly⟩
