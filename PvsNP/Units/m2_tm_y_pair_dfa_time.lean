import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_pair_dfa_time

open Turing

private inductive DK : Type
  | inp | out
  deriving DecidableEq

private instance : Fintype DK :=
  Fintype.ofEquiv Bool
    { toFun := fun b => if b then .out else .inp
      invFun := fun k => match k with | .inp => false | .out => true
      left_inv := fun b => by cases b <;> rfl
      right_inv := fun k => by cases k <;> rfl }

private abbrev DΓ : DK → Type
  | .inp => Bool ⊕ Bool
  | .out => Bool

private def dfaTM (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool) :
    FinTM2 where
  K := DK
  k₀ := .inp
  k₁ := .out
  Γ := DΓ
  Λ := Unit
  main := ()
  σ := Q × Bool
  initialState := (q₀, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := fun _ =>
    TM2.Stmt.pop .inp (fun s o => match o with
      | none => (s.1, false)
      | some a => (δ s.1 a, true))
      (TM2.Stmt.branch Prod.snd
        (TM2.Stmt.goto fun _ => ())
        (TM2.Stmt.push .out (fun s => F s.1)
          (TM2.Stmt.load (fun _ => (q₀, false)) TM2.Stmt.halt)))

private def mkStacks (inp : List (Bool ⊕ Bool)) (out : List Bool) : (k : DK) → List (DΓ k)
  | .inp => inp
  | .out => out

private def cfgAt (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (q : Q) (b : Bool) (l : List (Bool ⊕ Bool)) : (dfaTM Q δ q₀ F).Cfg :=
  ⟨some (), (q, b), mkStacks l []⟩

private def cfgDone (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (ans : Bool) : (dfaTM Q δ q₀ F).Cfg :=
  ⟨none, (q₀, false), mkStacks [] [ans]⟩

private theorem step_cons (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (q : Q) (b : Bool) (a : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) :
    (dfaTM Q δ q₀ F).step (cfgAt Q δ q₀ F q b (a :: l)) =
      some (cfgAt Q δ q₀ F (δ q a) true l) := by
  simp only [FinTM2.step, cfgAt, dfaTM, TM2.step, TM2.stepAux, mkStacks, List.head?_cons,
    List.tail_cons, Bool.cond_true]
  congr 1
  congr 1
  funext k
  cases k <;> rfl

private theorem step_nil (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (q : Q) (b : Bool) :
    (dfaTM Q δ q₀ F).step (cfgAt Q δ q₀ F q b []) =
      some (cfgDone Q δ q₀ F (F q)) := by
  simp only [FinTM2.step, cfgAt, cfgDone, dfaTM, TM2.step, TM2.stepAux, mkStacks, List.head?_nil,
    List.tail_nil, Bool.cond_false]
  congr 1
  congr 1
  funext k
  cases k <;> rfl

private theorem iter (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool) :
    ∀ (l : List (Bool ⊕ Bool)) (q : Q) (b : Bool),
      (flip bind (dfaTM Q δ q₀ F).step)^[l.length + 1] (some (cfgAt Q δ q₀ F q b l)) =
        some (cfgDone Q δ q₀ F (F (l.foldl δ q)))
  | [], q, b => by
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.foldl_nil]
    exact step_nil Q δ q₀ F q b
  | a :: l, q, b => by
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind (dfaTM Q δ q₀ F).step)^[l.length + 1]
        ((dfaTM Q δ q₀ F).step (cfgAt Q δ q₀ F q b (a :: l))) = _
    rw [step_cons]
    simpa [List.foldl_cons] using iter Q δ q₀ F l (δ q a) true

private theorem initList_eq (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (l : List (Bool ⊕ Bool)) :
    initList (dfaTM Q δ q₀ F) l = cfgAt Q δ q₀ F q₀ false l := by
  simp only [initList, cfgAt, dfaTM]
  congr 1
  funext k
  cases k <;> rfl

private theorem haltList_eq (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool)
    (ans : Bool) :
    haltList (dfaTM Q δ q₀ F) [ans] = cfgDone Q δ q₀ F ans := by
  simp only [haltList, cfgDone, dfaTM]
  congr 1
  funext k
  cases k <;> rfl

private noncomputable def dfaTime (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool) :
    TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => F ((PvsNP.encodePair p).foldl δ q₀)) where
  tm := dfaTM Q δ q₀ F
  inputAlphabet := Equiv.refl (Bool ⊕ Bool)
  outputAlphabet := Equiv.refl Bool
  time := fun n => n + 1
  outputsFun p :=
    { steps := (PvsNP.encodePair p).length + 1
      evals_in_steps := by
        have h := iter Q δ q₀ F (PvsNP.encodePair p) q₀ false
        rw [← initList_eq, ← haltList_eq] at h
        have h1 : List.map (Equiv.refl (Bool ⊕ Bool)) (PvsNP.encodePair p) = PvsNP.encodePair p :=
          List.map_id (PvsNP.encodePair p)
        exact Eq.trans
          (congrArg (fun l => (flip bind (dfaTM Q δ q₀ F).step)^[(PvsNP.encodePair p).length + 1]
            (some (initList (dfaTM Q δ q₀ F) l))) h1)
          h
      steps_le_m := le_refl _ }

theorem main :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool),
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer
          (fun p : List Bool × List Bool => F ((PvsNP.encodePair p).foldl δ q₀)),
        ∀ n : ℕ, M.time n ≤ 2 * n + 3 := by
  intro Q _ δ q₀ F
  refine ⟨dfaTime Q δ q₀ F, fun n => ?_⟩
  change n + 1 ≤ 2 * n + 3
  omega

end PvsNP.Units.m2_tm_y_pair_dfa_time

theorem PvsNP.Units.m2_tm_y_pair_dfa_time :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool),
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer
          (fun p : List Bool × List Bool => F ((PvsNP.encodePair p).foldl δ q₀)),
        ∀ n : ℕ, M.time n ≤ 2 * n + 3 :=
  PvsNP.Units.m2_tm_y_pair_dfa_time.main
