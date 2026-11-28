import Mathlib
import PvsNP.Defs
import CookLevin

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs)
at commit 8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Defs/Base.lean,
  lean/PEqualNP/Defs/Classes.lean,
  lean/PEqualNP/Library/Machines/Run.lean,
  lean/PEqualNP/Library/Machines/Compose.lean,
  lean/PEqualNP/Library/Machines/ComposeRun.lean,
  lean/PEqualNP/Library/Machines/FilterMap.lean,
  lean/PEqualNP/Library/Machines/TwoPass.lean,
  lean/PEqualNP/Library/Machines/First.lean,
  lean/PEqualNP/Library/Machines/FirstRun.lean,
  lean/PEqualNP/Library/Machines/FirstPoly.lean,
  lean/PEqualNP/Library/Machines/Pairing.lean,
  lean/PEqualNP/Library/Machines/AllTrue.lean,
  lean/PEqualNP/Library/Machines/LenLE.lean,
  lean/PEqualNP/Library/Machines/FirstG.lean,
  lean/PEqualNP/Library/Machines/FirstGRun.lean,
  lean/PEqualNP/Library/Machines/Mul.lean,
  lean/PEqualNP/Library/Machines/Clock.lean,
  lean/PEqualNP/Library/Machines/ConstList.lean,
  lean/PEqualNP/Library/L055.lean,
  lean/PEqualNP/Library/Machines/NormalForm.lean,
  lean/PEqualNP/Library/L045.lean (NP verifiers in normal form: the witness length bound built
    into the relation) and
  lean/PEqualNP/Library/Machines/Transducer.lean (a machine running a finite-state transducer).
Copied into this unit's namespace from the settled campaign file
PvsNP/Units/m2_np_verifier_normal.lean (github.com/makedotfun/pvsnp): the sections
Defs/Base through Machines/Transducer, the bridge NP_iff, and the initial certificate
encoding/decoding lemmas of its intersection section. The source file in turn copies
these machine sections from PvsNP/Units/m2_np_down_closed.lean and
PvsNP/Units/fr_np_in_exp.lean, under the Apache License, Version 2.0.
The copied bodies retain their proofs; only the enclosing unit namespace changes.
The remaining alternating-position decoder and shuffle argument are written for
this make.fun unit tc_closure_pshuffle_np.
-/

namespace PvsNP.Units.tc_closure_pshuffle_np

-- upstream PEqualNP.Defs.Base
section
/-!
# The definitions this project stands on

The ruling behind this file is `Library/README.md`. In short:

* Machines, their step function, running time and "computes `f` within a time bound" are
  Mathlib's: `Turing.FinTM2` (a multi-stack machine with finitely many stacks, labels and
  internal states), `Turing.TM2OutputsInTime`, `Turing.TM2ComputableInTime` and
  `Turing.TM2ComputableInPolyTime`.
* Mathlib stops there. It has no decision problems, no P, no NP and no reductions, and its
  notions are data (`Type`), not propositions. Everything below is the thin layer of
  propositions on top.

Inputs are binary strings, `List Bool`, encoded as themselves. A language is a
`Language Bool`, which is `Set (List Bool)`.
-/

namespace PEqualNP.Library

/-- `f` is computed by some machine within `t (length of the encoded input)` steps. -/
def ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    (t : ℕ → ℕ) : Prop :=
  ∃ c : Turing.TM2ComputableInTime ea eb f, ∀ n, c.time n ≤ t n

/-- `f` is computed by some machine within a polynomial number of steps in the length of the
encoded input. -/
def ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) :
    Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- The set `S` is decided within time `t`: some `f` computed within `t` steps answers `true`
exactly on the members of `S`. The answer is the one-symbol string `[true]` or `[false]`. -/
def DecidableInTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) (t : ℕ → ℕ) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInTime ea Computability.encodeBool f t

/-- The set `S` is decided in polynomial time. -/
def DecidableInPolyTime {α αΓ : Type} (ea : α → List αΓ) (S : Set α) : Prop :=
  ∃ f : α → Bool, (∀ a, a ∈ S ↔ f a = true) ∧ ComputableInPolyTime ea Computability.encodeBool f

/-- A pair of binary strings, written over the alphabet `Bool ⊕ Bool`: the first string tagged
`Sum.inl`, then the second tagged `Sum.inr`. This is the `encode` of Mathlib's
`Computability.encodingProd` on two copies of `Computability.encodingList Bool`. Its length is
the sum of the two lengths. -/
def encodePair (p : List Bool × List Bool) : List (Bool ⊕ Bool) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

/-- DTIME(t): the languages decided within `t (input length)` steps. -/
def DTIME (t : ℕ → ℕ) : Set (Language Bool) :=
  {L | DecidableInTime (fun x : List Bool => x) L t}

/-- P: the languages decided in polynomial time. -/
def P : Set (Language Bool) :=
  {L | DecidableInPolyTime (fun x : List Bool => x) L}

/-- NP, by verifiers: `L` is in NP when there are a polynomial-time decidable set `R` of pairs
(input, witness) and a polynomial `p` such that `x` is in `L` exactly when some witness `w` of
length at most `p (length of x)` has `(x, w)` in `R`. -/
def NP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ (x, w) ∈ R}

/-- Polynomial-time many-one (Karp) reducibility: a polynomial-time computable `f` maps members
of `L₁` to members of `L₂` and non-members to non-members. -/
def PolyTimeReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool,
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ x, x ∈ L₁ ↔ f x ∈ L₂

/-- `L` is NP-hard: every language in NP reduces to it in polynomial time. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, PolyTimeReducible L' L

/-- `L` is NP-complete: in NP and NP-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

end PEqualNP.Library
end

-- upstream PEqualNP.Defs.Classes
section
/-!
# Further uniform classes: coNP, EXP, NEXP

On top of `Defs/Base.lean` (machines, time bounds, `DTIME`, `P`, `NP`), in the same namespace.
Nothing here is in the pinned Mathlib.

* `coNP`: the complements of the NP languages.
* `EXP`: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`.
* `NEXP`, by verifiers, as `NP` is: a polynomial-time decidable relation with witnesses of
  length at most `2 ^ (n ^ k) + k` for some `k`. The verifier is polynomial in the length of
  the pair, so exponential in the length of the input.

Every bound `2 ^ p(n)` with `p` a polynomial is below `2 ^ (n ^ k) + k` for some `k`, so the
single family of bounds loses nothing.
-/

namespace PEqualNP.Library

/-- coNP: the languages whose complement is in NP. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- EXP: the languages decided within `2 ^ (n ^ k) + k` steps for some `k`. -/
def EXP : Set (Language Bool) :=
  {L | ∃ k : ℕ, L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)}

/-- NEXP, by verifiers: `L` is in NEXP when there are a polynomial-time decidable set `R` of
pairs (input, witness) and a `k` such that `x` is in `L` exactly when some witness `w` of length
at most `2 ^ (length of x ^ k) + k` has `(x, w)` in `R`. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (R : Set (List Bool × List Bool)) (k : ℕ),
    DecidableInPolyTime encodePair R ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ (x, w) ∈ R}

end PEqualNP.Library
end

-- upstream PEqualNP.Library.Machines.Run
section
/-!
# Running machines: generic facts

Helper module (proofs only, no statement may use it).

* iterating the step function from `none` stays at `none`;
* a step-by-step simulation carries a run of one machine to a run of another;
* a stack grows by at most a constant per step (`maxPush`), so the output of a machine is at
  most the input length plus a constant times the number of steps;
* the initial and the final configuration written with `Function.update`;
* a polynomial with natural coefficients is monotone.
-/

namespace PEqualNP.Library.Machines

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

/-- If every step of `f` is matched by a step of `g` through `emb`, a run of `f` is matched by a
run of `g` of the same length. -/
theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- The largest number of pushes one run of a statement can make. -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

/-- The largest number of pushes one step of a machine can make. -/
noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Compose
section
/-!
# Running one machine after another

Helper module (proofs only, no statement may use it).

Given machines `M1` and `M2` and a map `φ` from the output alphabet of `M1` to the input alphabet
of `M2`, `comp M1 M2 φ d` keeps the stacks of both machines side by side, plus one temporary
stack. It runs `M1`; where `M1` would halt it moves the output stack of `M1` onto the temporary
stack (which reverses it) and from there onto the input stack of `M2` (which restores the order),
translating each symbol by `φ`; then it runs `M2`.

A push needs a total function from the internal state to the symbol pushed, so the transfer
needs some symbol `d` of the input alphabet of `M2` as a default that is never actually written.
When that alphabet is empty there is nothing to move and the transfer is a single jump.
-/

namespace PEqualNP.Library.Machines

open Turing

section update

variable {ι : Type} [DecidableEq ι] {β : ι → Type}

theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

end update

variable (M1 M2 : FinTM2)

/-- The stacks: one temporary stack, the stacks of `M1`, the stacks of `M2`. -/
abbrev CK : Type := Option (M1.K ⊕ M2.K)

/-- The stack alphabets. The temporary stack holds input symbols of `M2`. -/
abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k

/-- The labels: those of `M1`, those of `M2`, and the two transfer loops. -/
abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool

/-- The internal state: that of `M1`, that of `M2`, and one symbol in transit. -/
abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

variable {M1 M2}

/-- A statement of `M1` inside the composite. Halting becomes a jump to the transfer. -/
def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

/-- A statement of `M2` inside the composite. -/
def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

variable (M1 M2)

/-- First transfer loop: output stack of `M1` to the temporary stack. -/
def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))

/-- Second transfer loop: the temporary stack to the input stack of `M2`. -/
def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))

/-- The program of the composite. -/
def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d

/-- The composite machine. -/
def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M2.Γk₀Fin
  { K := CK M1 M2
    k₀ := some (Sum.inl M1.k₀)
    k₁ := some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main := Sum.inl M1.main
    σ := Cσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }

variable {M1 M2}

/-- The stacks of `M1` inside the composite, everything else empty. -/
def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

/-- The stacks of `M2` inside the composite, everything else empty. -/
def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk1 S) (some (Sum.inl k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk2 S) (some (Sum.inr k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]

theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

/-- A configuration of `M1` inside the composite; a halted `M1` stands at the transfer. -/
def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩

/-- A configuration of `M2` inside the composite. -/
def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩

theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))

theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)

theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)

/-- The stacks during the transfer: output of `M1`, temporary, input of `M2`. -/
def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u

theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]

theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _

theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.ComposeRun
section
/-!
# The composite machine computes the composition in polynomial time

Helper module (proofs only, no statement may use it). The run of `comp M1 M2 φ d` is the run of
`M1`, then the two transfer loops, then the run of `M2`. The output of `M1` is no longer than the
input plus `maxPush M1` per step, which keeps the whole run polynomial.
-/

namespace PEqualNP.Library.Machines

open Turing

variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)

/-- Configurations of the composite. -/
abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)

theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]

theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]

theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]

theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]

theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp

theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp

/-- The transfer: from a halted `M1` to a fresh `M2`, in at most `2 * length + 2` steps. -/
theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp

theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

/-- The run of the composite, with its length. -/
theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl

/-- Polynomial-time computable functions compose. -/
theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FilterMap
section
/-!
# A machine that maps and filters its input symbol by symbol

Helper module (proofs only, no statement may use it).

For `φ : Γ₀ → Option Γ₁` the machine `fm φ d` turns the input `l` into `l.filterMap φ`. It moves
the input onto a temporary stack (which reverses it), then moves the temporary stack to the
output, writing `φ x` for each symbol `x` when it is defined. It takes `2 * length + 2` steps.

Used for: negating an answer bit, and the first component of a pair.

A push needs a total function from the internal state to the symbol pushed, so the machine takes
a default output symbol `d` that is never actually written. With no output symbol at all
(`d = none`) nothing is ever written.
-/

namespace PEqualNP.Library.Machines

open Turing

variable {Γ₀ Γ₁ : Type}

/-- Stack alphabets: input (`some false`), temporary (`none`), output (`some true`). -/
abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁

/-- The program: label `false` empties the input, label `true` writes the output. -/
def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
            | none => .goto fun _ => true)
          (.goto fun _ => true))
        .halt)

/-- The machine. -/
def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main := false
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := fmProg φ d

/-- The stacks: input, temporary, output. -/
def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

/-- Configurations of the machine. -/
abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)

variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]

theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

/-- A function whose encoded output is the encoded input mapped and filtered symbol by symbol is
computable in linear time. -/
theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := fm φ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.TwoPass
section
/-!
# A machine that reads its input twice, mapping and filtering it symbol by symbol

Helper module (proofs only, no statement may use it).

For `φ₁ φ₂ : Γ₀ → Option Γ₁` the machine `tp φ₁ φ₂ d` turns the input `l` into
`l.filterMap φ₁ ++ l.filterMap φ₂`. It has five stacks: input, three temporary stacks, output.

* Loop `a` moves the input onto the first temporary stack (which reverses it).
* Loop `b` moves the first temporary stack onto the second one, writing `φ₂ x` on the output for
  each symbol `x` when it is defined. The second temporary stack is again in the original order.
* Loop `c` moves the second temporary stack onto the third one (reversed again).
* Loop `e` empties the third temporary stack, writing `φ₁ x` on the output when it is defined.

It takes `4 * length + 4` steps.

Used for: duplicating a string into a pair, and swapping the components of a pair.

A push needs a total function from the internal state to the symbol pushed, so the machine takes
a default output symbol `d` that is never actually written. With no output symbol at all
(`d = none`) nothing is ever written.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- The five stacks: input, three temporary stacks, output. -/
inductive TPK : Type
  | inp | t1 | t2 | t3 | out
  deriving DecidableEq

instance : Fintype TPK :=
  Fintype.ofList [.inp, .t1, .t2, .t3, .out] (fun x => by cases x <;> simp)

/-- The four loops. -/
inductive TPL : Type
  | a | b | c | e
  deriving DecidableEq

instance : Fintype TPL :=
  Fintype.ofList [.a, .b, .c, .e] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ : Type}

/-- Stack alphabets. -/
abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | .inp => Γ₀
  | .t1 => Option Γ₀
  | .t2 => Option Γ₀
  | .t3 => Option Γ₀
  | .out => Γ₁

/-- Write `φ s` on the output when it is defined, then go to `lbl`. -/
def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push .out (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)

/-- The program. -/
def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | .a =>
    .pop .inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .t1 (fun s => s) (.goto fun _ => .a))
        (.goto fun _ => .b))
  | .b =>
    .pop .t1 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t2 (fun s => s) (tpWrite φ₂ d .b))
        (.goto fun _ => .c))
  | .c =>
    .pop .t2 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push .t3 (fun s => s) (.goto fun _ => .c))
        (.goto fun _ => .e))
  | .e =>
    .pop .t3 (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d .e)
        .halt)

/-- The machine. -/
def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := .inp
  k₁ := .out
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := .a
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d

/-- The stacks. -/
def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | .inp => l
  | .t1 => a
  | .t2 => b
  | .t3 => c
  | .out => u

theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .inp l' = st5 l' a b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t1 a' = st5 l a' b c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t2 b' = st5 l a b' c u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) .t3 c' = st5 l a b c' u := by
  funext k; cases k <;> simp [st5]

theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) .out u' = st5 l a b c u' := by
  funext k; cases k <;> simp [st5]

theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .inp l := by
  funext k; cases k <;> simp [st5]

theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) .out u := by
  funext k; cases k <;> simp [st5]

/-- Configurations of the machine. -/
abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)

variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]

theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .a, s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]

theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .b, some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]

theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .b, s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]

theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .c, some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]

theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .c, s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]

theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some .e, some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]

theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some .e, s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]

theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some .a, s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .a, s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .a, some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp

theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .b, s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .b, s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .b, some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]

theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .c, s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .c, s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .c, some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp

theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some .e, s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some .e, s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some .e, some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]

theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
        (l.length + 1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
    (l.length + 1) + (l.length + 1) + (l.length + 1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
      (l.length + 1)]
    (some (⟨some .a, none, Function.update (fun _ => []) .inp l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) .out
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .a, none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .b, none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .c, none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some .e, none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]

/-- A function whose encoded output is the encoded input mapped and filtered symbol by symbol
twice, the two results one after the other, is computable in linear time. -/
theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.First
section
/-!
# Running a machine on the first component of a pair

Helper module (proofs only, no statement may use it).

For a machine `M` computing `f` on binary strings, `firstM M e₀ e₁` computes
`(x, w) ↦ (f x, w)` on the pair encoding. It has the stacks of `M` and four more: the input `I`,
a store `W` for the second component, a temporary stack `T` and the output `O`.

1. `l1`: empty `I`; first components go to `T`, second components to `W` (both reversed).
2. `l2`: move `T` to the input stack of `M` (order restored).
3. run `M`, whose statements never touch the four extra stacks.
4. `l3`: move `W` to `O`, tagged as second components (order restored).
5. `l4`: move the output of `M` to `T`. `l5`: move `T` to `O`, tagged as first components.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- The four extra stacks. -/
inductive FX
  | I | W | T | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.T, FX.O] (fun x => by cases x <;> simp)

/-- The five extra labels. -/
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2)

/-- Stack alphabets of the composite. -/
abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => Bool ⊕ Bool
  | Sum.inr FX.W => Bool
  | Sum.inr FX.T => Bool
  | Sum.inr FX.O => Bool ⊕ Bool

/-- Labels of the composite. -/
abbrev FstΛ : Type := M.Λ ⊕ FL

/-- Internal state of the composite: that of `M` and one symbol in transit. -/
abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)

/-- The bit carried by a symbol in transit. -/
def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b

/-- Whether the symbol in transit is a first component. -/
def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

variable {M}

/-- A statement of `M` inside the composite. Halting becomes a jump to `l3`. -/
def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M)

/-- The program of the composite. -/
def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.T) (fun s => bit s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.T) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

/-- The composite machine. -/
def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }

variable {M}

/-- All stacks of the composite: those of `M`, then `I`, `W`, `T`, `O`. -/
def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.T => t
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.I) i' = fstk S i' w t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.W) w' = fstk S i w' t o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr FX.T) t' = fstk S i w t' o := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr FX.O) o' = fstk S i w t o' := by
  funext j
  rcases j with j | (_ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

/-- Configurations of the composite. -/
abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)

/-- A configuration of `M` inside the composite; a halted `M` stands at `l3`. -/
def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w t o⟩

theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FirstRun
section
/-!
# The run of the first-component machine

Helper module (proofs only, no statement may use it). Five loops and the run of `M` in between,
then the time bound: the output of `M` is at most the input plus `maxPush M` per step.
-/

namespace PEqualNP.Library.Machines

open Turing

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr FX.T) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr FX.O) = o := rfl
end fstk

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))

/-! ### `l1`: split the input -/

theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]

theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]

theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]

/-! ### `l2`: load the input stack of `M` -/

theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp

/-! ### `l3`: the second component goes to the output -/

theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]

theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp

/-! ### `l4`: the output of `M` goes to the temporary stack -/

theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp

/-! ### `l5`: the first component goes to the output -/

theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]

theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.FirstPoly
section
/-!
# Running a polynomial-time function on the first component of a pair is polynomial time

Helper module (proofs only, no statement may use it).
-/

namespace PEqualNP.Library.Machines

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _) <;> rfl

theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])

theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])

theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl

theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]

/-- The run of the composite on a pair. -/
theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega

/-- If `f` is polynomial-time computable on binary strings then so is `(x, w) ↦ (f x, w)` on the
pair encoding. -/
theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Pairing
section
/-!
# Pairing combinators for polynomial-time computable functions

Helper module (proofs only, no statement may use it).

Small closure properties of `PEqualNP.Library.ComputableInPolyTime` on binary strings and on
pairs of binary strings written with `PEqualNP.Library.encodePair`: composition, swapping,
duplication, the two projections, concatenation, acting on one component, and pairing two
functions. They are all obtained from the machines built in the neighbouring modules.
-/

namespace PEqualNP.Library.Machines

open PEqualNP.Library

private theorem filterMap_map_some {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

private theorem filterMap_map_none {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

/-- Composition of polynomial-time computable functions. -/
theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2

/-- Swapping the two components of a pair. -/
theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

/-- Duplicating a string. -/
theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]

/-- The first projection. -/
theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

/-- The second projection. -/
theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

/-- Concatenating the two components of a pair. -/
theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

/-- Acting on the first component of a pair. -/
theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c

/-- Acting on the second component of a pair. -/
theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap

/-- Pairing two functions of the same string. -/
theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)

/-- The identity on strings. -/
theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.AllTrue
section
/-!
# A machine that decides whether every bit of a pair of strings is true

Helper module (proofs only, no statement may use it). Two stacks: the input (tagged bits) and the
output (one bit). The single labelled statement pops one input symbol and ANDs its bit into the
internal state; when the input is empty it pushes the accumulated bit onto the output, resets the
internal state and halts. On an input of length `n` it halts after `n + 1` steps.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Stack alphabets: input (`false`), output (`true`). -/
abbrev AΓ : Bool → Type
  | false => Bool ⊕ Bool
  | true => Bool

/-- The bit carried by a tagged symbol. -/
def aval : Bool ⊕ Bool → Bool := Sum.elim id id

/-- The program. The state is (accumulated bit, whether a symbol was popped). -/
def atProg : Unit → TM2.Stmt AΓ Unit (Bool × Bool) :=
  fun _ => .pop false (fun s o => (s.1 && (o.map aval).getD true, o.isSome))
    (.branch (fun s => s.2)
      (.goto fun _ => ())
      (.push true (fun s => s.1) (.load (fun _ => (true, false)) .halt)))

/-- The machine. -/
def atM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := AΓ
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (true, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := atProg

/-- The stacks: input, output. -/
def ast (l : List (Bool ⊕ Bool)) (u : List Bool) : ∀ k, List (AΓ k)
  | false => l
  | true => u

theorem ast_in (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u false = l := rfl

theorem ast_out (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u true = u := rfl

theorem ast_set_in (l l' : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (ast l u) false l' = ast l' u := by
  funext k
  cases k <;> simp [ast]

theorem ast_set_out (l : List (Bool ⊕ Bool)) (u u' : List Bool) :
    Function.update (ast l u) true u' = ast l u' := by
  funext k
  cases k <;> simp [ast]

theorem ast_start (l : List (Bool ⊕ Bool)) :
    ast l [] = Function.update (fun _ => [] : ∀ k, List (AΓ k)) false l := by
  funext k
  cases k <;> simp [ast]

theorem ast_end (u : List Bool) :
    ast [] u = Function.update (fun _ => [] : ∀ k, List (AΓ k)) true u := by
  funext k
  cases k <;> simp [ast]

/-- Configurations of the machine. -/
abbrev ACfg : Type := TM2.Cfg AΓ Unit (Bool × Bool)

theorem at_cons (s : Bool × Bool) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast (x :: l) u⟩ : ACfg) =
      some ⟨some (), (s.1 && aval x, true), ast l u⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_set_in]

theorem at_nil (s : Bool × Bool) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast [] u⟩ : ACfg) =
      some ⟨none, (true, false), ast [] (s.1 :: u)⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_out, ast_set_in, ast_set_out]

theorem at_loop :
    ∀ (l : List (Bool ⊕ Bool)) (s : Bool × Bool),
      (flip bind (TM2.step atProg))^[l.length + 1]
          (some (⟨some (), s, ast l []⟩ : ACfg)) =
        some ⟨none, (true, false), ast [] [s.1 && l.all aval]⟩ := by
  intro l
  induction l with
  | nil =>
    intro s
    have h : (s.1 && ([] : List (Bool ⊕ Bool)).all aval) = s.1 := by simp
    rw [h]
    exact at_nil s []
  | cons x l ih =>
    intro s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step atProg)
        (some (⟨some (), s, ast (x :: l) []⟩ : ACfg)) =
        some ⟨some (), (s.1 && aval x, true), ast l []⟩ := at_cons s x l []
    rw [e, ih]
    simp [Bool.and_assoc]

theorem at_run (l : List (Bool ⊕ Bool)) :
    (flip bind (TM2.step atProg))^[l.length + 1]
        (some (initList atM l)) = some (haltList atM [l.all aval]) := by
  refine (congrArg (fun c => (flip bind (TM2.step atProg))^[l.length + 1]
    (some c)) (initList_eq atM l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq atM [l.all aval])).symm)
  show (flip bind (TM2.step atProg))^[l.length + 1]
    (some (⟨some (), (true, false), Function.update (fun _ => []) false l⟩ : ACfg)) =
    some (⟨none, (true, false), Function.update (fun _ => []) true [l.all aval]⟩ : ACfg)
  rw [← ast_start, at_loop, ← ast_end]
  simp

theorem all_aval_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).all aval = (p.1 ++ p.2).all id := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  unfold PEqualNP.Library.encodePair
  rw [List.all_append, List.all_append, h1, h2]

/-- Whether every bit of both components of a pair is true is decidable in `n + 1` steps. -/
theorem allTrue_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => (p.1 ++ p.2).all id)) :=
  ⟨{
    tm := atM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun p =>
      { steps := (PEqualNP.Library.encodePair p).length + 1
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [(PEqualNP.Library.encodePair p).all aval] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool ((p.1 ++ p.2).all id)) := by
            rw [hm, all_aval_encodePair]
            rfl
          exact (congrArg (fun x => (flip bind (TM2.step atProg))^[
            (PEqualNP.Library.encodePair p).length + 1]
            (some (initList atM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((at_run (PEqualNP.Library.encodePair p)).trans
              (congrArg (fun x => some (haltList atM x)) hout))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.LenLE
section
/-!
# A machine that decides whether the second string of a pair is no longer than the first

Helper module (proofs only, no statement may use it). It lives in its own namespace `LenCmp`, so
that it can be imported together with the multiplication machine. Four stacks: the input (tagged bits), two
unary counters and the output (one bit). The first loop moves the input onto the counters, one
mark per symbol of the first and of the second component. The second loop pops one mark from each
counter until one of them is empty: if the second counter is empty the answer is true, otherwise
the answer is false. An erasing loop then empties the other counter, writes the answer and halts.
On an input of length `n` it halts after at most `2 * n + 3` steps.
-/

namespace PEqualNP.Library.Machines.LenCmp

open Turing

/-- Stack alphabets: input, first counter, second counter, output. -/
abbrev LΓ : Bool × Bool → Type
  | (false, false) => Bool ⊕ Bool
  | (false, true) => Unit
  | (true, false) => Unit
  | (true, true) => Bool

/-- Labels: split the input, compare the counters, erase the first or the second counter. -/
inductive LL : Type
  | split
  | cmp
  | eraseA
  | eraseB
  deriving DecidableEq

instance : Fintype LL :=
  Fintype.ofList [LL.split, LL.cmp, LL.eraseA, LL.eraseB] (fun x => by cases x <;> simp)

/-- The program. -/
def lenProg : LL → TM2.Stmt LΓ LL (Bool × Bool)
  | .split =>
    .pop (false, false) (fun _ o => (o.isSome, (o.map Sum.isRight).getD false))
      (.branch (fun s => s.1)
        (.branch (fun s => s.2)
          (.push (true, false) (fun _ => ()) (.goto fun _ => .split))
          (.push (false, true) (fun _ => ()) (.goto fun _ => .split)))
        (.goto fun _ => .cmp))
  | .cmp =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.pop (true, false) (fun s o => (s.1, o.isSome))
        (.branch (fun s => s.2)
          (.branch (fun s => s.1)
            (.goto fun _ => .cmp)
            (.load (fun _ => (false, false)) (.goto fun _ => .eraseB)))
          (.load (fun _ => (false, false)) (.goto fun _ => .eraseA))))
  | .eraseA =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseA)
        (.push (true, true) (fun _ => true) (.load (fun _ => (false, false)) .halt)))
  | .eraseB =>
    .pop (true, false) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => .eraseB)
        (.push (true, true) (fun _ => false) (.load (fun _ => (false, false)) .halt)))

/-- The machine. -/
def lenM : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := LΓ
  Λ := LL
  main := .split
  σ := Bool × Bool
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := lenProg

/-- The stacks: input, the two counters (as numbers), output. -/
def lst (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) : ∀ k, List (LΓ k)
  | (false, false) => l
  | (false, true) => List.replicate a ()
  | (true, false) => List.replicate b ()
  | (true, true) => o

theorem lst_in (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, false) = l := rfl

theorem lst_a (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, true) = List.replicate a () := rfl

theorem lst_b (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, false) = List.replicate b () := rfl

theorem lst_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, true) = o := rfl

theorem lst_set_in (l l' : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, false) l' = lst l' a b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (Bool ⊕ Bool)) (a a' b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, true) (List.replicate a' ()) = lst l a' b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (Bool ⊕ Bool)) (a b b' : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) (List.replicate b' ()) = lst l a b' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b0 (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) [] = lst l a 0 o :=
  lst_set_b l a b 0 o

theorem lst_set_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o o' : List Bool) :
    Function.update (lst l a b o) (true, true) o' = lst l a b o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (Bool ⊕ Bool)) :
    lst l 0 0 [] = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst [] 0 0 o = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

/-- Configurations of the machine. -/
abbrev LCfg : Type := TM2.Cfg LΓ LL (Bool × Bool)

/-- The step function on optional configurations. -/
abbrev lenStep : Option LCfg → Option LCfg := flip bind (TM2.step lenProg)

theorem split_inl (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inl x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, false), lst l (a + 1) b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inl, Option.getD_some, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_a, ← List.replicate_succ, lst_set_a]

theorem split_inr (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst (Sum.inr x :: l) a b o⟩ : LCfg) =
      some ⟨some .split, (true, true), lst l a (b + 1) o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inr, Option.getD_some, Bool.cond_true]
  rw [lst_set_in, lst_b, ← List.replicate_succ, lst_set_b]

theorem split_nil (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .split, s, lst [] a b o⟩ : LCfg) =
      some ⟨some .cmp, (false, false), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Option.map_none,
    Option.getD_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_ss (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] (a + 1) (b + 1) o⟩ : LCfg) =
      some ⟨some .cmp, (true, true), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
  rw [lst_set_a, lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem cmp_b0 (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] a 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (false, false), lst [] (a - 1) 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_b0]

theorem cmp_a0 (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .cmp, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (false, false), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.replicate_succ, List.head?_nil, List.head?_cons,
    List.tail_cons, Option.isSome_none, Option.isSome_some, Bool.cond_false, Bool.cond_true]
  rw [lst_set_b]

theorem eraseA_s (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] (a + 1) 0 o⟩ : LCfg) =
      some ⟨some .eraseA, (true, s.2), lst [] a 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_a]

theorem eraseA_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseA, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (true :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem eraseB_s (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some .eraseB, (true, s.2), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem eraseB_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some .eraseB, s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (false :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b, List.tail_replicate, lst_set_b]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (Bool ⊕ Bool)) (a b : ℕ) (s : Bool × Bool),
      lenStep^[l.length + 1] (some (⟨some .split, s, lst l a b []⟩ : LCfg)) =
        some ⟨some .cmp, (false, false),
          lst [] (a + l.countP Sum.isLeft) (b + l.countP Sum.isRight) []⟩ := by
  intro l
  induction l with
  | nil => intro a b s; exact split_nil s a b []
  | cons x l ih =>
    intro a b s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inl x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, false), lst l (a + 1) b []⟩ := split_inl s x l a b []
      have h1 : a + 1 + l.countP Sum.isLeft =
          a + (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isRight =
          (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]
    | inr x =>
      have e : lenStep (some (⟨some .split, s, lst (Sum.inr x :: l) a b []⟩ : LCfg)) =
          some ⟨some .split, (true, true), lst l a (b + 1) []⟩ := split_inr s x l a b []
      have h1 : b + 1 + l.countP Sum.isRight =
          b + (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isLeft =
          (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]

theorem cmpLoopT :
    ∀ (b c : ℕ) (s : Bool × Bool),
      lenStep^[b + 1] (some (⟨some .cmp, s, lst [] (b + c) b []⟩ : LCfg)) =
        some ⟨some .eraseA, (false, false), lst [] (c - 1) 0 []⟩ := by
  intro b
  induction b with
  | zero =>
    intro c s
    rw [Nat.zero_add c]
    exact cmp_b0 s c []
  | succ b ih =>
    intro c s
    rw [Function.iterate_succ_apply]
    have hbc : b + 1 + c = b + c + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (b + 1 + c) (b + 1) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] (b + c) b []⟩ := by
      rw [hbc]; exact cmp_ss s (b + c) b []
    rw [e, ih]

theorem cmpLoopF :
    ∀ (a d : ℕ) (s : Bool × Bool),
      lenStep^[a + 1] (some (⟨some .cmp, s, lst [] a (a + 1 + d) []⟩ : LCfg)) =
        some ⟨some .eraseB, (false, false), lst [] 0 d []⟩ := by
  intro a
  induction a with
  | zero =>
    intro d s
    have h : 0 + 1 + d = d + 1 := by omega
    rw [h]
    exact cmp_a0 s d []
  | succ a ih =>
    intro d s
    rw [Function.iterate_succ_apply]
    have had : a + 1 + 1 + d = a + 1 + d + 1 := by omega
    have e : lenStep (some (⟨some .cmp, s, lst [] (a + 1) (a + 1 + 1 + d) []⟩ : LCfg)) =
        some ⟨some .cmp, (true, true), lst [] a (a + 1 + d) []⟩ := by
      rw [had]; exact cmp_ss s a (a + 1 + d) []
    rw [e, ih]

theorem eraseALoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseA, s, lst [] n 0 []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [true]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseA_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseA, s, lst [] (n + 1) 0 []⟩ : LCfg)) =
        some ⟨some .eraseA, (true, s.2), lst [] n 0 []⟩ := eraseA_s s n []
    rw [e, ih]

theorem eraseBLoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some .eraseB, s, lst [] 0 n []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [false]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseB_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some .eraseB, s, lst [] 0 (n + 1) []⟩ : LCfg)) =
        some ⟨some .eraseB, (true, s.2), lst [] 0 n []⟩ := eraseB_s s n []
    rw [e, ih]

theorem len_run (l : List (Bool ⊕ Bool)) (a b : ℕ) (ha : l.countP Sum.isLeft = a)
    (hb : l.countP Sum.isRight = b) (hab : a + b ≤ l.length) :
    ∃ n, n ≤ 2 * l.length + 3 ∧
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
  have hs := splitLoop l 0 0 (false, false)
  rw [Nat.zero_add, Nat.zero_add, ha, hb] at hs
  have key : ∀ n : ℕ,
      lenStep^[n] (some (⟨some .split, (false, false), lst l 0 0 []⟩ : LCfg)) =
        some (⟨none, (false, false), lst [] 0 0 [decide (b ≤ a)]⟩ : LCfg) →
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
    intro n h
    refine (congrArg (fun c => lenStep^[n] (some c)) (initList_eq lenM l)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq lenM [decide (b ≤ a)])).symm)
    show lenStep^[n]
      (some (⟨some .split, (false, false), Function.update (fun _ => []) (false, false) l⟩ :
        LCfg)) =
      some (⟨none, (false, false),
        Function.update (fun _ => []) (true, true) [decide (b ≤ a)]⟩ : LCfg)
    rw [← lst_start, ← lst_end]
    exact h
  by_cases h : b ≤ a
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨(c - 1 + 1) + ((b + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (b ≤ b + c) = true := by simp
    rw [Function.iterate_add_apply _ (c - 1 + 1) _, Function.iterate_add_apply _ (b + 1) _, hs,
      cmpLoopT, eraseALoop, hd]
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    refine ⟨(d + 1) + ((a + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (a + 1 + d ≤ a) = false := decide_eq_false h
    rw [Function.iterate_add_apply _ (d + 1) _, Function.iterate_add_apply _ (a + 1) _, hs,
      cmpLoopF, eraseBLoop, hd]

theorem countP_isLeft_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isLeft = p.1.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isLeft =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isLeft = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.add_zero]

theorem countP_isRight_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isRight = p.2.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isRight =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isRight = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.zero_add]

theorem lenLE_run (p : List Bool × List Bool) :
    ∃ n, n ≤ 2 * (PEqualNP.Library.encodePair p).length + 3 ∧
      lenStep^[n] (some (initList lenM (PEqualNP.Library.encodePair p))) =
        some (haltList lenM [decide (p.2.length ≤ p.1.length)]) :=
  len_run (PEqualNP.Library.encodePair p) p.1.length p.2.length
    (countP_isLeft_encodePair p) (countP_isRight_encodePair p)
    (by simp [PEqualNP.Library.encodePair])

/-- Whether the second component of a pair is no longer than the first is decidable in at most
`2 * n + 3` steps. -/
theorem lenLE_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length))) :=
  ⟨{
    tm := lenM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := Classical.choose (lenLE_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.2.length ≤ p.1.length)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.2.length ≤ p.1.length))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => lenStep^[Classical.choose (lenLE_run p)]
            (some (initList lenM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((Classical.choose_spec (lenLE_run p)).2.trans
              (congrArg (fun x => some (haltList lenM x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (lenLE_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.Library.Machines.LenCmp
end

-- upstream PEqualNP.Library.Machines.FirstG
section
/-!
# Running a machine on the first component of a pair, any alphabets

Helper module (proofs only, no statement may use it).

A pair of a list over `A` and a list over `C` is written over `A ⊕ C`: the first list tagged
`Sum.inl`, then the second tagged `Sum.inr`. For a machine `M` computing `f` from strings over
`A` to strings over `B`, `firstM M e₀ e₁` computes `(a, w) ↦ (f a, w)`. It has the stacks of `M`
and five more: the input `I`, a store `W` for the second component, temporary stacks `TA` and
`TB`, and the output `O`.

1. `l1`: empty `I`; first components go to `TA`, second components to `W` (both reversed).
2. `l2`: move `TA` to the input stack of `M` (order restored).
3. run `M`, whose statements never touch the five extra stacks.
4. `l3`: move `W` to `O`, tagged as second components (order restored).
5. `l4`: move the output of `M` to `TB`. `l5`: move `TB` to `O`, tagged as first components.

A push needs a total function from the internal state to the symbol pushed, so the alphabets
are asked to be inhabited; the default symbols are never written.
-/

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

/-- The pair of two lists, over the sum alphabet. -/
def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

/-- The five extra stacks. -/
inductive FX
  | I | W | TA | TB | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.TA, FX.TB, FX.O] (fun x => by cases x <;> simp)

/-- The five extra labels. -/
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2) (A B C : Type)

/-- Stack alphabets of the composite. -/
abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => A ⊕ C
  | Sum.inr FX.W => C
  | Sum.inr FX.TA => A
  | Sum.inr FX.TB => B
  | Sum.inr FX.O => B ⊕ C

/-- Labels of the composite. -/
abbrev FstΛ : Type := M.Λ ⊕ FL

/-- Internal state of the composite: that of `M` and one symbol in transit. -/
abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

/-- The symbol in transit, read as a symbol of `A`. -/
def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

/-- The symbol in transit, read as a symbol of `B`. -/
def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

/-- The symbol in transit, read as a symbol of `C`. -/
def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

/-- Whether the symbol in transit is a symbol of `A`. -/
def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

/-- An input symbol as a symbol in transit. -/
def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

/-- A statement of `M` inside the composite. Halting becomes a jump to `l3`. -/
def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

/-- The program of the composite. -/
def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr FX.TA) (fun s => getA s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => getC s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.TA) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.TB) (fun s => getB s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.TB) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

/-- The composite machine. -/
def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

/-- All stacks of the composite: those of `M`, then `I`, `W`, `TA`, `TB`, `O`. -/
def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.TA => ta
  | Sum.inr FX.TB => tb
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr FX.TA) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr FX.TB) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr FX.O) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.I) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.W) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TA) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TB) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.O) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

variable (M A B C) in
/-- Configurations of the composite. -/
abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

/-- A configuration of `M` inside the composite; a halted `M` stands at `l3`. -/
def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Library.Machines.Gen
end

-- upstream PEqualNP.Library.Machines.FirstGRun
section
/-!
# The run of the first-component machine over any alphabets

Helper module (proofs only, no statement may use it). Five loops and the run of `M` in between,
then the time bound: the output of `M` is at most the input plus `maxPush M` per step. The
result is that running a polynomial-time function on the first component of a pair is
polynomial time, for any encodings of the first component.
-/

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

/-! ### `l1`: split the input -/

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

/-! ### `l2`: load the input stack of `M` -/

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

/-! ### `l3`: the second component goes to the output -/

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l4), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

/-! ### `l4`: the output of `M` goes to the temporary stack -/

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

/-! ### `l5`: the first component goes to the output -/

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

/-! ### The whole run -/

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _ | _) <;> rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

/-- The run of the composite on a pair. -/
theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

/-- If `f` is polynomial-time computable for the encodings `ea`, `eb` then so is
`(a, w) ↦ (f a, w)` for the pair encodings. -/
theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines.Gen
end

-- upstream PEqualNP.Library.Machines.Mul
section
/-!
# A machine that multiplies two lengths

Helper module (proofs only, no statement may use it).

Given a pair of strings `(x, w)` on its input stack, the machine writes `|x| * |w|` copies of
`true` on its output stack. It has five stacks: the input `I`, two counters `A` and `B`, a
temporary stack `C` and the output `O`.

* Label `split`: empty the input, one symbol on `A` for each symbol of `x`, one symbol on `B` for
  each symbol of `w`.
* Label `outer`: pop one symbol of `A`; when `A` is empty go to `clean`.
* Label `copy`: move `B` to `C`, writing one `true` on the output per symbol.
* Label `back`: move `C` back to `B`, then return to `outer`.
* Label `clean`: erase `B`, then halt.

It takes `|x| * (2 * |w| + 3) + |x| + 2 * |w| + 3` steps, which is at most
`2 * n ^ 2 + 5 * n + 3` for `n = |x| + |w|`.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- The stacks of the multiplication machine. -/
inductive MulK
  | I | A | B | C | O
  deriving DecidableEq

instance : Fintype MulK :=
  Fintype.ofList [.I, .A, .B, .C, .O] (fun x => by cases x <;> simp)

/-- The labels of the multiplication machine. -/
inductive MulL
  | split | outer | copy | back | clean
  deriving DecidableEq

instance : Fintype MulL :=
  Fintype.ofList [.split, .outer, .copy, .back, .clean] (fun x => by cases x <;> simp)

/-- Stack alphabets: the input holds an encoded pair, every other stack holds bits. -/
abbrev MulΓ : MulK → Type
  | .I => Bool ⊕ Bool
  | .A => Bool
  | .B => Bool
  | .C => Bool
  | .O => Bool

/-- The program. -/
def mulProg : MulL → TM2.Stmt MulΓ MulL (Option Bool)
  | .split =>
    .pop .I (fun _ o => o.map Sum.isLeft)
      (.branch (fun s => s.isSome)
        (.branch (fun s => s == some true)
          (.push .A (fun _ => true) (.goto fun _ => .split))
          (.push .B (fun _ => true) (.goto fun _ => .split)))
        (.goto fun _ => .outer))
  | .outer =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .copy)
        (.goto fun _ => .clean))
  | .copy =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .C (fun _ => true) (.push .O (fun _ => true) (.goto fun _ => .copy)))
        (.goto fun _ => .back))
  | .back =>
    .pop .C (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .clean =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .clean)
        .halt)

/-- The machine. -/
def mulTM : FinTM2 where
  K := MulK
  k₀ := .I
  k₁ := .O
  Γ := MulΓ
  Λ := MulL
  main := .split
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := mulProg

/-- All five stacks. -/
def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) : ∀ k, List (MulΓ k)
  | .I => i
  | .A => a
  | .B => b
  | .C => c
  | .O => o

@[simp] theorem mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .I = i := rfl
@[simp] theorem mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .A = a := rfl
@[simp] theorem mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .B = b := rfl
@[simp] theorem mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .C = c := rfl
@[simp] theorem mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o .O = o := rfl

@[simp] theorem mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    Function.update (mstk i a b c o) .I i' = mstk i' a b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
    Function.update (mstk i a b c o) .A a' = mstk i a' b c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
    Function.update (mstk i a b c o) .B b' = mstk i a b' c o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
    Function.update (mstk i a b c o) .C c' = mstk i a b c' o := by
  funext k; cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
    Function.update (mstk i a b c o) .O o' = mstk i a b c o' := by
  funext k; cases k <;> simp [mstk]

theorem mstk_start (i : List (Bool ⊕ Bool)) :
    mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .I i := by
  funext k; cases k <;> simp [mstk]

theorem mstk_end (o : List Bool) :
    mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) .O o := by
  funext k; cases k <;> simp [mstk]

/-- Configurations of the machine. -/
abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)

/-- One step of the machine on an optional configuration. -/
abbrev mulStep : Option MulCfg → Option MulCfg := flip bind (TM2.step mulProg)

/-! ### Single steps -/

theorem split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inl y :: i) a b c o⟩) =
      some ⟨some .split, some true, mstk i (true :: a) b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk (Sum.inr y :: i) a b c o⟩) =
      some ⟨some .split, some false, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_nil (s : Option Bool) (a b c o : List Bool) :
    mulStep (some ⟨some .split, s, mstk [] a b c o⟩) =
      some ⟨some .outer, none, mstk [] a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i (y :: a) b c o⟩) =
      some ⟨some .copy, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
    mulStep (some ⟨some .outer, s, mstk i [] b c o⟩) =
      some ⟨some .clean, none, mstk i [] b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .copy, some y, mstk i a b (true :: c) (true :: o)⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .copy, s, mstk i a [] c o⟩) =
      some ⟨some .back, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b (y :: c) o⟩) =
      some ⟨some .back, some y, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
    mulStep (some ⟨some .back, s, mstk i a b [] o⟩) =
      some ⟨some .outer, none, mstk i a b [] o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a (y :: b) c o⟩) =
      some ⟨some .clean, some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some .clean, s, mstk i a [] c o⟩) =
      some ⟨none, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

/-! ### Loops -/

/-- A stack of `n` copies of `true`. -/
abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem splitLoopW (a : List Bool) :
    ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
      mulStep^[w.length + 1] (some ⟨some .split, s, mstk (w.map Sum.inr) a (rep b) [] []⟩) =
        some ⟨some .outer, none, mstk [] a (rep (w.length + b)) [] []⟩ := by
  intro w
  induction w with
  | nil => intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, split_inr, rep_succ, ih]
    rw [show w.length + (b + 1) = w.length + 1 + b from by omega]

theorem splitLoopX (w : List Bool) :
    ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
      mulStep^[x.length + (w.length + 1)]
          (some ⟨some .split, s, mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
        some ⟨some .outer, none, mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [List.length_cons, show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
      from by omega, Function.iterate_succ_apply, List.map_cons, List.cons_append, split_inl,
      rep_succ, ih]
    rw [show x.length + (a + 1) = x.length + 1 + a from by omega]

theorem copyLoop (a : List Bool) :
    ∀ (b c o : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .copy, s, mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some .back, none, mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
  intro b
  induction b with
  | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [Function.iterate_succ_apply, ← rep_succ b, copy_cons, rep_succ, rep_succ, ih]
    rw [show b + (c + 1) = b + 1 + c from by omega, show b + (o + 1) = b + 1 + o from by omega]

theorem backLoop (a o : List Bool) :
    ∀ (c b : ℕ) (s : Option Bool),
      mulStep^[c + 1] (some ⟨some .back, s, mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some .outer, none, mstk [] a (rep (c + b)) [] o⟩ := by
  intro c
  induction c with
  | zero => intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← rep_succ c, back_cons, rep_succ, ih]
    rw [show c + (b + 1) = c + 1 + b from by omega]

theorem outerLoop (b : ℕ) :
    ∀ (a o : ℕ) (s : Option Bool),
      mulStep^[a * (2 * b + 3) + 1] (some ⟨some .outer, s, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .clean, none, mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
  intro a
  induction a with
  | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
      from by ring, Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
      Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
      Function.iterate_succ_apply mulStep (b + 1), ← rep_succ a, outer_cons]
    have h1 : mulStep^[b + 1]
        (some ⟨some .copy, some true, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2 : mulStep^[b + 1]
        (some ⟨some .back, none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
        some ⟨some .outer, none, mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
      backLoop (rep a) (rep (b + o)) b 0 none
    rw [h2, ih]
    rw [show a * b + (b + o) = (a + 1) * b + o from by ring]

theorem cleanLoop (o : List Bool) :
    ∀ (b : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some .clean, s, mstk [] [] (rep b) [] o⟩) =
        some ⟨none, none, mstk [] [] [] [] o⟩ := by
  intro b
  induction b with
  | zero => intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [Function.iterate_succ_apply, ← rep_succ b, clean_cons, ih]

/-- The number of steps of the machine on the pair `(x, w)`. -/
def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))

theorem mul_run (x w : List Bool) :
    (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList mulTM (rep (x.length * w.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some .split, none, Function.update (fun _ => []) .I
      (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (rep (x.length * w.length))⟩ : MulCfg)
  rw [← mstk_start, ← mstk_end, mulSteps, Function.iterate_add_apply mulStep (w.length + 1),
    Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
  have h1 : mulStep^[x.length + (w.length + 1)]
      (some ⟨some .split, none, mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
      some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
      (some ⟨some .outer, none, mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some .clean, none, mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2, cleanLoop]

/-- The product of the lengths of a pair of strings, written in unary, is computable in
quadratic time. -/
theorem mul_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow, encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.Clock
section
/-!
# A polynomial clock

Helper module (proofs only, no statement may use it).

For every polynomial `p` with natural coefficients, the function sending a string `x` to
`p (|x|)` copies of `true` is computable in polynomial time, provided every constant function
on strings is. The proof builds powers by repeated multiplication of lengths, monomials by one
more multiplication with a constant string, and sums by concatenation.
-/

namespace PEqualNP.Library.Machines

open PEqualNP.Library

/-- Multiplying the output lengths of two computable functions. -/
private theorem cpt_mul {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime

/-- The clock for a power of the input length. -/
private theorem pow_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (n : ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ n) true) := by
  induction n with
  | zero => simpa using hconst [true]
  | succ n ih =>
    have h := cpt_mul cpt_id ih
    have e : (fun x : List Bool =>
        List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool => List.replicate (x.length ^ (n + 1)) true) := by
      funext x
      rw [List.length_replicate, pow_succ, Nat.mul_comm]
    rw [← e]
    exact h

/-- The clock: `p (|x|)` copies of `true`, for a polynomial `p`. -/
theorem clock_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (p : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h := cpt_comp (cpt_pair hp hq) cpt_append
    have e : (fun x : List Bool => List.replicate (p.eval x.length) true ++
        List.replicate (q.eval x.length) true) =
        (fun x : List Bool => List.replicate ((p + q).eval x.length) true) := by
      funext x
      rw [Polynomial.eval_add, List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h := cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
    have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
      funext x
      rw [List.length_replicate, List.length_replicate, Polynomial.eval_monomial]
    rw [← e]
    exact h

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.Machines.ConstList
section
/-!
# A machine that erases its input and writes a fixed string

Helper module (proofs only, no statement may use it). One stack of bits, used for both input and
output. The single labelled statement pops one symbol; if there was one it loops, otherwise it
pushes the whole fixed string (last symbol first) and halts. On an input of length `n` it halts
after `n + 1` steps.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Push the symbols of a list one after the other, then halt. -/
def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

/-- The program: erase the input, then write `l`. -/
def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

/-- The machine. -/
def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

/-- Configurations of the machine. -/
abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a

/-- The constant function to a fixed binary string is computable in `n + 1` steps. -/
theorem constList_polyTime (l : List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => l)) :=
  ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.L055
section
/-- Polynomial clocks: writing `p (length of the input)` ones takes polynomial time. Sums by
pairing and appending, powers and coefficients by unary multiplication. -/
theorem PEqualNP.Library.L055 : ∀ p : Polynomial ℕ,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) :=
  fun p => PEqualNP.Library.Machines.clock_polyTime
    (fun l => PEqualNP.Library.Machines.constList_polyTime l) p
end

-- upstream PEqualNP.Library.Machines.NormalForm
section
/-!
# Helper module (proofs only): the witness length bound inside the verifier

This is a helper module: it holds proofs only, no new notions. Given a polynomial-time decider
`fR` for a set of pairs and a polynomial `p`, the function
`q ↦ decide (q.2.length ≤ p.eval q.1.length) && fR q` is polynomial-time computable.

A machine is only specified on well-formed inputs, so the construction works on raw lists over
`Bool ⊕ Bool`: decode the raw list into a pair, compute each of the two bits from a copy of the
raw list, and answer whether both bits are true. Restricting to well-formed inputs at the end
costs nothing.
-/

namespace PEqualNP.Library.Machines

open PEqualNP.Library

/-- Decoding a raw list over `Bool ⊕ Bool` into a pair of strings. -/
def nfDec (l : List (Bool ⊕ Bool)) : List Bool × List Bool :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

theorem nfDec_encodePair (q : List Bool × List Bool) : nfDec (encodePair q) = q := by
  obtain ⟨x, w⟩ := q
  have h1 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getLeft? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  have h2 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getLeft? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h3 : ∀ x : List Bool, (x.map (Sum.inl (β := Bool))).filterMap Sum.getRight? = [] := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact ih
  have h4 : ∀ x : List Bool, (x.map (Sum.inr (α := Bool))).filterMap Sum.getRight? = x := by
    intro x; induction x with
    | nil => rfl
    | cons a l ih => exact congrArg (a :: ·) ih
  simp only [nfDec, encodePair, List.filterMap_append, h1, h2, h3, h4, List.append_nil,
    List.nil_append]

/-- Decoding is polynomial-time computable. -/
theorem nfDec_polyTime :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) encodePair nfDec := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => (Sum.getLeft? s).map Sum.inl)
    (fun s : Bool ⊕ Bool => (Sum.getRight? s).map Sum.inr) ?_
  intro l
  simp only [nfDec, encodePair, List.map_filterMap]

/-- Restricting a machine on raw lists to the well-formed inputs. -/
theorem nf_restrict {β βΓ : Type} {eb : β → List βΓ} {F : List (Bool ⊕ Bool) → β}
    (h : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) eb F) :
    ComputableInPolyTime encodePair eb (fun q => F (encodePair q)) := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun (encodePair q)⟩⟩

/-- Two bits computed from the same raw list can be combined by conjunction. -/
theorem nf_and {A B : List (Bool ⊕ Bool) → Bool}
    (hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool A)
    (hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool B) :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => B l && A l) := by
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  have dup : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l)
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun l => (l, l)) := by
    refine twoPass_polyTime _ _ _ (fun s => some (Sum.inl s)) (fun s => some (Sum.inr s)) ?_
    intro l
    have e1 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inl (β := Bool ⊕ Bool) s)) = l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have e2 : ∀ l : List (Bool ⊕ Bool), l.filterMap
        (fun s => some (Sum.inr (α := Bool ⊕ Bool) s)) = l.map Sum.inr := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp only [Gen.gpair, e1, e2]
  have s1 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List (Bool ⊕ Bool) => Gen.gpair (p.1, p.2))
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (A p.1, p.2)) :=
    Gen.first_polyTime (C := Bool ⊕ Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool A cA
  have sw : ComputableInPolyTime
      (fun p : Bool × List (Bool ⊕ Bool) => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p => (p.2, [p.1])) := by
    refine twoPass_polyTime _ _ _
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
      (fun s : Bool ⊕ (Bool ⊕ Bool) => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
    rintro ⟨b, l⟩
    have h1 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun _ => none) (fun b => some (Sum.inl (β := Bool) b)) s) =
        l.map Sum.inl := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    have h2 : ∀ l : List (Bool ⊕ Bool), (l.map (Sum.inr (α := Bool))).filterMap
        (fun s : Bool ⊕ (Bool ⊕ Bool) =>
          Sum.elim (fun b => some (Sum.inr (α := Bool ⊕ Bool) b)) (fun _ => none) s) = [] := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp
    simp [Gen.gpair, Computability.encodeBool, h2]
    exact (h1 l).symm
  have s2 : ComputableInPolyTime
      (fun p : List (Bool ⊕ Bool) × List Bool => Gen.gpair (p.1, p.2))
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      (fun p => (B p.1, p.2)) :=
    Gen.first_polyTime (C := Bool) (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool B cB
  have cv : ComputableInPolyTime
      (fun p : Bool × List Bool => Gen.gpair (Computability.encodeBool p.1, p.2))
      encodePair (fun p => (([p.1], p.2) : List Bool × List Bool)) := by
    refine filterMap_polyTime _ _ _ (fun s => some s) ?_
    intro p
    simp only [List.filterMap_some]
    rfl
  have h := cpt_comp (cpt_comp (cpt_comp (cpt_comp (cpt_comp dup s1) sw) s2) cv)
    allTrue_polyTime
  have e : (fun l : List (Bool ⊕ Bool) => B l && A l) =
      (fun l : List (Bool ⊕ Bool) => ([B l] ++ [A l]).all id) := by
    funext l; simp
  rw [e]; exact h

/-- The verifier with the witness length bound built in: polynomial-time decidable whenever the
original verifier is. -/
theorem nf_decider (fR : List Bool × List Bool → Bool) (p : Polynomial ℕ)
    (cR : ComputableInPolyTime encodePair Computability.encodeBool fR) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun q : List Bool × List Bool => decide (q.2.length ≤ p.eval q.1.length) && fR q) := by
  have hA : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => fR (nfDec l)) := cpt_comp nfDec_polyTime cR
  have hB0 := cpt_comp (cpt_comp nfDec_polyTime (cpt_first (PEqualNP.Library.L055 p)))
    LenCmp.lenLE_polyTime
  have hB : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) := by
    have e : (fun l : List (Bool ⊕ Bool) =>
        decide ((nfDec l).2.length ≤ p.eval (nfDec l).1.length)) =
        (fun l : List (Bool ⊕ Bool) => decide ((nfDec l).2.length ≤
          (List.replicate (p.eval (nfDec l).1.length) true).length)) := by
      funext l; simp
    rw [e]; exact hB0
  have h := nf_restrict (nf_and hA hB)
  have e : (fun q : List Bool × List Bool =>
      decide (q.2.length ≤ p.eval q.1.length) && fR q) =
      (fun q : List Bool × List Bool =>
        decide ((nfDec (encodePair q)).2.length ≤ p.eval (nfDec (encodePair q)).1.length) &&
          fR (nfDec (encodePair q))) := by
    funext q; rw [nfDec_encodePair]
  rw [e]; exact h

end PEqualNP.Library.Machines
end

-- upstream PEqualNP.Library.L045
section
/-- NP verifiers in normal form: the witness length bound can be built into the relation. -/
theorem PEqualNP.Library.L045 : ∀ L ∈ PEqualNP.Library.NP, ∃ (R : Set (List Bool × List Bool)) (p : Polynomial ℕ), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair R ∧ (∀ x w : List Bool, (x, w) ∈ R → w.length ≤ p.eval x.length) ∧ ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, (x, w) ∈ R := by
  rintro L ⟨R, p, ⟨fR, hfR, cR⟩, hL⟩
  refine ⟨{q | q.2.length ≤ p.eval q.1.length ∧ q ∈ R}, p,
    ⟨fun q => decide (q.2.length ≤ p.eval q.1.length) && fR q, fun q => ?_,
      PEqualNP.Library.Machines.nf_decider fR p cR⟩, fun x w h => h.1, fun x => hL x⟩
  exact (and_congr decide_eq_true_iff.symm (hfR q)).trans Bool.and_eq_true_iff.symm
end
-- upstream PEqualNP.Library.Machines.Transducer
section

namespace PEqualNP.Library.Machines

open Turing

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

inductive TrK : Type
  | inp | tmp | out
  deriving DecidableEq

instance : Fintype TrK :=
  Fintype.ofList [.inp, .tmp, .out] (fun x => by cases x <;> simp)

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | .inp => Γ₀
  | .tmp => Q × Option Γ₀
  | .out => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push .out (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop .inp (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push .tmp (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push .tmp (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop .tmp (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := .inp
  k₁ := .out
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | .inp => l
  | .tmp => t
  | .out => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .inp l' = trSt l' t u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) .tmp t' = trSt l t' u := by
  funext k; cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) .out u' = trSt l t u' := by
  funext k; cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .inp l := by
  funext k; cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .out u := by
  funext k; cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) .tmp = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) .inp l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) .out (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))

end PEqualNP.Library.Machines
end

-- the bridge from the upstream NP to the campaign's (from campaign m2_np_down_closed)
section bridge
theorem NP_iff (L : Language Bool) : L ∈ PvsNP.NP ↔ L ∈ PEqualNP.Library.NP := by
  constructor
  · rintro ⟨V, p, hV, hL⟩
    exact ⟨{xw | V xw = true}, p, ⟨V, fun _ => Iff.rfl, hV⟩, hL⟩
  · rintro ⟨R, p, ⟨f, hf, hc⟩, hL⟩
    refine ⟨f, p, hc, fun x => (hL x).trans ?_⟩
    exact exists_congr fun w => and_congr_right fun _ => hf (x, w)
end bridge

/-- Two witnesses written as one string: each bit of the first is preceded by `true`, then one
`false`, then the second witness as it is. -/
def pairEnc : List Bool → List Bool → List Bool
  | [], w₂ => false :: w₂
  | b :: w₁, w₂ => true :: b :: pairEnc w₁ w₂

theorem pairEnc_length (w₁ w₂ : List Bool) :
    (pairEnc w₁ w₂).length = 2 * w₁.length + w₂.length + 1 := by
  induction w₁ with
  | nil => simp only [pairEnc, List.length_cons, List.length_nil]; omega
  | cons b w₁ ih => simp only [pairEnc, List.length_cons, ih]; omega

/-- The decoder keeping the first witness. State `(false, false)`: a tag is next; `(true, false)`:
a bit of the first witness is next; `(_, true)`: inside the second witness. -/
def decFst (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Option Bool :=
  if q.2 then (q, none)
  else if q.1 then ((false, false), some b)
  else if b then ((true, false), none)
  else ((false, true), none)

/-- The decoder keeping the second witness (same states as `decFst`). -/
def decSnd (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Option Bool :=
  if q.2 then (q, some b)
  else if q.1 then ((false, false), none)
  else if b then ((true, false), none)
  else ((false, true), none)

theorem decFst_tail (w : List Bool) :
    PEqualNP.Library.Machines.fstRun decFst (fun _ => none) (false, true) w = [] := by
  induction w with
  | nil => simp [PEqualNP.Library.Machines.fstRun]
  | cons b w ih => simp [PEqualNP.Library.Machines.fstRun, decFst, ih]

theorem decSnd_tail (w : List Bool) :
    PEqualNP.Library.Machines.fstRun decSnd (fun _ => none) (false, true) w = w := by
  induction w with
  | nil => simp [PEqualNP.Library.Machines.fstRun]
  | cons b w ih => simp [PEqualNP.Library.Machines.fstRun, decSnd, ih]

theorem decFst_pairEnc (w₁ w₂ : List Bool) :
    PEqualNP.Library.Machines.fstRun decFst (fun _ => none) (false, false) (pairEnc w₁ w₂) =
      w₁ := by
  induction w₁ with
  | nil => simp [pairEnc, PEqualNP.Library.Machines.fstRun, decFst, decFst_tail]
  | cons b w₁ ih => simp [pairEnc, PEqualNP.Library.Machines.fstRun, decFst, ih]

theorem decSnd_pairEnc (w₁ w₂ : List Bool) :
    PEqualNP.Library.Machines.fstRun decSnd (fun _ => none) (false, false) (pairEnc w₁ w₂) =
      w₂ := by
  induction w₁ with
  | nil => simp [pairEnc, PEqualNP.Library.Machines.fstRun, decSnd, decSnd_tail]
  | cons b w₁ ih => simp [pairEnc, PEqualNP.Library.Machines.fstRun, decSnd, ih]


open PEqualNP.Library
open PEqualNP.Library.Machines

/-- Select alternating positions; `true` keeps the next bit. -/
def strand : Bool → List Bool → List Bool
  | _, [] => []
  | true, b :: x => b :: strand false x
  | false, _ :: x => strand true x

/-- The parity state after scanning the input. -/
def parity : Bool → List Bool → Bool
  | q, [] => q
  | q, _ :: x => parity (!q) x

theorem strand_length_le (q : Bool) (x : List Bool) :
    (strand q x).length ≤ x.length := by
  induction x generalizing q with
  | nil => simp [strand]
  | cons b x ih =>
    cases q with
    | false => exact (ih true).trans (Nat.le_succ _)
    | true => exact Nat.succ_le_succ (ih false)

theorem strand_zip (u v : List Bool) (hlen : u.length = v.length) :
    strand true (List.zipWith (fun a b => [a, b]) u v).flatten = u ∧
    strand false (List.zipWith (fun a b => [a, b]) u v).flatten = v ∧
    parity true (List.zipWith (fun a b => [a, b]) u v).flatten = true := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simp [strand, parity]
    | cons b v => simp at hlen
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      have ht : u.length = v.length := Nat.succ.inj hlen
      obtain ⟨h₁, h₂, he⟩ := ih v ht
      simpa [strand, parity] using
        (show a :: strand true (List.zipWith (fun a b => [a, b]) u v).flatten = a :: u ∧
          b :: strand false (List.zipWith (fun a b => [a, b]) u v).flatten = b :: v ∧
          parity true (List.zipWith (fun a b => [a, b]) u v).flatten = true from
            ⟨congrArg (a :: ·) h₁, congrArg (b :: ·) h₂, he⟩)

theorem recover :
    ∀ x : List Bool, parity true x = true →
      (strand true x).length = (strand false x).length ∧
      x = (List.zipWith (fun a b => [a, b]) (strand true x) (strand false x)).flatten
  | [], _ => by simp [strand]
  | [a], h => by simp [parity] at h
  | a :: b :: x, h => by
    have ht : parity true x = true := h
    obtain ⟨hlen, hx⟩ := recover x ht
    constructor
    · change (strand true x).length + 1 = (strand false x).length + 1
      omega
    · change a :: b :: x =
        a :: b :: (List.zipWith (fun a b => [a, b]) (strand true x) (strand false x)).flatten
      exact congrArg (fun t => a :: b :: t) hx

/-- Select input positions and decode the relevant certificate in one finite pass. -/
def pickStep (g : Bool × Bool → Bool → (Bool × Bool) × Option Bool)
    (q : Bool × (Bool × Bool)) : Bool ⊕ Bool →
      (Bool × (Bool × Bool)) × Option (Bool ⊕ Bool)
  | Sum.inl b => ((!q.1, q.2), if q.1 then some (Sum.inl b) else none)
  | Sum.inr b => ((q.1, (g q.2 b).1), (g q.2 b).2.map Sum.inr)

theorem pick_inr (g : Bool × Bool → Bool → (Bool × Bool) × Option Bool)
    (k : Bool) (r : Bool × Bool) (w : List Bool) :
    fstRun (pickStep g) (fun _ => none) (k, r) (w.map Sum.inr) =
      (fstRun g (fun _ => none) r w).map Sum.inr := by
  induction w generalizing r with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, fstRun, pickStep]
    rw [ih, List.map_append]
    cases (g r b).2 <;> rfl

theorem pick_pair (g : Bool × Bool → Bool → (Bool × Bool) × Option Bool)
    (k : Bool) (r : Bool × Bool) (x w : List Bool) :
    fstRun (pickStep g) (fun _ => none) (k, r) (encodePair (x, w)) =
      encodePair (strand k x, fstRun g (fun _ => none) r w) := by
  induction x generalizing k with
  | nil =>
    change fstRun (pickStep g) (fun _ => none) (k, r) (w.map Sum.inr) =
      (fstRun g (fun _ => none) r w).map Sum.inr
    exact pick_inr g k r w
  | cons b x ih =>
    cases k with
    | false =>
      change fstRun (pickStep g) (fun _ => none) (true, r) (encodePair (x, w)) =
        encodePair (strand true x, fstRun g (fun _ => none) r w)
      exact ih true
    | true =>
      change Sum.inl b :: fstRun (pickStep g) (fun _ => none) (false, r)
          (encodePair (x, w)) =
        Sum.inl b :: encodePair (strand false x, fstRun g (fun _ => none) r w)
      exact congrArg (Sum.inl b :: ·) (ih false)

theorem cpt_picked (g : Bool × Bool → Bool → (Bool × Bool) × Option Bool)
    (k : Bool) {f : List Bool × List Bool → Bool}
    (hf : ComputableInPolyTime encodePair Computability.encodeBool f) :
    ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l) Computability.encodeBool
      (fun l => f (nfDec (fstRun (pickStep g) (fun _ => none)
        (k, (false, false)) l))) := by
  have hT : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l)
      (fun l : List (Bool ⊕ Bool) => l)
      (fstRun (pickStep g) (fun _ => none) (k, (false, false))) :=
    fst_polyTime _ _ _ (pickStep g) (fun _ => none) (k, (false, false)) (fun _ => rfl)
  exact cpt_comp (cpt_comp hT nfDec_polyTime) hf

def parityStep (q : Bool) : Bool ⊕ Bool → Bool × Option Bool
  | Sum.inl _ => (!q, none)
  | Sum.inr _ => (q, none)

def rawParity (q : Bool) (l : List (Bool ⊕ Bool)) : Bool :=
  l.foldl (fun q s => Sum.elim (fun _ => !q) (fun _ => q) s) q

theorem rawParity_run (q : Bool) (l : List (Bool ⊕ Bool)) :
    fstRun parityStep some q l = [rawParity q l] := by
  induction l generalizing q with
  | nil => rfl
  | cons s l ih =>
    cases s <;> simp [fstRun, parityStep, rawParity, ih]

theorem rawParity_pair (q : Bool) (x w : List Bool) :
    rawParity q (encodePair (x, w)) = parity q x := by
  have hw : ∀ q : Bool, rawParity q (w.map Sum.inr) = q := by
    induction w with
    | nil => intro q; rfl
    | cons b w ih => intro q; exact ih q
  induction x generalizing q with
  | nil =>
    change rawParity q (w.map Sum.inr) = q
    exact hw q
  | cons b x ih =>
    change rawParity (!q) (encodePair (x, w)) = parity (!q) x
    exact ih (!q)

/-- Check even input length and run the two normalized verifiers. -/
def shuffleV (f₁ f₂ : List Bool × List Bool → Bool)
    (q : List Bool × List Bool) : Bool :=
  parity true q.1 &&
    (f₂ (strand false q.1, fstRun decSnd (fun _ => none) (false, false) q.2) &&
     f₁ (strand true q.1, fstRun decFst (fun _ => none) (false, false) q.2))

theorem cpt_shuffleV {f₁ f₂ : List Bool × List Bool → Bool}
    (c₁ : ComputableInPolyTime encodePair Computability.encodeBool f₁)
    (c₂ : ComputableInPolyTime encodePair Computability.encodeBool f₂) :
    ComputableInPolyTime encodePair Computability.encodeBool (shuffleV f₁ f₂) := by
  have hE : ComputableInPolyTime (fun l : List (Bool ⊕ Bool) => l)
      Computability.encodeBool (rawParity true) :=
    fst_polyTime _ _ _ parityStep some true (fun l => (rawParity_run true l).symm)
  have h := nf_restrict
    (nf_and (nf_and (cpt_picked decFst true c₁) (cpt_picked decSnd false c₂)) hE)
  have hdec (q : List Bool × List Bool) : nfDec (PvsNP.encodePair q) = q :=
    nfDec_encodePair q
  have heq :
      (fun q : List Bool × List Bool =>
        rawParity true (encodePair q) &&
          (f₂ (nfDec (fstRun (pickStep decSnd) (fun _ => none)
            (false, (false, false)) (encodePair q))) &&
           f₁ (nfDec (fstRun (pickStep decFst) (fun _ => none)
            (true, (false, false)) (encodePair q))))) = shuffleV f₁ f₂ := by
    funext ⟨x, w⟩
    simp only [shuffleV, rawParity_pair, pick_pair, hdec]
  change ComputableInPolyTime encodePair Computability.encodeBool
    (fun q : List Bool × List Bool =>
      rawParity true (encodePair q) &&
        (f₂ (nfDec (fstRun (pickStep decSnd) (fun _ => none)
          (false, (false, false)) (encodePair q))) &&
         f₁ (nfDec (fstRun (pickStep decFst) (fun _ => none)
          (true, (false, false)) (encodePair q))))) at h
  rwa [heq] at h

theorem lib_pshuffle :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PEqualNP.Library.NP → L₂ ∈ PEqualNP.Library.NP →
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PEqualNP.Library.NP := by
  intro L₁ L₂ h₁ h₂
  obtain ⟨R₁, p₁, ⟨f₁, hf₁, c₁⟩, hs₁, hL₁⟩ := PEqualNP.Library.L045 L₁ h₁
  obtain ⟨R₂, p₂, ⟨f₂, hf₂, c₂⟩, hs₂, hL₂⟩ := PEqualNP.Library.L045 L₂ h₂
  refine ⟨{q | shuffleV f₁ f₂ q = true}, Polynomial.C 2 * p₁ + p₂ + 1,
    ⟨shuffleV f₁ f₂, fun _ => Iff.rfl, cpt_shuffleV c₁ c₂⟩, fun x => ?_⟩
  constructor
  · rintro ⟨u, v, hlen, rfl, hu, hv⟩
    obtain ⟨w₁, hw₁⟩ := (hL₁ u).1 hu
    obtain ⟨w₂, hw₂⟩ := (hL₂ v).1 hv
    obtain ⟨hleft, hright, heven⟩ := strand_zip u v hlen
    have hule : u.length ≤ (List.zipWith (fun a b => [a, b]) u v).flatten.length := by
      have h := strand_length_le true (List.zipWith (fun a b => [a, b]) u v).flatten
      rwa [hleft] at h
    have hvle : v.length ≤ (List.zipWith (fun a b => [a, b]) u v).flatten.length := by
      have h := strand_length_le false (List.zipWith (fun a b => [a, b]) u v).flatten
      rwa [hright] at h
    refine ⟨pairEnc w₁ w₂, ?_, ?_⟩
    · have b₁ := (hs₁ u w₁ hw₁).trans (eval_mono p₁ hule)
      have b₂ := (hs₂ v w₂ hw₂).trans (eval_mono p₂ hvle)
      rw [pairEnc_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_one]
      omega
    · show shuffleV f₁ f₂
        ((List.zipWith (fun a b => [a, b]) u v).flatten, pairEnc w₁ w₂) = true
      simp only [shuffleV, hleft, hright, heven, decFst_pairEnc, decSnd_pairEnc,
        (hf₁ (u, w₁)).1 hw₁, (hf₂ (v, w₂)).1 hw₂, Bool.and_self]
  · rintro ⟨w, _, hw⟩
    change shuffleV f₁ f₂ (x, w) = true at hw
    obtain ⟨heven, hbits⟩ := Bool.and_eq_true_iff.1 hw
    obtain ⟨hv, hu⟩ := Bool.and_eq_true_iff.1 hbits
    obtain ⟨hlen, hx⟩ := recover x heven
    exact ⟨strand true x, strand false x, hlen, hx,
      (hL₁ _).2 ⟨_, (hf₁ _).2 hu⟩, (hL₂ _).2 ⟨_, (hf₂ _).2 hv⟩⟩

end PvsNP.Units.tc_closure_pshuffle_np

theorem PvsNP.Units.tc_closure_pshuffle_np :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.NP := by
  intro L₁ L₂ h₁ h₂
  exact (PvsNP.Units.tc_closure_pshuffle_np.NP_iff _).2
    (PvsNP.Units.tc_closure_pshuffle_np.lib_pshuffle L₁ L₂
      ((PvsNP.Units.tc_closure_pshuffle_np.NP_iff L₁).1 h₁)
      ((PvsNP.Units.tc_closure_pshuffle_np.NP_iff L₂).1 h₂))
