import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled campaign unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp
(Apache License 2.0), which carries the upstream PEqualNP library from
github.com/open-goat/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0). Nothing from that unit is copied; it is imported directly.
The binary-to-unary TM2, unary trial-division non-compositeness decider, and exponential-time
composition proof below are original work for unit m2_x_not_composite_in_exp.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_x_not_composite_in_exp

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-! ### Part 1: Unary non-compositeness decider in polynomial time -/

private abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

private theorem tail_iter_eq_drop {α : Type} (n : ℕ) (l : List α) :
    List.tail^[n] l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l with
    | nil => simp
    | cons a l => simp

private def dropLen (a b : List Bool) : List Bool :=
  List.tail^[b.length] a

private theorem dropLen_eq (a b : List Bool) : dropLen a b = a.drop b.length :=
  tail_iter_eq_drop b.length a

private theorem cpt_dropLen {u v : List Bool → List Bool} (hu : CPT u) (hv : CPT v) :
    CPT (fun s => dropLen (u s) (v s)) :=
  cptU (cpt_iterGrow cpt_tail 0 (fun l => by cases l <;> simp) hv hu) (fun _ => rfl)

-- Repeated subtraction to compute `u.length % a.length`
private def modStep (st : List Bool) : List Bool :=
  let a := (unpairB st).1
  let rem := (unpairB st).2
  let canSub := if decide (a.length ≤ rem.length) then [true] else []
  pairB a (sel canSub rem (dropLen rem a))

private theorem cpt_modStep : CPT modStep := by
  have hA := cpt_unpairB1
  have hR := cpt_unpairB2
  have hCan := cpt_le hA hR
  exact cptU (cpt_pairB2 hA (cpt_sel hCan hR (cpt_dropLen hR hA))) (fun _ => rfl)

private theorem modStep_len (st : List Bool) : (modStep st).length ≤ st.length + 2 := by
  unfold modStep
  dsimp only
  set a := (unpairB st).1
  set rem := (unpairB st).2
  have h0 : 2 * a.length + rem.length ≤ st.length := unpairB_length st
  have hdr : (dropLen rem a).length ≤ rem.length := by rw [dropLen_eq, List.length_drop]; omega
  by_cases h : a.length ≤ rem.length <;> simp [sel, h, pairB_length] <;> omega

private theorem modStep_fixed (a rem : List Bool) (hlt : rem.length < a.length) :
    ∀ m : ℕ, modStep^[m] (pairB a rem) = pairB a rem
  | 0 => rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply]
    have hnot : ¬ (a.length ≤ rem.length) := by omega
    have hs : modStep (pairB a rem) = pairB a rem := by simp [modStep, unpairB_pairB, sel, hnot]
    rw [hs, modStep_fixed a rem hlt m]

private theorem modStep_iter_mod (a : List Bool) (ha : 0 < a.length) :
    ∀ (m : ℕ) (rem : List Bool), rem.length ≤ m →
      (unpairB (modStep^[m] (pairB a rem))).2.length = rem.length % a.length
  | 0, rem, hm => by
    have h0 : rem.length = 0 := by omega
    simp [unpairB_pairB, h0]
  | m + 1, rem, hm => by
    by_cases hle : a.length ≤ rem.length
    · rw [Function.iterate_succ_apply]
      have hs : modStep (pairB a rem) = pairB a (rem.drop a.length) := by
        simp [modStep, unpairB_pairB, sel, hle, dropLen_eq]
      rw [hs, modStep_iter_mod a ha m (rem.drop a.length) (by rw [List.length_drop]; omega),
        List.length_drop, Nat.mod_eq_sub_mod hle]
    · have hlt : rem.length < a.length := by omega
      rw [modStep_fixed a rem hlt (m + 1), unpairB_pairB, Nat.mod_eq_of_lt hlt]

private def divFlag (a u : List Bool) : List Bool :=
  let rem := (unpairB (modStep^[u.length] (pairB a u))).2
  sel rem [true] []

private theorem cpt_divFlag {fa fu : List Bool → List Bool} (ha : CPT fa) (hu : CPT fu) :
    CPT (fun s => divFlag (fa s) (fu s)) := by
  have hIt := cpt_iterGrow cpt_modStep 2 modStep_len hu (cpt_pairB2 ha hu)
  exact cptU (cpt_sel (cpt_unpairB2_1 hIt) (cpt_const [true]) (cpt_const [])) (fun _ => rfl)

private theorem divFlag_ne_nil_iff (a u : List Bool) (ha : 0 < a.length) :
    divFlag a u ≠ [] ↔ a.length ∣ u.length := by
  unfold divFlag
  have hm := modStep_iter_mod a ha u.length u le_rfl
  set r := (unpairB (modStep^[u.length] (pairB a u))).2
  by_cases hr : r = []
  · simp only [sel, hr, ↓reduceIte, ne_eq, List.cons_ne_nil, not_false_eq_true, true_iff]
    rw [hr, List.length_nil] at hm
    exact Nat.dvd_of_mod_eq_zero hm.symm
  · simp only [sel, hr, ↓reduceIte, ne_eq, not_true_eq_false, false_iff]
    intro hdvd
    have h0 : r.length = 0 := by rw [hm, Nat.mod_eq_zero_of_dvd hdvd]
    exact hr (List.eq_nil_of_length_eq_zero h0)

-- Scan a = 2, 3, ..., u.length checking if `a < u.length ∧ a ∣ u.length`
private def compStep (st : List Bool) : List Bool :=
  let found := (unpairB st).1
  let r := (unpairB st).2
  let a := (unpairB r).1
  let u := (unpairB r).2
  let ltU := if decide ((true :: a).length ≤ u.length) then [true] else []
  let hit := sel ltU [] (sel (divFlag a u) [] [true])
  let found' := sel found hit [true]
  pairB found' (pairB (true :: a) u)

private theorem cpt_compStep : CPT compStep := by
  have hF := cpt_unpairB1
  have hR := cpt_unpairB2
  have hA := cpt_unpairB1_1 hR
  have hU := cpt_unpairB2_1 hR
  have hLt := cpt_le (cpt_cons1 true hA) hU
  have hHit := cpt_sel hLt (cpt_const []) (cpt_sel (cpt_divFlag hA hU) (cpt_const []) (cpt_const [true]))
  have hF' := cpt_sel hF hHit (cpt_const [true])
  exact cptU (cpt_pairB2 hF' (cpt_pairB2 (cpt_cons1 true hA) hU)) (fun _ => rfl)

private theorem compStep_len (st : List Bool) : (compStep st).length ≤ st.length + 8 := by
  unfold compStep
  dsimp only
  set found := (unpairB st).1
  set r := (unpairB st).2
  set a := (unpairB r).1
  set u := (unpairB r).2
  have h0 : 2 * found.length + r.length ≤ st.length := unpairB_length st
  have h1 : 2 * a.length + u.length ≤ r.length := unpairB_length r
  simp only [pairB_length, List.length_cons]
  have hf : (sel found (sel (if decide (a.length + 1 ≤ u.length) then [true] else []) []
      (sel (divFlag a u) [] [true])) [true]).length ≤ 1 := by
    by_cases h1 : found = [] <;> by_cases h2 : a.length + 1 ≤ u.length <;>
      by_cases h3 : divFlag a u = [] <;> simp [sel, h1, h2, h3]
  omega

private theorem compStep_iter (u : List Bool) :
    ∀ (m : ℕ) (a found : List Bool), 0 < a.length →
      ((unpairB (compStep^[m] (pairB found (pairB a u)))).1 ≠ [] ↔
        found ≠ [] ∨ ∃ j < m, a.length + j < u.length ∧ (a.length + j) ∣ u.length)
  | 0, a, found, _ => by simp [unpairB_pairB]
  | m + 1, a, found, ha => by
    rw [Function.iterate_succ_apply]
    set hit := sel (if decide ((true :: a).length ≤ u.length) then [true] else []) []
      (sel (divFlag a u) [] [true])
    have hs : compStep (pairB found (pairB a u)) =
        pairB (sel found hit [true]) (pairB (true :: a) u) := by
      simp [compStep, hit, unpairB_pairB]
    rw [hs, compStep_iter u m (true :: a) (sel found hit [true]) (by simp)]
    have hsel : sel found hit [true] ≠ [] ↔ found ≠ [] ∨ hit ≠ [] := by
      unfold sel; split <;> simp_all
    have hhit : hit ≠ [] ↔ a.length < u.length ∧ a.length ∣ u.length := by
      simp only [hit, List.length_cons]
      by_cases hlt : a.length + 1 ≤ u.length
      · have hlt' : a.length < u.length := by omega
        simp only [hlt, decide_true, ↓reduceIte, sel, List.cons_ne_nil, hlt', true_and]
        by_cases hd : divFlag a u = []
        · have hnd : ¬ (a.length ∣ u.length) := fun h => ((divFlag_ne_nil_iff a u ha).mpr h) hd
          simp [hd, hnd]
        · have hdd : a.length ∣ u.length := (divFlag_ne_nil_iff a u ha).mp hd
          simp [hd, hdd]
      · have hnlt : ¬ (a.length < u.length) := by omega
        simp [hlt, hnlt, sel]
    rw [hsel, hhit]
    simp only [List.length_cons]
    constructor
    · rintro ((hf | h0) | ⟨j, hj, hlt, hdvd⟩)
      · exact Or.inl hf
      · exact Or.inr ⟨0, by omega, by simpa using h0.1, by simpa using h0.2⟩
      · exact Or.inr ⟨j + 1, by omega, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1] using hdvd⟩
    · rintro (hf | ⟨j, hj, hlt, hdvd⟩)
      · exact Or.inl (Or.inl hf)
      · cases j with
        | zero => exact Or.inl (Or.inr ⟨by simpa using hlt, by simpa using hdvd⟩)
        | succ j' =>
          exact Or.inr ⟨j', by omega, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1] using hdvd⟩

private def notCompFlag (u : List Bool) : List Bool :=
  let comp := (unpairB (compStep^[u.length] (pairB [] (pairB [true, true] u)))).1
  sel comp [true] []

private theorem cpt_notCompFlag : CPT notCompFlag := by
  have hInit := cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const [true, true]) cpt_id)
  have hIt := cpt_iterGrow cpt_compStep 8 compStep_len cpt_id hInit
  exact cptU (cpt_sel (cpt_unpairB1_1 hIt) (cpt_const [true]) (cpt_const [])) (fun _ => rfl)

private def isNotCompUnary (u : List Bool) : Bool :=
  !(notCompFlag u).isEmpty

private theorem cpt_isNotCompUnary :
    ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer isNotCompUnary :=
  cptU (cpt_comp cpt_notCompFlag cpt_neU) (fun _ => rfl)

private theorem isNotCompUnary_iff (u : List Bool) :
    isNotCompUnary u = true ↔ ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = u.length := by
  simp only [isNotCompUnary, notCompFlag, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq]
  set c := (unpairB (compStep^[u.length] (pairB [] (pairB [true, true] u)))).1
  have hc : c ≠ [] ↔ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = u.length := by
    rw [compStep_iter u u.length [true, true] [] (by decide)]
    simp only [ne_eq, not_true_eq_false, false_or, List.length_cons, List.length_nil]
    constructor
    · rintro ⟨j, _, hlt, ⟨b, hb⟩⟩
      refine ⟨2 + j, b, by omega, ?_, hb.symm⟩
      by_contra hble
      have hb1 : b = 0 ∨ b = 1 := by omega
      rcases hb1 with rfl | rfl <;> omega
    · rintro ⟨a, b, ha, hb, hab⟩
      have hlt : a < u.length := by
        have : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb
        omega
      refine ⟨a - 2, by omega, by omega, ?_⟩
      have h2 : 2 + (a - 2) = a := by omega
      rw [h2]
      exact ⟨b, hab.symm⟩
  by_cases hcn : c = []
  · have hno : ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = u.length := fun h => (hc.mpr h) hcn
    exact ⟨fun _ => hno, fun _ => by simp [sel, hcn]⟩
  · have hyes : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = u.length := hc.mp hcn
    exact ⟨fun h => by simp [sel, hcn] at h, fun h => absurd hyes h⟩

/-! ### Part 2: Direct `FinTM2` binary-to-unary converter in `O(2^n)` steps -/

-- Stacks Fin 4: 0 = input x, 1 = reversed x (MSB first), 2 = tmp, 3 = output unary u
private def b2uTM : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ := fun _ => Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m := fun
    | ⟨0, _⟩ =>
      TM2.Stmt.pop 0 (fun _ o => o)
        (TM2.Stmt.branch Option.isSome
          (TM2.Stmt.push 1 (fun o => o.getD false) (TM2.Stmt.goto (fun _ => 0)))
          (TM2.Stmt.goto (fun _ => 1)))
    | ⟨1, _⟩ =>
      TM2.Stmt.pop 1 (fun _ o => o)
        (TM2.Stmt.branch Option.isSome
          (TM2.Stmt.branch (fun o => o.getD false)
            (TM2.Stmt.push 2 (fun _ => true) (TM2.Stmt.goto (fun _ => 2)))
            (TM2.Stmt.goto (fun _ => 2)))
          TM2.Stmt.halt)
    | ⟨2, _⟩ =>
      TM2.Stmt.pop 3 (fun _ o => o)
        (TM2.Stmt.branch Option.isSome
          (TM2.Stmt.push 2 (fun _ => true)
            (TM2.Stmt.push 2 (fun _ => true) (TM2.Stmt.goto (fun _ => 2))))
          (TM2.Stmt.goto (fun _ => 3)))
    | ⟨3, _⟩ =>
      TM2.Stmt.pop 2 (fun _ o => o)
        (TM2.Stmt.branch Option.isSome
          (TM2.Stmt.push 3 (fun _ => true) (TM2.Stmt.goto (fun _ => 3)))
          (TM2.Stmt.goto (fun _ => 1)))

private def mkStk (s0 s1 s2 s3 : List Bool) : Fin 4 → List Bool
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2
  | ⟨3, _⟩ => s3

private abbrev BStep := flip Option.bind (TM2.step b2uTM.m)

private theorem rep_append_cons (n : ℕ) (t : List Bool) :
    List.replicate n true ++ (true :: t) = true :: (List.replicate n true ++ t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem run_rev01 : ∀ (s0 s1 : List Bool) (v : Option Bool),
    BStep^[s0.length + 1] (some ⟨some (0 : Fin 4), v, mkStk s0 s1 [] []⟩) =
      some ⟨some (1 : Fin 4), none, mkStk [] (s0.reverse ++ s1) [] []⟩
  | [], s1, v => by
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, BStep, flip, Option.bind_some,
      TM2.step, b2uTM, TM2.stepAux, mkStk, List.head?_nil, Option.isSome_none, Bool.cond_false,
      List.reverse_nil, List.nil_append, Option.some.injEq]
    congr 1; funext k; fin_cases k <;> rfl
  | b :: s0, s1, v => by
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have h1 : BStep (some ⟨some (0 : Fin 4), v, mkStk (b :: s0) s1 [] []⟩) =
        some ⟨some (0 : Fin 4), some b, mkStk s0 (b :: s1) [] []⟩ := by
      simp only [BStep, flip, Option.bind_some, TM2.step, b2uTM, TM2.stepAux, mkStk,
        List.head?_cons, Option.isSome_some, Option.getD_some, Bool.cond_true, Option.some.injEq]
      congr 1; funext k; fin_cases k <;> rfl
    rw [h1, run_rev01 s0 (b :: s1) (some b)]
    simp [List.reverse_cons, List.append_assoc]

private theorem run_dbl32 : ∀ (s3 s1 s2 : List Bool) (v : Option Bool),
    BStep^[s3.length + 1] (some ⟨some (2 : Fin 4), v, mkStk [] s1 s2 s3⟩) =
      some ⟨some (3 : Fin 4), none, mkStk [] s1 (List.replicate (2 * s3.length) true ++ s2) []⟩
  | [], s1, s2, v => by
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, Nat.mul_zero,
      List.replicate_zero, List.nil_append, BStep, flip, Option.bind_some, TM2.step, b2uTM,
      TM2.stepAux, mkStk, List.head?_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
    congr 1; funext k; fin_cases k <;> rfl
  | b :: s3, s1, s2, v => by
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have h1 : BStep (some ⟨some (2 : Fin 4), v, mkStk [] s1 s2 (b :: s3)⟩) =
        some ⟨some (2 : Fin 4), some b, mkStk [] s1 (true :: true :: s2) s3⟩ := by
      simp only [BStep, flip, Option.bind_some, TM2.step, b2uTM, TM2.stepAux, mkStk,
        List.head?_cons, Option.isSome_some, Bool.cond_true, Option.some.injEq]
      congr 1; funext k; fin_cases k <;> rfl
    rw [h1, run_dbl32 s3 s1 (true :: true :: s2) (some b)]
    have hrep : List.replicate (2 * s3.length) true ++ (true :: true :: s2) =
        List.replicate (2 * (s3.length + 1)) true ++ s2 := by
      have : 2 * (s3.length + 1) = 2 * s3.length + 2 := by omega
      rw [this, List.replicate_add]
      simp [rep_append_cons]
    simp only [hrep]

private theorem run_move23 : ∀ (s2 s1 s3 : List Bool) (v : Option Bool),
    BStep^[s2.length + 1] (some ⟨some (3 : Fin 4), v, mkStk [] s1 s2 s3⟩) =
      some ⟨some (1 : Fin 4), none, mkStk [] s1 [] (List.replicate s2.length true ++ s3)⟩
  | [], s1, s3, v => by
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.replicate_zero,
      List.nil_append, BStep, flip, Option.bind_some, TM2.step, b2uTM, TM2.stepAux, mkStk,
      List.head?_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
    congr 1; funext k; fin_cases k <;> rfl
  | b :: s2, s1, s3, v => by
    rw [List.length_cons, Nat.succ_add, Function.iterate_succ_apply]
    have h1 : BStep (some ⟨some (3 : Fin 4), v, mkStk [] s1 (b :: s2) s3⟩) =
        some ⟨some (3 : Fin 4), some b, mkStk [] s1 s2 (true :: s3)⟩ := by
      simp only [BStep, flip, Option.bind_some, TM2.step, b2uTM, TM2.stepAux, mkStk,
        List.head?_cons, Option.isSome_some, Bool.cond_true, Option.some.injEq]
      congr 1; funext k; fin_cases k <;> rfl
    rw [h1, run_move23 s2 s1 (true :: s3) (some b)]
    simp [List.replicate_succ, rep_append_cons]

private theorem ofDigits_append_singleton (l : List Bool) (b : Bool) :
    Nat.ofDigits 2 ((l ++ [b]).map Bool.toNat) =
      Nat.ofDigits 2 (l.map Bool.toNat) + 2 ^ l.length * b.toNat := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.cons_append, List.map_cons, Nat.ofDigits_cons, ih, List.length_cons, Nat.pow_succ]
    ring

private theorem ofDigits_lt_two_pow : ∀ l : List Bool,
    Nat.ofDigits 2 (l.map Bool.toNat) < 2 ^ l.length
  | [] => by simp
  | b :: l => by
    have ih := ofDigits_lt_two_pow l
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

private theorem run_horner : ∀ (rev : List Bool) (acc : ℕ) (v : Option Bool),
    ∃ s, s + 3 * acc ≤ (3 * acc + 8) * 2 ^ rev.length ∧
      BStep^[s] (some ⟨some (1 : Fin 4), v, mkStk [] rev [] (List.replicate acc true)⟩) =
        some ⟨none, none,
          mkStk [] [] [] (List.replicate (acc * 2 ^ rev.length + Nat.ofDigits 2 (rev.reverse.map Bool.toNat)) true)⟩
  | [], acc, v => by
    refine ⟨1, by simp; omega, ?_⟩
    simp only [Function.iterate_one, List.length_nil, Nat.pow_zero, Nat.mul_one, List.reverse_nil,
      List.map_nil, Nat.ofDigits_nil, add_zero, BStep, flip, Option.bind_some, TM2.step, b2uTM,
      TM2.stepAux, mkStk, List.head?_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
    congr 1; funext k; fin_cases k <;> rfl
  | b :: rev, acc, v => by
    have h1 : BStep (some ⟨some (1 : Fin 4), v, mkStk [] (b :: rev) [] (List.replicate acc true)⟩) =
        some ⟨some (2 : Fin 4), some b, mkStk [] rev (if b then [true] else []) (List.replicate acc true)⟩ := by
      cases b <;>
        (simp only [BStep, flip, Option.bind_some, TM2.step, b2uTM, TM2.stepAux, mkStk,
          List.head?_cons, Option.isSome_some, Option.getD_some, Bool.cond_true, Bool.cond_false,
          ↓reduceIte, Bool.false_eq_true, Option.some.injEq];
         congr 1; funext k; fin_cases k <;> rfl)
    have h2 := run_dbl32 (List.replicate acc true) rev (if b then [true] else []) (some b)
    simp only [List.length_replicate] at h2
    have htmp : List.replicate (2 * acc) true ++ (if b then [true] else []) =
        List.replicate (2 * acc + b.toNat) true := by
      cases b <;> simp [List.replicate_add]
    rw [htmp] at h2
    have h3 := run_move23 (List.replicate (2 * acc + b.toNat) true) rev [] none
    simp only [List.length_replicate, List.append_nil] at h3
    obtain ⟨s', hs', hrest⟩ := run_horner rev (2 * acc + b.toNat) none
    refine ⟨s' + ((2 * acc + b.toNat + 1) + ((acc + 1) + 1)), ?_, ?_⟩
    · have hpow : 2 ^ (b :: rev).length = 2 * 2 ^ rev.length := by
        simp only [List.length_cons, Nat.pow_succ]; ring
      have hge1 : 1 ≤ 2 ^ rev.length := Nat.one_le_pow _ _ (by decide)
      have hb1 : b.toNat ≤ 1 := by cases b <;> decide
      have hmul : (3 * (2 * acc + b.toNat) + 8) * 2 ^ rev.length ≤
          (6 * acc + 11) * 2 ^ rev.length :=
        Nat.mul_le_mul_right _ (by omega)
      have hbig : (3 * acc + 8) * (2 * 2 ^ rev.length) =
          (6 * acc + 11) * 2 ^ rev.length + 5 * 2 ^ rev.length := by ring
      rw [hpow, hbig]
      omega
    · have hcomb : s' + ((2 * acc + b.toNat + 1) + ((acc + 1) + 1)) =
          (((s' + (2 * acc + b.toNat + 1)) + (acc + 1)) + 1) := by omega
      rw [hcomb, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_one, h1, h2, h3, hrest]
      have hval : (2 * acc + b.toNat) * 2 ^ rev.length + Nat.ofDigits 2 (rev.reverse.map Bool.toNat) =
          acc * 2 ^ (b :: rev).length + Nat.ofDigits 2 ((b :: rev).reverse.map Bool.toNat) := by
        simp only [List.reverse_cons, ofDigits_append_singleton, List.length_reverse,
          List.length_cons, Nat.pow_succ]
        ring
      rw [hval]

private theorem b2u_run (x : List Bool) :
    ∃ s ≤ 8 * 2 ^ x.length + x.length + 1,
      BStep^[s] (some (initList b2uTM x)) =
        some (haltList b2uTM (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)) := by
  have hinit : initList b2uTM x = ⟨some (0 : Fin 4), none, mkStk x [] [] []⟩ := by
    unfold initList
    congr 1; funext k; change Fin 4 at k
    fin_cases k
    · simp [b2uTM, mkStk]; rfl
    · simp [b2uTM, mkStk]
    · simp [b2uTM, mkStk]
    · simp [b2uTM, mkStk]
  have hhalt : haltList b2uTM (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true) =
      ⟨none, none, mkStk [] [] [] (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)⟩ := by
    unfold haltList
    congr 1; funext k; change Fin 4 at k
    fin_cases k
    · simp [b2uTM, mkStk]
    · simp [b2uTM, mkStk]
    · simp [b2uTM, mkStk]
    · simp [b2uTM, mkStk]; rfl
  obtain ⟨s', hs', hhor⟩ := run_horner x.reverse 0 none
  simp only [Nat.mul_zero, add_zero, zero_mul, zero_add, List.length_reverse,
    List.reverse_reverse, List.replicate_zero] at hs' hhor
  refine ⟨s' + (x.length + 1), by omega, ?_⟩
  rw [hinit, hhalt, Function.iterate_add_apply]
  have hr := run_rev01 x [] none
  simp only [List.append_nil] at hr
  rw [hr]
  exact hhor

/-! ### Part 3: Composition via `comp_run` and exponential time bound -/

private theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem poly_eval_le_const_pow (p : Polynomial ℕ) :
    ∃ C D : ℕ, ∀ m : ℕ, p.eval m ≤ C * (m + 1) ^ D := by
  refine ⟨p.eval 1, p.natDegree, fun m => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hle : i ≤ p.natDegree := by
    have := Finset.mem_range.mp hi; omega
  have h1 : m ^ i ≤ (m + 1) ^ p.natDegree :=
    le_trans (Nat.pow_le_pow_left (by omega) i) (Nat.pow_le_pow_right (by omega) hle)
  have h2 : p.coeff i * 1 ^ i = p.coeff i := by simp
  rw [h2]
  exact Nat.mul_le_mul_left _ h1

private theorem exp_dominates (A B D : ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, A * (2 ^ n) ^ D + B ≤ 2 ^ (n ^ k) + k := by
  let k := A * 2 ^ D + B + D + 3
  refine ⟨k, fun n => ?_⟩
  rcases n with _ | _ | n'
  · -- n = 0
    have h0 : 0 ^ k = 0 := Nat.zero_pow (by omega)
    simp only [Nat.pow_zero, Nat.one_pow, Nat.mul_one, h0]
    have : 1 ≤ 2 ^ D := Nat.one_le_pow _ _ (by decide)
    have : A ≤ A * 2 ^ D := Nat.le_mul_of_pos_right A (by omega)
    omega
  · -- n = 1
    simp [k]; omega
  · -- n = n' + 2 ≥ 2
    set n := n' + 2
    have hn2 : 2 ≤ n := by omega
    have hpow_add : A * (2 ^ n) ^ D + B ≤ (A + B + 1) * 2 ^ (D * n) := by
      have h1 : (2 ^ n) ^ D = 2 ^ (D * n) := by rw [← Nat.pow_mul, Nat.mul_comm]
      have h2 : 1 ≤ 2 ^ (D * n) := Nat.one_le_pow _ _ (by decide)
      have h3 : (A + B + 1) * 2 ^ (D * n) = A * 2 ^ (D * n) + B * 2 ^ (D * n) + 2 ^ (D * n) := by ring
      have h4 : B ≤ B * 2 ^ (D * n) := Nat.le_mul_of_pos_right B (by omega)
      rw [h1, h3]; omega
    have hAB : A + B + 1 ≤ 2 ^ (A + B + 1) := le_of_lt Nat.lt_two_pow_self
    have hle1 : (A + B + 1) * 2 ^ (D * n) ≤ 2 ^ (A + B + 1 + D * n) := by
      rw [Nat.pow_add]
      exact Nat.mul_le_mul_right _ hAB
    have hexp_le : A + B + 1 + D * n ≤ n ^ k := by
      have h2D : 1 ≤ 2 ^ D := Nat.one_le_pow _ _ (by decide)
      have hA : A ≤ A * 2 ^ D := Nat.le_mul_of_pos_right A (by omega)
      have hk1 : k - 1 ≥ A + B + D + 2 := by omega
      have h2k : A + B + D + 2 ≤ 2 ^ (k - 1) := le_trans hk1 (le_of_lt Nat.lt_two_pow_self)
      have hnk : 2 ^ (k - 1) ≤ n ^ (k - 1) := Nat.pow_le_pow_left hn2 (k - 1)
      have hmul : (A + B + D + 2) * n ≤ n ^ (k - 1) * n := Nat.mul_le_mul_right n (le_trans h2k hnk)
      have hpowk : n ^ (k - 1) * n = n ^ k := by
        have hksucc : (k - 1).succ = k := by omega
        rw [← Nat.pow_succ, hksucc]
      have hlin : A + B + 1 + D * n ≤ (A + B + D + 2) * n := by
        have : (A + B + D + 2) * n = (A + B + 2) * n + D * n := by ring
        have : A + B + 1 ≤ (A + B + 2) * n := by
          have : A + B + 2 ≤ (A + B + 2) * n := Nat.le_mul_of_pos_right _ (by omega)
          omega
        omega
      omega
    have hle2 : 2 ^ (A + B + 1 + D * n) ≤ 2 ^ (n ^ k) := Nat.pow_le_pow_right (by decide) hexp_le
    omega

theorem not_composite_in_exp_main :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool,
        x ∈ ({x : List Bool | ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
          Language Bool) ↔ f x = true) ∧
      ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  classical
  obtain ⟨c2⟩ := cpt_isNotCompUnary
  let φ : b2uTM.Γ b2uTM.k₁ → c2.tm.Γ c2.tm.k₀ := fun b => c2.inputAlphabet.invFun b
  let d : Option (c2.tm.Γ c2.tm.k₀) := some (c2.inputAlphabet.invFun false)
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by intro h; simp [d] at h
  obtain ⟨C, D, hCD⟩ := poly_eval_le_const_pow c2.time
  -- For input length n, s1 ≤ 8*2^n + n + 1, o1.length < 2^n, s2 ≤ C * (2^n)^D
  -- Total ≤ 8*2^n + n + 1 + (2*2^n + 2) + C * (2^n)^D ≤ (11 + C) * (2^n)^(D+1) + 3
  let T : ℕ → ℕ := fun n => (11 + C) * (2 ^ n) ^ (D + 1) + 3
  obtain ⟨k, hk⟩ := exp_dominates (11 + C) 3 (D + 1)
  let f : List Bool → Bool := fun x => isNotCompUnary (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)
  let M : TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f :=
    { tm := comp b2uTM c2.tm φ d
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := c2.outputAlphabet
      time := T
      outputsFun := fun x => by
        have h1ex := b2u_run x
        have r2 := c2.outputsFun (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)
        have hm1 : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := by
          change List.map id x = x
          exact List.map_id x
        have hφ : (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true).map φ =
            List.map c2.inputAlphabet.invFun
              (PvsNP.encodeString (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)) := rfl
        have hrun : ∃ n ≤ T x.length,
            (flip Option.bind (comp b2uTM c2.tm φ d).step)^[n]
              (some (initList (comp b2uTM c2.tm φ d) (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x)))) =
              Option.map (haltList (comp b2uTM c2.tm φ d))
                (some (List.map c2.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)))) := by
          obtain ⟨s1, hs1, hr1⟩ := h1ex
          have hr2 : (flip Option.bind (TM2.step c2.tm.m))^[r2.steps]
              (some (initList c2.tm ((List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true).map φ))) =
              some (haltList c2.tm (List.map c2.outputAlphabet.invFun (PvsNP.encodeAnswer (f x)))) := by
            rw [hφ]
            exact r2.evals_in_steps
          obtain ⟨n, hnle, _, hcomp⟩ := comp_run (M1 := b2uTM) (M2 := c2.tm) (φ := φ) d hd x
            (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)
            (List.map c2.outputAlphabet.invFun (PvsNP.encodeAnswer (f x))) s1 r2.steps hr1 hr2
          have hNlt : Nat.ofDigits 2 (x.map Bool.toNat) < 2 ^ x.length := ofDigits_lt_two_pow x
          have hs2 : r2.steps ≤ C * (2 ^ x.length) ^ D := by
            have h4 : (PvsNP.encodeString (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)).length =
                Nat.ofDigits 2 (x.map Bool.toNat) := List.length_replicate
            have h1 : r2.steps ≤ Polynomial.eval (Nat.ofDigits 2 (x.map Bool.toNat)) c2.time := by
              have hr := r2.steps_le_m
              simpa [h4] using hr
            have h2 := hCD (Nat.ofDigits 2 (x.map Bool.toNat))
            have h3 : (Nat.ofDigits 2 (x.map Bool.toNat) + 1) ^ D ≤ (2 ^ x.length) ^ D :=
              Nat.pow_le_pow_left (by omega) D
            exact le_trans h1 (le_trans h2 (Nat.mul_le_mul_left C h3))
          have hxn : x.length ≤ 2 ^ x.length := le_of_lt Nat.lt_two_pow_self
          have hpow1 : 2 ^ x.length ≤ (2 ^ x.length) ^ (D + 1) := by
            have hge1 : 1 ≤ (2 ^ x.length) ^ D := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
            rw [Nat.pow_succ]
            exact Nat.le_mul_of_pos_left _ (by omega)
          have hpowD : (2 ^ x.length) ^ D ≤ (2 ^ x.length) ^ (D + 1) := by
            have hge1 : 1 ≤ 2 ^ x.length := Nat.one_le_pow _ _ (by decide)
            rw [Nat.pow_succ]
            exact Nat.le_mul_of_pos_right _ (by omega)
          have hT : n ≤ T x.length := by
            have hnle' : n ≤ s1 + (2 * Nat.ofDigits 2 (x.map Bool.toNat) + 2) + r2.steps := by
              simpa [b2uTM] using hnle
            have hsum : (11 + C) * (2 ^ x.length) ^ (D + 1) =
                11 * (2 ^ x.length) ^ (D + 1) + C * (2 ^ x.length) ^ (D + 1) := by ring
            have hC : C * (2 ^ x.length) ^ D ≤ C * (2 ^ x.length) ^ (D + 1) :=
              Nat.mul_le_mul_left C hpowD
            dsimp only [T]
            omega
          refine ⟨n, hT, ?_⟩
          rw [Option.map_some]
          have hinit_eq : initList (comp b2uTM c2.tm φ d) (List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x)) =
              initList (comp b2uTM c2.tm φ d) x := by
            exact congrArg (initList (comp b2uTM c2.tm φ d)) hm1
          rw [hinit_eq]
          exact hcomp
        exact
          { steps := Classical.choose hrun
            steps_le_m := (Classical.choose_spec hrun).1
            evals_in_steps := (Classical.choose_spec hrun).2 } }
  refine ⟨k, f, M, fun x => ?_, fun n => hk n⟩
  show (¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ↔ f x = true
  have hf := isNotCompUnary_iff (List.replicate (Nat.ofDigits 2 (x.map Bool.toNat)) true)
  simpa [f] using hf.symm

end PvsNP.Units.m2_x_not_composite_in_exp

theorem PvsNP.Units.m2_x_not_composite_in_exp :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool,
        x ∈ ({x : List Bool | ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
          Language Bool) ↔ f x = true) ∧
      ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_x_not_composite_in_exp.not_composite_in_exp_main


