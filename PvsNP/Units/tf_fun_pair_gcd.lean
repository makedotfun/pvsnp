import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tr_rel_val_coprime
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_p_rotate_closed
import PvsNP.Units.m2_bool_combine_polytime

-- Adapted from `PvsNP.Units.tr_rel_val_coprime` (settled, commit
-- `08cf7a2`, 2026-11-27): the same Stein binary-GCD step, binary addition /
-- subtraction and `m2_iterate_polytime` assembly, but with a triple state
-- `pairB (pairB a b) c` where `c` is a unary counter of the common factors of
-- two stripped so far, so the step preserves the value
-- `2 ^ c.length * Nat.gcd a b` (the coprime step instead collapses the
-- both-even case to `(0, 0)`, which only preserves coprimality, not the gcd
-- itself). The final output is `c.map (fun _ => false) ++ binAdd a' b'`,
-- i.e. `Nat.bits (2 ^ c.length * (a' + b')) = Nat.bits (Nat.gcd m n)`.

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_gcd

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tr_rel_val_coprime

/-! ### Stein step on the triple state, and its length bound -/

/-- One Stein step on `pairB (pairB a b) c`: `c` counts the common factors of
    two stripped so far (as a unary list of `true`s). -/
def gcdStepG (s : List Bool) : List Bool :=
  if decide ((unpairB (unpairB s).1).1 = []) || decide ((unpairB (unpairB s).1).2 = []) then s
  else if decide ((unpairB (unpairB s).1).1.take 1 = [false]) && decide ((unpairB (unpairB s).1).2.take 1 = [false]) then pairB (pairB ((unpairB (unpairB s).1).1.tail) ((unpairB (unpairB s).1).2.tail)) (true :: (unpairB s).2)
  else if decide ((unpairB (unpairB s).1).1.take 1 = [false]) then pairB (pairB ((unpairB (unpairB s).1).1.tail) ((unpairB (unpairB s).1).2)) (unpairB s).2
  else if decide ((unpairB (unpairB s).1).2.take 1 = [false]) then pairB (pairB ((unpairB (unpairB s).1).1) ((unpairB (unpairB s).1).2.tail)) (unpairB s).2
  else if decide (val ((unpairB (unpairB s).1).1) ≤ val ((unpairB (unpairB s).1).2)) then pairB (pairB ((unpairB (unpairB s).1).1) ((binSub ((unpairB (unpairB s).1).2) ((unpairB (unpairB s).1).1)).tail)) (unpairB s).2
  else pairB (pairB ((binSub ((unpairB (unpairB s).1).1) ((unpairB (unpairB s).1).2)).tail) ((unpairB (unpairB s).1).2)) (unpairB s).2

theorem gcdStepG_len (s : List Bool) : (gcdStepG s).length ≤ s.length + 1 := by
  have hw := unpairB_weighted s
  have hw2 := unpairB_weighted (unpairB s).1
  unfold gcdStepG
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ ((unpairB (unpairB s).1).1).length := List.length_pos_of_ne_nil h0.1
    have hb : 1 ≤ ((unpairB (unpairB s).1).2).length := List.length_pos_of_ne_nil h0.2
    simp only [pairB_length, List.length_tail, List.length_cons]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ ((unpairB (unpairB s).1).1).length := List.length_pos_of_ne_nil h0.1
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have hb : 1 ≤ ((unpairB (unpairB s).1).2).length := List.length_pos_of_ne_nil h0.2
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have hb : 1 ≤ ((unpairB (unpairB s).1).2).length := List.length_pos_of_ne_nil h0.2
    have hsub := binSub_length_le ((unpairB (unpairB s).1).2) ((unpairB (unpairB s).1).1)
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ ((unpairB (unpairB s).1).1).length := List.length_pos_of_ne_nil h0.1
    have hsub := binSub_length_le ((unpairB (unpairB s).1).1) ((unpairB (unpairB s).1).2)
    simp only [pairB_length, List.length_tail]
    omega

theorem cpt_gcdStepG :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString gcdStepG := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).1).1) :=
    cpt_unpairB1_1 (cpt_unpairB1_1 cpt_id)
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).1).2) :=
    cpt_unpairB2_1 (cpt_unpairB1_1 cpt_id)
  have hC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hA0 := cpt_eq_fun _ _ hA (cpt_const [])
  have hB0 := cpt_eq_fun _ _ hB (cpt_const [])
  have hZero := PvsNP.Units.m2_bool_combine_polytime (· || ·) _ _ hA0 hB0
  have hAev := cpt_eq_fun _ _ (cpt_comp hA PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_const [false])
  have hBev := cpt_eq_fun _ _ (cpt_comp hB PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_const [false])
  have hBothEv := PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hAev hBev
  have hLe := cpt_binLe_fun _ _ hA hB
  have hBoth : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (unpairB (unpairB s).1).1.tail (unpairB (unpairB s).1).2.tail) (true :: (unpairB s).2)) :=
    cpt_pairB2 (cpt_pairB2 (cpt_comp hA cpt_tailStr) (cpt_comp hB cpt_tailStr)) (cpt_cons1 true hC)
  have hAeven : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (unpairB (unpairB s).1).1.tail (unpairB (unpairB s).1).2) (unpairB s).2) :=
    cpt_pairB2 (cpt_pairB2 (cpt_comp hA cpt_tailStr) hB) hC
  have hBeven : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (unpairB (unpairB s).1).1 (unpairB (unpairB s).1).2.tail) (unpairB s).2) :=
    cpt_pairB2 (cpt_pairB2 hA (cpt_comp hB cpt_tailStr)) hC
  have hBrSubB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (unpairB (unpairB s).1).1 (binSub (unpairB (unpairB s).1).2 (unpairB (unpairB s).1).1).tail) (unpairB s).2) :=
    cpt_pairB2 (cpt_pairB2 hA (cpt_comp (cpt_binSub_fun _ _ hB hA) cpt_tailStr)) hC
  have hBrSubA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (binSub (unpairB (unpairB s).1).1 (unpairB (unpairB s).1).2).tail (unpairB (unpairB s).1).2) (unpairB s).2) :=
    cpt_pairB2 (cpt_pairB2 (cpt_comp (cpt_binSub_fun _ _ hA hB) cpt_tailStr) hB) hC
  have h5 := PvsNP.Units.m2_ite_polytime _ _ _ hLe hBrSubB hBrSubA
  have h4 := PvsNP.Units.m2_ite_polytime _ _ _ hBev hBeven h5
  have h3 := PvsNP.Units.m2_ite_polytime _ _ _ hAev hAeven h4
  have h2 := PvsNP.Units.m2_ite_polytime _ _ _ hBothEv hBoth h3
  exact PvsNP.Units.m2_ite_polytime _ _ _ hZero cpt_id h2

/-! ### Correctness and convergence of the triple-state Stein step -/

theorem gcdStepG_canon (m n : ℕ) (c : List Bool) :
    ∃ m' n' c',
      gcdStepG (pairB (pairB (Nat.bits m) (Nat.bits n)) c) = pairB (pairB (Nat.bits m') (Nat.bits n')) c' ∧
      2 ^ c'.length * Nat.gcd m' n' = 2 ^ c.length * Nat.gcd m n ∧
      ((m = 0 ∨ n = 0) → (m' = 0 ∨ n' = 0)) ∧
      ((m = 0 ∨ n = 0) → c' = c) ∧
      (m ≠ 0 → n ≠ 0 → (Nat.bits m').length + (Nat.bits n').length < (Nat.bits m).length + (Nat.bits n).length) := by
  unfold gcdStepG
  simp only [unpairB_pairB]
  split_ifs with h0 h1 h2 h3 h4
  · refine ⟨m, n, c, rfl, rfl, id, fun _ => rfl, ?_⟩
    intro hm hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff] at h0
    rcases h0 with rfl | rfl <;> contradiction
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have hme := (bits_take1_eq_false h1.1).1
    have hne := (bits_take1_eq_false h1.2).1
    refine ⟨m / 2, n / 2, true :: c, by rw [bits_tail_even hme, bits_tail_even hne], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0,
      fun h => by rcases h with rfl | rfl <;> simp at h0, ?_⟩
    · have hm2 : m = 2 * (m / 2) := by omega
      have hn2 : n = 2 * (n / 2) := by omega
      have hg : Nat.gcd m n = 2 * Nat.gcd (m / 2) (n / 2) := by
        conv_lhs => rw [hm2, hn2]
        rw [Nat.gcd_mul_left]
      rw [List.length_cons, pow_succ, hg]
      ring
    · intro hm hn
      rw [← bits_tail_even hme, ← bits_tail_even hne, List.length_tail, List.length_tail]
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h1
    simp only [decide_eq_true_eq] at h2
    have hme := (bits_take1_eq_false h2).1
    have hno := bits_take1_ne_false h0.2 (h1 h2)
    refine ⟨m / 2, n, c, by rw [bits_tail_even hme], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, fun _ => rfl, ?_⟩
    · have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 (Nat.odd_iff.2 hno)
      have hm2 : m = 2 * (m / 2) := by omega
      have hg : Nat.gcd (m / 2) n = Nat.gcd m n := by
        conv_rhs => rw [hm2, Nat.Coprime.gcd_mul_left_cancel (m / 2) hcop]
      rw [hg]
    · intro hm _
      rw [← bits_tail_even hme, List.length_tail]
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3
    have hne := (bits_take1_eq_false h3).1
    have hmo := bits_take1_ne_false h0.1 h2
    refine ⟨m, n / 2, c, by rw [bits_tail_even hne], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, fun _ => rfl, ?_⟩
    · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hmo)
      have hn2 : n = 2 * (n / 2) := by omega
      have hg : Nat.gcd m (n / 2) = Nat.gcd m n := by
        conv_rhs => rw [hn2, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel (n / 2) hcop, Nat.gcd_comm]
      rw [hg]
    · intro _ hn
      rw [← bits_tail_even hne, List.length_tail]
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3 h4
    rw [val_bits, val_bits] at h4
    have hmo := bits_take1_ne_false h0.1 h2
    have hno := bits_take1_ne_false h0.2 h3
    have hde : (n - m) % 2 = 0 := by omega
    refine ⟨m, (n - m) / 2, c, by rw [binSub_eq h4, bits_tail_even hde], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, fun _ => rfl, ?_⟩
    · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hmo)
      have hsub_gcd : Nat.gcd m n = Nat.gcd m (n - m) := by
        have : n = (n - m) + m := by omega
        conv_lhs => rw [this, Nat.gcd_add_self_right]
      have hd2 : n - m = 2 * ((n - m) / 2) := by omega
      have hg : Nat.gcd m ((n - m) / 2) = Nat.gcd m n := by
        conv_rhs => rw [hsub_gcd, hd2, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel ((n - m) / 2) hcop, Nat.gcd_comm]
      rw [hg]
    · intro _ hn
      rw [← bits_tail_even hde, ← binSub_eq h4, List.length_tail]
      have hsub := binSub_length_le (Nat.bits n) (Nat.bits m)
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3 h4
    rw [val_bits, val_bits] at h4
    have hlt : n ≤ m := by omega
    have hmo := bits_take1_ne_false h0.1 h2
    have hno := bits_take1_ne_false h0.2 h3
    have hde : (m - n) % 2 = 0 := by omega
    refine ⟨(m - n) / 2, n, c, by rw [binSub_eq hlt, bits_tail_even hde], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, fun _ => rfl, ?_⟩
    · have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 (Nat.odd_iff.2 hno)
      have hsub_gcd : Nat.gcd m n = Nat.gcd (m - n) n := by
        have : m = (m - n) + n := by omega
        conv_lhs => rw [this, Nat.gcd_add_self_left]
      have hd2 : m - n = 2 * ((m - n) / 2) := by omega
      have hg : Nat.gcd ((m - n) / 2) n = Nat.gcd m n := by
        conv_rhs => rw [hsub_gcd, hd2, Nat.Coprime.gcd_mul_left_cancel ((m - n) / 2) hcop]
      rw [hg]
    · intro hm _
      rw [← bits_tail_even hde, ← binSub_eq hlt, List.length_tail]
      have hsub := binSub_length_le (Nat.bits m) (Nat.bits n)
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      omega

theorem gcdStepG_iter (t m n : ℕ) (c : List Bool) :
    ∃ m' n' c',
      gcdStepG^[t] (pairB (pairB (Nat.bits m) (Nat.bits n)) c) = pairB (pairB (Nat.bits m') (Nat.bits n')) c' ∧
      2 ^ c'.length * Nat.gcd m' n' = 2 ^ c.length * Nat.gcd m n ∧
      ((Nat.bits m).length + (Nat.bits n).length ≤ t → (m' = 0 ∨ n' = 0)) ∧
      ((m = 0 ∨ n = 0) → c' = c) := by
  induction t generalizing m n c with
  | zero =>
    refine ⟨m, n, c, rfl, rfl, fun h => ?_, fun _ => rfl⟩
    have h1 : (Nat.bits m).length = 0 := by omega
    exact Or.inl ((bits_eq_nil_iff m).1 (List.eq_nil_of_length_eq_zero h1))
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨m1, n1, c1, hstep, hgcd1, hzero1, hc1, hdec1⟩ := gcdStepG_canon m n c
    rw [hstep]
    obtain ⟨m2, n2, c2, hiter, hgcd2, hterm2, hc2⟩ := ih m1 n1 c1
    refine ⟨m2, n2, c2, hiter, hgcd2.trans hgcd1, fun hle => ?_, fun hmn => ?_⟩
    · by_cases hmn : m = 0 ∨ n = 0
      · have hmn1 : m1 = 0 ∨ n1 = 0 := hzero1 hmn
        have hstay : ∀ k a b cc, (a = 0 ∨ b = 0) →
            gcdStepG^[k] (pairB (pairB (Nat.bits a) (Nat.bits b)) cc) = pairB (pairB (Nat.bits a) (Nat.bits b)) cc := by
          intro k a b cc hab
          induction k with
          | zero => rfl
          | succ k ihk =>
            rw [Function.iterate_succ_apply]
            have hfix : gcdStepG (pairB (pairB (Nat.bits a) (Nat.bits b)) cc) = pairB (pairB (Nat.bits a) (Nat.bits b)) cc := by
              unfold gcdStepG
              simp only [unpairB_pairB]
              rcases hab with rfl | rfl <;> simp
            rw [hfix, ihk]
        rw [hstay t m1 n1 c1 hmn1] at hiter
        have hpair := congrArg unpairB hiter
        simp only [unpairB_pairB, Prod.mk.injEq] at hpair
        have hpair2 := congrArg unpairB hpair.1
        simp only [unpairB_pairB, Prod.mk.injEq] at hpair2
        rw [bits_eq_iff, bits_eq_iff] at hpair2
        rcases hmn1 with h1 | h2
        · exact Or.inl (hpair2.1.symm.trans h1)
        · exact Or.inr (hpair2.2.symm.trans h2)
      · have hm0 : m ≠ 0 := fun h => hmn (Or.inl h)
        have hn0 : n ≠ 0 := fun h => hmn (Or.inr h)
        have hlt := hdec1 hm0 hn0
        exact hterm2 (by omega)
    · have hmn1 : m1 = 0 ∨ n1 = 0 := hzero1 hmn
      rw [hc2 hmn1, hc1 hmn]

/-! ### Bits of a power-of-two multiple -/

theorem bits_two_pow_mul (k v : ℕ) (hv : v ≠ 0) :
    Nat.bits (2 ^ k * v) = List.replicate k false ++ Nat.bits v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hw : 2 ^ k * v ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hv
    have h2 : 2 ^ (k + 1) * v = 2 * (2 ^ k * v) := by rw [pow_succ]; ring
    have hbit : 2 * (2 ^ k * v) = Nat.bit false (2 ^ k * v) := by rw [Nat.bit_val]; simp
    rw [h2, hbit, Nat.bits_append_bit (2 ^ k * v) false (fun h => absurd h hw), ih,
      List.replicate_succ, List.cons_append]

/-! ### The gcd function and its polytime proof -/

theorem map_false_eq_replicate (l : List Bool) :
    l.map (fun _ => false) = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons _ _ ih => rw [List.map_cons, List.length_cons, List.replicate_succ, ih]

def gcdStr (s : List Bool) : List Bool :=
  let sf := gcdStepG^[((unpairB s).1 ++ (unpairB s).2).length]
    (pairB (pairB (canon (unpairB s).1) (canon (unpairB s).2)) [])
  (unpairB sf).2.map (fun _ => false) ++ binAdd (unpairB (unpairB sf).1).1 (unpairB (unpairB sf).1).2

def gcdFn (p : List Bool × List Bool) : List Bool := gcdStr (pairB p.1 p.2)

theorem cpt_gcdStr :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString gcdStr := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hInit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (pairB (canon (unpairB s).1) (canon (unpairB s).2)) []) :=
    cpt_pairB2 (cpt_pairB2 (cpt_binAdd_fun _ _ hA (cpt_const [])) (cpt_binAdd_fun _ _ hB (cpt_const []))) (cpt_const [])
  have hCnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1 ++ (unpairB s).2) :=
    cpt_app2 hA hB
  have hIter := PvsNP.Units.m2_iterate_polytime gcdStepG 1 cpt_gcdStepG gcdStepG_len
  have hRun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => gcdStepG^[((unpairB s).1 ++ (unpairB s).2).length]
        (pairB (pairB (canon (unpairB s).1) (canon (unpairB s).2)) [])) :=
    cpt_comp
      (f := fun s => (pairB (pairB (canon (unpairB s).1) (canon (unpairB s).2)) [], (unpairB s).1 ++ (unpairB s).2))
      (g := fun p : List Bool × List Bool => gcdStepG^[p.2.length] p.1)
      (PvsNP.Units.m2_pair_build_polytime _ _ hInit hCnt) hIter
  exact cpt_app2 (cpt_comp (cpt_unpairB2_1 hRun) cpt_zeroPad)
    (cpt_binAdd_fun _ _ (cpt_unpairB1_1 (cpt_unpairB1_1 hRun)) (cpt_unpairB2_1 (cpt_unpairB1_1 hRun)))

theorem cpt_gcdFn :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString gcdFn := by
  exact cpt_comp (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := gcdStr)
    cpt_pairB cpt_gcdStr

theorem gcdFn_spec (p : List Bool × List Bool) :
    gcdFn p = Nat.bits (Nat.gcd (val p.1) (val p.2)) := by
  simp only [gcdFn, gcdStr, unpairB_pairB, canon_eq]
  obtain ⟨m', n', c', hiter, hgcd, hterm, hc0⟩ :=
    gcdStepG_iter (p.1 ++ p.2).length (val p.1) (val p.2) []
  rw [hiter]
  simp only [unpairB_pairB]
  have hgcd : 2 ^ c'.length * Nat.gcd m' n' = Nat.gcd (val p.1) (val p.2) := by
    simpa using hgcd
  have hlen1 := bits_length_le_of_lt_two_pow (val_lt_two_pow p.1)
  have hlen2 := bits_length_le_of_lt_two_pow (val_lt_two_pow p.2)
  have hzero : m' = 0 ∨ n' = 0 := hterm (by simp only [List.length_append]; omega)
  have hsum : Nat.gcd m' n' = m' + n' := by
    rcases hzero with rfl | rfl <;> simp
  have hbin : binAdd (Nat.bits m') (Nat.bits n') = Nat.bits (m' + n') := by
    simp [binAdd, val_bits]
  have hmap : c'.map (fun _ => false) = List.replicate c'.length false :=
    map_false_eq_replicate c'
  by_cases hv : m' + n' = 0
  · have hm0 : m' = 0 := by omega
    have hn0 : n' = 0 := by omega
    have h0 : Nat.gcd (val p.1) (val p.2) = 0 := by
      rw [hm0, hn0] at hgcd
      simpa using hgcd.symm
    have hvals : val p.1 = 0 ∨ val p.2 = 0 := Or.inl ((Nat.gcd_eq_zero_iff).1 h0).1
    have hc' : c' = [] := hc0 hvals
    subst hc'
    simp only [List.map_nil, List.nil_append]
    rw [hm0, hn0, h0]
    rfl
  · rw [hmap, hbin, ← bits_two_pow_mul c'.length (m' + n') hv, ← hsum]
    exact congrArg Nat.bits hgcd

end PvsNP.Units.tf_fun_pair_gcd

/-- The greatest common divisor of two binary numerals takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_pair_gcd :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (Nat.gcd (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)) (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) := by
  have hfun : (fun p : List Bool × List Bool => Nat.bits (Nat.gcd (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)) (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) = PvsNP.Units.tf_fun_pair_gcd.gcdFn := by
    funext p
    exact (PvsNP.Units.tf_fun_pair_gcd.gcdFn_spec p).symm
  rw [hfun]
  exact PvsNP.Units.tf_fun_pair_gcd.cpt_gcdFn
