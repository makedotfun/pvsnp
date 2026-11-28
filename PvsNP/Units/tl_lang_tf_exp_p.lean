import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_tf_exp_p

/-- Two-state automaton transition tracking `(seenFalse, seenTrueAfterFalse)`. -/
def trans (p : Bool × Bool) (b : Bool) : Bool × Bool :=
  (p.1 || !b, p.2 || (p.1 && b))

/-- Accept iff no `true` appeared after a `false`. -/
def accept (p : Bool × Bool) : Bool := !p.2

def bad : Bool → List Bool → Bool
  | _, [] => false
  | s, b :: rest => (s && b) || bad (s || !b) rest

theorem fold_snd (x : List Bool) (s t : Bool) :
    (x.foldl trans (s, t)).2 = (t || bad s x) := by
  induction x generalizing s t with
  | nil => simp [bad]
  | cons b rest ih =>
    show (rest.foldl trans (s || !b, t || (s && b))).2 = (t || bad s (b :: rest))
    rw [ih]
    simp [bad, Bool.or_assoc]

theorem bad_true_iff (x : List Bool) :
    bad true x = false ↔ ∃ b : ℕ, x = List.replicate b false := by
  induction x with
  | nil =>
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => rfl⟩
  | cons c rest ih =>
    cases c with
    | true =>
      constructor
      · intro h
        simp [bad] at h
      · rintro ⟨b, hb⟩
        cases b with
        | zero => cases hb
        | succ b' => simp [List.replicate_succ] at hb
    | false =>
      have e : bad true (false :: rest) = bad true rest := by simp [bad]
      rw [e]
      constructor
      · intro h
        obtain ⟨b, rfl⟩ := ih.mp h
        exact ⟨b + 1, rfl⟩
      · rintro ⟨b, hb⟩
        cases b with
        | zero => cases hb
        | succ b' =>
          simp only [List.replicate_succ, List.cons.injEq, true_and] at hb
          exact ih.mpr ⟨b', hb⟩

theorem bad_false_iff (x : List Bool) :
    bad false x = false ↔ ∃ a b : ℕ, x = List.replicate a true ++ List.replicate b false := by
  induction x with
  | nil =>
    exact ⟨fun _ => ⟨0, 0, rfl⟩, fun _ => rfl⟩
  | cons c rest ih =>
    cases c with
    | true =>
      have e : bad false (true :: rest) = bad false rest := by simp [bad]
      rw [e]
      constructor
      · intro h
        obtain ⟨a, b, rfl⟩ := ih.mp h
        exact ⟨a + 1, b, rfl⟩
      · rintro ⟨a, b, h⟩
        cases a with
        | zero =>
          cases b with
          | zero => cases h
          | succ b' => simp [List.replicate_succ] at h
        | succ a' =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          exact ih.mpr ⟨a', b, h⟩
    | false =>
      have e : bad false (false :: rest) = bad true rest := by simp [bad]
      rw [e, bad_true_iff]
      constructor
      · intro h
        obtain ⟨b, rfl⟩ := h
        exact ⟨0, b + 1, rfl⟩
      · rintro ⟨a, b, h⟩
        cases a with
        | zero =>
          cases b with
          | zero => cases h
          | succ b' =>
            simp only [List.replicate_zero, List.nil_append, List.replicate_succ,
              List.cons.injEq, true_and] at h
            exact ⟨b', h⟩
        | succ a' =>
          simp [List.replicate_succ] at h

theorem accept_iff (x : List Bool) :
    accept (x.foldl trans (false, false)) = true ↔
      ∃ a b : ℕ, x = List.replicate a true ++ List.replicate b false := by
  unfold accept
  rw [fold_snd]
  have h : (!(false || bad false x) = true) ↔ bad false x = false := by
    cases bad false x <;> simp
  exact h.trans (bad_false_iff x)

theorem ones_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count true) true) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ b => ((), if b then some true else none)) (fun _ => none)
    (fun _ x => List.replicate (x.count true) true)
    (fun _ => rfl)
    (fun _ b x => by cases b <;> simp [List.replicate_succ])
    ()

theorem zeros_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count false) true) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ b => ((), if b then none else some true)) (fun _ => none)
    (fun _ x => List.replicate (x.count false) true)
    (fun _ => rfl)
    (fun _ b x => by cases b <;> simp [List.replicate_succ])
    ()

theorem pow2Len_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (2 ^ x.length)) := by
  have hbits : ∀ n : ℕ, Nat.bits (2 ^ n) = List.replicate n false ++ [true] := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : 2 ^ n ≠ 0 := by positivity
      rw [Nat.pow_succ, mul_comm (2 ^ n) 2, Nat.bit0_bits _ hne, ih]
      simp [List.replicate_succ]
  have hfun : (fun x : List Bool => Nat.bits (2 ^ x.length))
      = (fun x : List Bool => List.replicate x.length false ++ [true]) := by
    funext x
    exact hbits x.length
  rw [hfun]
  exact PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some false)) (fun _ => some true)
    (fun _ x => List.replicate x.length false ++ [true])
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

theorem countFalseBits_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.count false)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (x.count false) true)
    (fun x : List Bool => Nat.bits x.length)
    zeros_polyTime PvsNP.Units.m2_unary_to_binary_polytime
  have he : ((fun x : List Bool => Nat.bits x.length) ∘
      (fun x : List Bool => List.replicate (x.count false) true))
      = (fun x : List Bool => Nat.bits (x.count false)) := by
    funext x
    simp
  rwa [he] at h

theorem pow2CountTrueBits_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (2 ^ (x.count true))) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (x.count true) true)
    (fun x : List Bool => Nat.bits (2 ^ x.length))
    ones_polyTime pow2Len_polyTime
  have he : ((fun x : List Bool => Nat.bits (2 ^ x.length)) ∘
      (fun x : List Bool => List.replicate (x.count true) true))
      = (fun x : List Bool => Nat.bits (2 ^ (x.count true))) := by
    funext x
    simp
  rwa [he] at h

theorem bits_inj {a b : ℕ} (h : Nat.bits a = Nat.bits b) : a = b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.even_or_odd' a with ⟨m, rfl | rfl⟩ <;> rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm <;> rcases Nat.eq_zero_or_pos k with rfl | hk
      · rfl
      · simp [Nat.bit0_bits k (by omega)] at h
      · simp [Nat.bit0_bits m (by omega)] at h
      · rw [Nat.bit0_bits m (by omega), Nat.bit0_bits k (by omega)] at h
        have := ih m (by omega) (List.cons.inj h).2
        omega
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h
      · rw [Nat.bit0_bits m (by omega), Nat.bit1_bits k] at h
        cases h
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h
      · rw [Nat.bit1_bits m, Nat.bit0_bits k (by omega)] at h
        cases h
    · rw [Nat.bit1_bits m, Nat.bit1_bits k] at h
      have := ih m (by omega) (List.cons.inj h).2
      omega

theorem bits_eq_iff (a b : ℕ) : Nat.bits a = Nat.bits b ↔ a = b :=
  ⟨bits_inj, fun h => by rw [h]⟩

theorem count_eq_in_p :
    ({x : List Bool | x.count false = 2 ^ (x.count true)} : Language Bool) ∈ PvsNP.P := by
  have hpair := PvsNP.Units.m2_pair_build_polytime
    (fun x : List Bool => Nat.bits (x.count false))
    (fun x : List Bool => Nat.bits (2 ^ (x.count true)))
    countFalseBits_polyTime pow2CountTrueBits_polyTime
  have heq := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeAnswer
    (fun x : List Bool => (Nat.bits (x.count false), Nat.bits (2 ^ (x.count true))))
    (fun p : List Bool × List Bool => decide (p.1 = p.2))
    hpair PvsNP.Units.m2_eq_polytime
  refine ⟨fun x => decide (Nat.bits (x.count false) = Nat.bits (2 ^ (x.count true))),
    heq, fun x => ?_⟩
  simp only [decide_eq_true_eq, bits_eq_iff]
  rfl

theorem count_rep_true (a b : ℕ) :
    (List.replicate a true ++ List.replicate b false).count true = a := by
  simp [List.count_append, List.count_replicate]

theorem count_rep_false (a b : ℕ) :
    (List.replicate a true ++ List.replicate b false).count false = b := by
  simp [List.count_append, List.count_replicate]

end PvsNP.Units.tl_lang_tf_exp_p

/-- The language `{1^n 0^(2^n) | n ∈ ℕ}` is in P: a two-state DFA checks that no `true`
follows a `false`, while a polytime decider computes `Nat.bits (x.count false)` and
`Nat.bits (2 ^ (x.count true))` and compares them for equality. -/
theorem PvsNP.Units.tl_lang_tf_exp_p :
    ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate (2 ^ n) false} :
      Language Bool) ∈ PvsNP.P := by
  have hdfa :
      ({x : List Bool | PvsNP.Units.tl_lang_tf_exp_p.accept
        (x.foldl PvsNP.Units.tl_lang_tf_exp_p.trans (false, false)) = true} :
        Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_dfa_in_p (Bool × Bool)
      PvsNP.Units.tl_lang_tf_exp_p.trans (false, false)
      PvsNP.Units.tl_lang_tf_exp_p.accept
  have hinter := PvsNP.Units.m2_p_inter _ _
    PvsNP.Units.tl_lang_tf_exp_p.count_eq_in_p hdfa
  have heq :
      (({x : List Bool | x.count false = 2 ^ (x.count true)} : Language Bool) ∩
        ({x : List Bool | PvsNP.Units.tl_lang_tf_exp_p.accept
          (x.foldl PvsNP.Units.tl_lang_tf_exp_p.trans (false, false)) = true} :
          Language Bool)) =
      ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate (2 ^ n) false} :
        Language Bool) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
      PvsNP.Units.tl_lang_tf_exp_p.accept_iff]
    constructor
    · rintro ⟨hcnt, a, b, hx⟩
      have hb : b = 2 ^ a := by
        rw [hx, PvsNP.Units.tl_lang_tf_exp_p.count_rep_false,
          PvsNP.Units.tl_lang_tf_exp_p.count_rep_true] at hcnt
        exact hcnt
      subst hb
      exact ⟨a, hx⟩
    · rintro ⟨n, rfl⟩
      refine ⟨?_, n, 2 ^ n, rfl⟩
      rw [PvsNP.Units.tl_lang_tf_exp_p.count_rep_false,
        PvsNP.Units.tl_lang_tf_exp_p.count_rep_true]
  rw [← heq]
  exact hinter
