import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_unary_mul_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def val (x : List Bool) : ℕ := Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · rcases h with ⟨rfl, rfl⟩; simp [val]
    · have hcond : n = 0 → b = true := by intro hn; cases b <;> simp_all
      rw [Nat.bits_append_bit n b hcond, val_cons, ih, Nat.bit_val]
      omega

theorem bits_eq_iff (m n : ℕ) : Nat.bits m = Nat.bits n ↔ m = n := by
  constructor
  · intro h
    have := congrArg val h
    rwa [val_bits, val_bits] at this
  · intro h; rw [h]

def binMul (a b : List Bool) : List Bool := Nat.bits (val a * val b)

theorem cpt_binMul_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binMul (f s) (g s)) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_mul

theorem cpt_pairB_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => pairB (f s) (g s)) :=
  cpt_comp (g := fun p : List Bool × List Bool => pairB p.1 p.2)
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) cpt_pairB

theorem cpt_eq_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => decide (f s = g s)) :=
  cpt_comp (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.m2_eq_polytime

def nextSt : Bool × Bool → Bool → Bool × Bool
  | q, true => q
  | (false, false), false => (false, true)
  | (false, true), false => (true, false)
  | (true, false), false => (true, true)
  | (true, true), false => (true, true)

def runSt (q : Bool × Bool) : List Bool → Bool × Bool
  | [] => q
  | b :: l => runSt (nextSt q b) l

theorem runSt_append (q : Bool × Bool) (u v : List Bool) :
    runSt q (u ++ v) = runSt (runSt q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b tl ih => exact ih (nextSt q b)

theorem runSt_replicate_true (q : Bool × Bool) (n : ℕ) :
    runSt q (List.replicate n true) = q := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, runSt, nextSt, ih]

theorem runSt_sink (l : List Bool) : runSt (true, true) l = (true, true) := by
  induction l with
  | nil => rfl
  | cons b tl ih => cases b <;> simp [runSt, nextSt, ih]

def fmtD (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Option Bool := (nextSt q b, none)
def fmtFin (q : Bool × Bool) : Option Bool := if q = (true, false) then some true else none
def fmtCheck (x : List Bool) : List Bool := fstRun fmtD fmtFin (false, false) x

def segD (target : Bool × Bool) (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Option Bool :=
  (nextSt q b, if b ∧ q = target then some true else none)

def seg (target : Bool × Bool) (x : List Bool) : List Bool :=
  fstRun (segD target) (fun _ => none) (false, false) x

theorem cpt_fmtCheck : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString fmtCheck :=
  fst_polyTime _ _ _ fmtD fmtFin (false, false) (fun _ => rfl)

theorem cpt_seg (target : Bool × Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (seg target) :=
  fst_polyTime _ _ _ (segD target) (fun _ => none) (false, false) (fun _ => rfl)

theorem fstRun_fmtD (q : Bool × Bool) (l : List Bool) :
    fstRun fmtD fmtFin q l = if runSt q l = (true, false) then [true] else [] := by
  induction l generalizing q with
  | nil =>
    simp only [fstRun, fmtFin, runSt]
    split <;> simp_all
  | cons b tl ih =>
    simp only [fstRun, fmtD, runSt]
    exact ih (nextSt q b)

theorem fstRun_segD_append (target q : Bool × Bool) (u v : List Bool) :
    fstRun (segD target) (fun _ => none) q (u ++ v) =
      fstRun (segD target) (fun _ => none) q u ++ fstRun (segD target) (fun _ => none) (runSt q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b tl ih =>
    simp only [List.cons_append, fstRun, segD, runSt]
    split <;> simp [ih]

theorem fstRun_segD_rep_eq (target : Bool × Bool) (n : ℕ) :
    fstRun (segD target) (fun _ => none) target (List.replicate n true) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, fstRun, segD, nextSt, ih]

theorem fstRun_segD_rep_ne (target q : Bool × Bool) (hne : q ≠ target) (n : ℕ) :
    fstRun (segD target) (fun _ => none) q (List.replicate n true) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, fstRun, segD, nextSt, hne, ih]

theorem seg_of_form (a b c : ℕ) :
    let x := List.replicate a true ++ false :: List.replicate b true ++ false :: List.replicate c true
    fmtCheck x = [true] ∧
      seg (false, false) x = List.replicate a true ∧
      seg (false, true) x = List.replicate b true ∧
      seg (true, false) x = List.replicate c true := by
  intro x
  have hx : x = List.replicate a true ++ ([false] ++ (List.replicate b true ++ ([false] ++ List.replicate c true))) := by
    simp [x, List.append_assoc]
  rw [hx]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fmtCheck
    rw [fstRun_fmtD, runSt_append, runSt_replicate_true]
    simp [runSt, nextSt, runSt_append, runSt_replicate_true]
  · unfold seg
    rw [fstRun_segD_append, fstRun_segD_rep_eq, runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_append, fstRun_segD_rep_ne _ _ (by decide), runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_rep_ne _ _ (by decide)]
    simp
  · unfold seg
    rw [fstRun_segD_append, fstRun_segD_rep_ne _ _ (by decide), runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_append, fstRun_segD_rep_eq, runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_rep_ne _ _ (by decide)]
    simp
  · unfold seg
    rw [fstRun_segD_append, fstRun_segD_rep_ne _ _ (by decide), runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_append, fstRun_segD_rep_ne _ _ (by decide), runSt_replicate_true]
    simp only [List.cons_append, List.nil_append, fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [fstRun_segD_rep_eq]
    simp

theorem form_of_runSt_s2 (l : List Bool) (h : runSt (true, false) l = (true, false)) :
    l = List.replicate (fstRun (segD (true, false)) (fun _ => none) (true, false) l).length true := by
  induction l with
  | nil => rfl
  | cons b tl ih =>
    cases b with
    | false =>
      simp [runSt, nextSt, runSt_sink] at h
    | true =>
      simp only [runSt, nextSt] at h
      simp only [fstRun, segD, nextSt, and_self, ↓reduceIte, List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih h)

theorem form_of_runSt_s1 (l : List Bool) (h : runSt (false, true) l = (true, false)) :
    l = List.replicate (fstRun (segD (false, true)) (fun _ => none) (false, true) l).length true ++
      false :: List.replicate (fstRun (segD (true, false)) (fun _ => none) (false, true) l).length true := by
  induction l with
  | nil => simp [runSt] at h
  | cons b tl ih =>
    cases b with
    | false =>
      simp only [runSt, nextSt] at h
      have hB : fstRun (segD (false, true)) (fun _ => none) (true, false) tl = [] := by
        rw [form_of_runSt_s2 tl h, fstRun_segD_rep_ne _ _ (by decide)]
      simp only [fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte, hB, List.length_nil,
        List.replicate_zero, List.nil_append]
      exact congrArg (List.cons false) (form_of_runSt_s2 tl h)
    | true =>
      simp only [runSt, nextSt] at h
      have hne : (false, true) ≠ (true, false) := by decide
      simp only [fstRun, segD, nextSt, and_self, hne, and_false, ↓reduceIte, List.length_cons,
        List.replicate_succ, List.cons_append]
      exact congrArg (List.cons true) (ih h)

theorem form_of_runSt_s0 (l : List Bool) (h : runSt (false, false) l = (true, false)) :
    l = List.replicate (seg (false, false) l).length true ++
      false :: List.replicate (seg (false, true) l).length true ++
      false :: List.replicate (seg (true, false) l).length true := by
  unfold seg
  induction l with
  | nil => simp [runSt] at h
  | cons b tl ih =>
    cases b with
    | false =>
      simp only [runSt, nextSt] at h
      have htl := form_of_runSt_s1 tl h
      have hA : fstRun (segD (false, false)) (fun _ => none) (false, true) tl = [] := by
        rw [htl, fstRun_segD_append, fstRun_segD_rep_ne _ _ (by decide), runSt_replicate_true]
        simp only [fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte, List.nil_append]
        rw [fstRun_segD_rep_ne _ _ (by decide)]
        simp
      simp only [fstRun, segD, nextSt, Bool.false_eq_true, false_and, ↓reduceIte, hA,
        List.length_nil, List.replicate_zero, List.nil_append]
      exact congrArg (List.cons false) htl
    | true =>
      simp only [runSt, nextSt] at h
      have hne1 : (false, false) ≠ (false, true) := by decide
      have hne2 : (false, false) ≠ (true, false) := by decide
      simp only [fstRun, segD, nextSt, and_self, hne1, hne2, and_false, ↓reduceIte, List.length_cons,
        List.replicate_succ, List.cons_append]
      exact congrArg (List.cons true) (ih h)

def decMul (x : List Bool) : Bool :=
  decide (pairB (fmtCheck x) (binMul (Nat.bits (seg (false, false) x).length) (Nat.bits (seg (false, true) x).length)) =
    pairB [true] (Nat.bits (seg (true, false) x).length))

theorem cpt_decMul : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decMul := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => Nat.bits (seg (false, false) x).length) :=
    cpt_comp (g := fun l : List Bool => Nat.bits l.length) (cpt_seg (false, false))
      PvsNP.Units.m2_unary_to_binary_polytime
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => Nat.bits (seg (false, true) x).length) :=
    cpt_comp (g := fun l : List Bool => Nat.bits l.length) (cpt_seg (false, true))
      PvsNP.Units.m2_unary_to_binary_polytime
  have hC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => Nat.bits (seg (true, false) x).length) :=
    cpt_comp (g := fun l : List Bool => Nat.bits l.length) (cpt_seg (true, false))
      PvsNP.Units.m2_unary_to_binary_polytime
  have hL := cpt_pairB_fun _ _ cpt_fmtCheck (cpt_binMul_fun _ _ hA hB)
  have hR := cpt_pairB_fun _ _ (cpt_const [true]) hC
  exact cpt_eq_fun _ _ hL hR

theorem pairB_eq_iff (a b c d : List Bool) : pairB a b = pairB c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h' := congrArg unpairB h
    simp only [unpairB_pairB, Prod.mk.injEq] at h'
    exact h'
  · rintro ⟨rfl, rfl⟩; rfl

end PvsNP.Units.tl_lang_unary_mul_p

theorem PvsNP.Units.tl_lang_unary_mul_p :
    ({x : List Bool | ∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++ false :: List.replicate (a * b) true} : Language Bool) ∈ PvsNP.P := by
  refine ⟨PvsNP.Units.tl_lang_unary_mul_p.decMul, PvsNP.Units.tl_lang_unary_mul_p.cpt_decMul, fun x => ?_⟩
  change (∃ a b : ℕ, x = List.replicate a true ++ false :: List.replicate b true ++ false :: List.replicate (a * b) true) ↔
    PvsNP.Units.tl_lang_unary_mul_p.decMul x = true
  simp only [PvsNP.Units.tl_lang_unary_mul_p.decMul, decide_eq_true_eq,
    PvsNP.Units.tl_lang_unary_mul_p.pairB_eq_iff, PvsNP.Units.tl_lang_unary_mul_p.binMul,
    PvsNP.Units.tl_lang_unary_mul_p.val_bits, PvsNP.Units.tl_lang_unary_mul_p.bits_eq_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    obtain ⟨hf, hA, hB, hC⟩ := PvsNP.Units.tl_lang_unary_mul_p.seg_of_form a b (a * b)
    rw [hf, hA, hB, hC]
    simp
  · rintro ⟨hf, hmul⟩
    have hrun : PvsNP.Units.tl_lang_unary_mul_p.runSt (false, false) x = (true, false) := by
      unfold PvsNP.Units.tl_lang_unary_mul_p.fmtCheck at hf
      rw [PvsNP.Units.tl_lang_unary_mul_p.fstRun_fmtD] at hf
      split at hf
      · assumption
      · simp at hf
    refine ⟨(PvsNP.Units.tl_lang_unary_mul_p.seg (false, false) x).length,
      (PvsNP.Units.tl_lang_unary_mul_p.seg (false, true) x).length, ?_⟩
    rw [hmul]
    exact PvsNP.Units.tl_lang_unary_mul_p.form_of_runSt_s0 x hrun
