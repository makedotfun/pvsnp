import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_y_binary_lengths_product

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_tri_p_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

theorem encodeString_eq :
    PvsNP.encodeString = (fun x : List Bool => x) := by
  funext x
  rfl

theorem ite_poly (c : List Bool → Bool) (a b : List Bool → List Bool)
    (hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer c)
    (ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString a)
    (hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString b) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if c x = true then a x else b x) := by
  have h := cpt_sel (f := fun x => if c x = true then [true] else []) (a := b) (b := a)
    (cpt_bitFlag hc) hb ha
  have e : (fun x : List Bool => if c x = true then a x else b x) =
      fun x => sel (if c x = true then [true] else []) (b x) (a x) := by
    funext x
    by_cases hx : c x = true <;> simp [sel, hx]
  rw [e]
  exact h

private theorem bl_cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def bN (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

def bd (l : List Bool) : ℕ := (l.headD false).toNat

theorem bN_eq (l : List Bool) : bN l = bd l + 2 * bN l.tail := by
  cases l with
  | nil => simp [bN, bd]
  | cons x l => simp [bN, bd, Nat.ofDigits_cons]

theorem bd_le (l : List Bool) : bd l ≤ 1 := by
  unfold bd
  cases l.headD false <;> simp

def blRes (res a b : List Bool) : List Bool :=
  sel (hd a) (sel (hd b) res []) (sel (hd b) [true] res)

theorem blRes_nil (res a b : List Bool) :
    blRes res a b = [] ↔ bd a < bd b ∨ (bd a = bd b ∧ res = []) := by
  rcases a with _ | ⟨x, a⟩ <;> rcases b with _ | ⟨y, b⟩ <;> (try cases x) <;> (try cases y) <;>
    simp [blRes, hd, bd, sel]

theorem blRes_len (res a b : List Bool) : (blRes res a b).length ≤ res.length + 1 := by
  unfold blRes sel
  split_ifs <;> simp

def lR (s : List Bool) : List Bool := (unpairB s).1
def lA (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def lB (s : List Bool) : List Bool := (unpairB (unpairB s).2).2

def blStep (s : List Bool) : List Bool :=
  pairB (blRes (lR s) (lA s) (lB s)) (pairB (lA s).tail (lB s).tail)

theorem blStep_eq (res a b : List Bool) :
    blStep (pairB res (pairB a b)) = pairB (blRes res a b) (pairB a.tail b.tail) := by
  simp only [blStep, lR, lA, lB, unpairB_pairB]

theorem bl_unpairB_len (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have h1 : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have h2 : ((s.dropWhile id).tail).length ≤ (s.dropWhile id).length := by
    rw [List.length_tail]; omega
  simp only [unpairB, List.length_take, List.length_drop]
  omega

theorem blStep_len (s : List Bool) : (blStep s).length ≤ s.length + 5 := by
  have a1 : 2 * (lR s).length + (unpairB s).2.length ≤ s.length := bl_unpairB_len s
  have a2 : 2 * (lA s).length + (lB s).length ≤ (unpairB s).2.length :=
    bl_unpairB_len (unpairB s).2
  have a3 := blRes_len (lR s) (lA s) (lB s)
  simp only [blStep, pairB_length, List.length_tail]
  omega

theorem blIter : ∀ (k : ℕ) (res a b : List Bool), a.length ≤ k → b.length ≤ k →
    ((unpairB (blStep^[k] (pairB res (pairB a b)))).1 = [] ↔
      bN a < bN b ∨ (bN a = bN b ∧ res = [])) := by
  intro k
  induction k with
  | zero =>
    intro res a b ha hb
    have ha' : a = [] := List.length_eq_zero_iff.1 (by omega)
    have hb' : b = [] := List.length_eq_zero_iff.1 (by omega)
    subst ha' hb'
    simp [unpairB_pairB, bN]
  | succ k ih =>
    intro res a b ha hb
    rw [Function.iterate_succ_apply, blStep_eq,
      ih _ _ _ (by rw [List.length_tail]; omega) (by rw [List.length_tail]; omega),
      blRes_nil, bN_eq a, bN_eq b]
    have h1 := bd_le a
    have h2 := bd_le b
    by_cases hR : res = []
    · simp only [hR, and_true]
      constructor <;> intro h <;> omega
    · simp only [hR, and_false, or_false]
      constructor <;> intro h <;> omega

def blF (q : List Bool × List Bool) : Bool :=
  (unpairB (blStep^[(q.1 ++ q.2).length] (pairB [] (pairB q.1 q.2)))).1.isEmpty

theorem blF_eq (a b : List Bool) : blF (a, b) = decide (bN a ≤ bN b) := by
  have h := blIter (a ++ b).length [] a b (by simp) (by simp)
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff]
  show (unpairB (blStep^[(a ++ b).length] (pairB [] (pairB a b)))).1.isEmpty = true ↔ _
  rw [List.isEmpty_iff, h]
  constructor
  · rintro (h | ⟨h, -⟩) <;> omega
  · intro h'
    rcases Nat.lt_or_ge (bN a) (bN b) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩

private theorem bl_false (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool))) (fun q => some q) false l =
      [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem bl_cpt_empty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
    (fun q => some q) true (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, bl_false, Computability.encodeBool])

theorem cpt_blF : ComputableInPolyTime PvsNP.encodePair Computability.encodeBool blF := by
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hres : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lR :=
    bl_cptp cpt_unpairB1 (fun _ => rfl)
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lA :=
    bl_cptp (cpt_comp hR cpt_unpairB1) (fun _ => rfl)
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lB :=
    bl_cptp (cpt_comp hR cpt_unpairB2) (fun _ => rfl)
  have hhA := cpt_comp hA cpt_hd
  have hhB := cpt_comp hB cpt_hd
  have hnew : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => blRes (lR s) (lA s) (lB s)) :=
    bl_cptp (cpt_sel hhA (cpt_sel hhB hres (cpt_const [])) (cpt_sel hhB (cpt_const [true]) hres))
      (fun _ => rfl)
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) blStep :=
    bl_cptp (cpt_pairB2 hnew (cpt_pairB2 (cpt_comp hA cpt_tail) (cpt_comp hB cpt_tail)))
      (fun _ => rfl)
  have hI := cpt_iterB blStep hg (fun _ => 5) 5 (fun _ => le_refl 5) blStep_len
    (fun _ => by omega)
  have hs0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun y : List Bool => pairB [] y) :=
    cpt_pairB2 (cpt_const []) cpt_id
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun y : List Bool => (unpairB y).1 ++ (unpairB y).2) :=
    cpt_app2 cpt_unpairB1 cpt_unpairB2
  have hit := cpt_comp (cpt_pairB2 hs0 hcnt) hI
  have hout := cpt_comp (cpt_comp hit cpt_unpairB1) bl_cpt_empty
  exact bl_cptp (cpt_comp cpt_pairB hout) (fun q => by
    obtain ⟨a, b⟩ := q
    simp only [unpairB_pairB, blF])

theorem binary_le_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have h := cpt_blF
  have e : blF = fun p : List Bool × List Bool =>
      decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) := by
    funext p
    obtain ⟨a, b⟩ := p
    exact blF_eq a b
  rw [e] at h
  exact h

def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

theorem val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val_nil]
  | cons b rest ih =>
    rw [val_cons, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : b = false ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      simp [val]
    · rw [Nat.bits_append_bit n b (fun hn => by cases b <;> simp_all), val_cons, ih, Nat.bit_val]
      cases b
      · simp
      · simp; ring

theorem length_bits_le (k : ℕ) : ∀ n : ℕ, n < 2 ^ k → (Nat.bits n).length ≤ k := by
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by omega
    subst h0
    simp
  | succ k ih =>
    intro n hn
    induction n using Nat.binaryRec with
    | zero => simp
    | bit b m _ =>
      by_cases h : b = false ∧ m = 0
      · rcases h with ⟨rfl, rfl⟩
        simp
      · rw [Nat.bits_append_bit m b (fun hm => by cases b <;> simp_all), List.length_cons]
        have hm : m < 2 ^ k := by
          rw [Nat.bit_val, pow_succ'] at hn
          cases b <;> simp at hn <;> omega
        have := ih m hm
        omega

def pow2List (k : ℕ) : List Bool :=
  List.replicate k false ++ [true]

theorem val_pow2List (k : ℕ) : val (pow2List k) = 2 ^ k := by
  induction k with
  | zero => simp [pow2List, val_cons, val_nil]
  | succ k ih =>
    simp only [pow2List, List.replicate_succ, List.cons_append, val_cons, Bool.toNat_false,
      Nat.zero_add] at ih ⊢
    rw [ih, pow_succ']

theorem pow2List_length (k : ℕ) : (pow2List k).length = k + 1 := by
  simp [pow2List]

theorem cpt_zeros :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length false) := by
  rw [encodeString_eq]
  refine filterMap_polyTime _ _ _ (fun _ : Bool => some false) ?_
  intro x
  induction x with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
    exact congrArg (List.cons false) ih

def sX (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def sBit (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def sR (s : List Bool) : List Bool := (unpairB s).2

def candR (s : List Bool) : List Bool :=
  PvsNP.Units.tf_fun_pair_mul.addB (sR s) (sBit s)

theorem val_candR (s : List Bool) : val (candR s) = val (sR s) + val (sBit s) :=
  PvsNP.Units.tf_fun_pair_mul.val_addB (sR s) (sBit s)

def sqCand (s : List Bool) : List Bool :=
  Nat.bits (val (candR s) * val (candR s))

def sqrtStep (s : List Bool) : List Bool :=
  pairB (pairB (sX s) (sBit s).tail)
    (if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s)

def sqrtMeasure (s : List Bool) : ℕ :=
  (sX s).length + 4

theorem sqrtMeasure_step (s : List Bool) :
    sqrtMeasure (sqrtStep s) ≤ sqrtMeasure s := by
  simp [sqrtMeasure, sqrtStep, sX, unpairB_pairB]

theorem sqrtMeasure_linear (s : List Bool) :
    sqrtMeasure s ≤ 4 * s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  unfold sqrtMeasure sX
  omega

theorem val_append_true (l : List Bool) : val (l ++ [true]) = val l + 2 ^ l.length := by
  induction l with
  | nil => simp [val_cons, val_nil]
  | cons b l ih =>
    simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ']
    ring

theorem stripLSB_length_le (r : List Bool) (k : ℕ) (h : val (PvsNP.Units.tf_fun_pair_mul.stripLSB r) < 2 ^ k) :
    (PvsNP.Units.tf_fun_pair_mul.stripLSB r).length ≤ k := by
  unfold PvsNP.Units.tf_fun_pair_mul.stripLSB at h ⊢
  rw [PvsNP.Units.tf_fun_pair_mul.dropLeadingFalse_eq] at h ⊢
  cases hdw : r.reverse.dropWhile (fun b => !b) with
  | nil => simp
  | cons b ts =>
    have hb : b = true := by
      have hp := List.head_dropWhile_not (p := fun b => !b) (l := r.reverse)
        (by rw [hdw]; simp)
      cases b <;> simp_all
    subst hb
    rw [List.reverse_cons, List.length_append, List.length_singleton, List.length_reverse]
    have hval : 2 ^ ts.length ≤ val (ts.reverse ++ [true]) := by
      rw [val_append_true, List.length_reverse]
      omega
    rw [hdw, List.reverse_cons] at h
    have hlt : 2 ^ ts.length < 2 ^ k := lt_of_le_of_lt hval h
    have hlt' : ts.length < k := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
    omega

theorem sqrtStep_len (s : List Bool) :
    (sqrtStep s).length ≤ s.length + sqrtMeasure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have hbt : (sBit s).tail.length ≤ (sBit s).length := by simp
  have hbound : 4 * (sX s).length + 2 * (sBit s).length + (sR s).length ≤ s.length := by
    unfold sX sBit sR; omega
  unfold sqrtStep sqrtMeasure
  simp only [pairB_length]
  by_cases hok : decide (val (sqCand s) ≤ val (sX s)) = true
  · simp only [hok, ↓reduceIte]
    simp only [decide_eq_true_eq] at hok
    have hval_sq : val (sqCand s) = val (candR s) * val (candR s) := val_bits _
    have hle_x : val (candR s) < 2 ^ (sX s).length := by
      have hxlt := val_lt_two_pow (sX s)
      have hsq : val (candR s) ≤ val (candR s) * val (candR s) := Nat.le_mul_self _
      omega
    have hclen : (candR s).length ≤ (sX s).length := by
      unfold candR PvsNP.Units.tf_fun_pair_mul.addB at hle_x ⊢
      exact stripLSB_length_le _ _ hle_x
    omega
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    omega

theorem toCpt {f : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f := hf

theorem fromCptPair {f : List Bool → List Bool × List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair f := by
  rw [← encodePair_eq, encodeString_eq]
  exact hf

theorem sqrtStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sqrtStep := by
  have hmul : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) :=
    PvsNP.Units.tf_fun_pair_mul
  have hle : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) :=
    binary_le_polytime
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sX :=
    cpt_unpairB1_1 cpt_unpairB1
  have hBit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sBit :=
    cpt_unpairB2_1 cpt_unpairB1
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sR :=
    cpt_unpairB2
  have hpairRB := fromCptPair (cpt_pair hR hBit)
  have hcand0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (sR s, sBit s))
      (fun p : List Bool × List Bool => PvsNP.Units.tf_fun_pair_mul.addB p.1 p.2)
      hpairRB PvsNP.Units.tf_fun_pair_mul.cpt_addB
  have hcand : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString candR := by
    have heq : ((fun p : List Bool × List Bool => PvsNP.Units.tf_fun_pair_mul.addB p.1 p.2) ∘
        (fun s => (sR s, sBit s))) = candR := by
      funext s; dsimp only [Function.comp_apply]; unfold candR; rfl
    rwa [heq] at hcand0
  have hpairCC := fromCptPair (cpt_pair (toCpt hcand) (toCpt hcand))
  have hsq0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (candR s, candR s))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
      hpairCC hmul
  have hsq : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sqCand := by
    have heq : ((fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) ∘
        (fun s => (candR s, candR s))) = sqCand := by
      funext s; dsimp only [Function.comp_apply]; unfold sqCand; rfl
    rwa [heq] at hsq0
  have hpairSX := fromCptPair (cpt_pair (toCpt hsq) hX)
  have hok0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun s => (sqCand s, sX s))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairSX hle
  have hok : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (sqCand s) ≤ val (sX s))) := by
    have heq : ((fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) ∘
        (fun s => (sqCand s, sX s))) = (fun s => decide (val (sqCand s) ≤ val (sX s))) := by
      funext s; dsimp only [Function.comp_apply]
    rwa [heq] at hok0
  have hrNext : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s) :=
    ite_poly (fun s => decide (val (sqCand s) ≤ val (sX s))) candR sR hok hcand hR
  have hstep0 := cpt_pairB2 (cpt_pairB2 hX (cpt_tail1 hBit)) (toCpt hrNext)
  have heq : (fun s => pairB (pairB (sX s) (sBit s).tail)
      (if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s)) = sqrtStep := by
    funext s; unfold sqrtStep; rfl
  rw [encodeString_eq, ← heq]
  exact hstep0

theorem val_addB (a b : List Bool) :
    val (PvsNP.Units.tf_fun_pair_mul.addB a b) = val a + val b :=
  PvsNP.Units.tf_fun_pair_mul.val_addB a b

theorem sqrtStep_iter (x : List Bool) :
    ∀ (k : ℕ) (r : List Bool),
      val r * val r ≤ val x →
      val x < (val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) →
      let res := (unpairB (sqrtStep^[k + 1] (pairB (pairB x (pow2List k)) r))).2
      val res * val res ≤ val x ∧ val x < (val res + 1) * (val res + 1) := by
  intro k
  induction k with
  | zero =>
    intro r hlo hhi
    simp only [Nat.zero_add, Function.iterate_one]
    have hs : sqrtStep (pairB (pairB x (pow2List 0)) r) =
        pairB (pairB x [])
          (if decide ((val r + 1) * (val r + 1) ≤ val x) = true then
            PvsNP.Units.tf_fun_pair_mul.addB r (pow2List 0) else r) := by
      unfold sqrtStep sqCand candR sX sBit sR
      simp only [unpairB_pairB, val_bits]
      rw [val_addB, val_pow2List, pow_zero]
      rfl
    rw [hs, unpairB_pairB]
    by_cases h : (val r + 1) * (val r + 1) ≤ val x
    · simp only [decide_eq_true h, ↓reduceIte]
      rw [val_addB, val_pow2List, pow_zero]
      exact ⟨h, by simpa using hhi⟩
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlo, by omega⟩
  | succ k ih =>
    intro r hlo hhi
    rw [Function.iterate_succ_apply]
    have htail : (pow2List (k + 1)).tail = pow2List k := rfl
    have hs : sqrtStep (pairB (pairB x (pow2List (k + 1))) r) =
        pairB (pairB x (pow2List k))
          (if decide ((val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) ≤ val x) = true then
            PvsNP.Units.tf_fun_pair_mul.addB r (pow2List (k + 1)) else r) := by
      unfold sqrtStep sqCand candR sX sBit sR
      simp only [unpairB_pairB, val_bits, htail]
      rw [val_addB, val_pow2List]
    rw [hs]
    by_cases h : (val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) ≤ val x
    · simp only [h, decide_true, ↓reduceIte]
      apply ih (PvsNP.Units.tf_fun_pair_mul.addB r (pow2List (k + 1)))
      · rw [val_addB, val_pow2List]; exact h
      · rw [val_addB, val_pow2List]
        have heq : val r + 2 ^ (k + 1) + 2 ^ (k + 1) = val r + 2 ^ (k + 1 + 1) := by
          rw [pow_succ]; ring
        rw [heq]
        exact hhi
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih r hlo (by omega)

def rFinal (x : List Bool) : List Bool :=
  (unpairB (sqrtStep^[(pow2List x.length).length]
    (pairB (pairB x (pow2List x.length)) []))).2

def eightXPlusOne (x : List Bool) : List Bool :=
  [true, false, false] ++ x

theorem val_eightXPlusOne (x : List Bool) : val (eightXPlusOne x) = 8 * val x + 1 := by
  simp only [eightXPlusOne, List.cons_append, List.nil_append, val_cons,
    Bool.toNat_true, Bool.toNat_false]
  omega

def triDecider (x : List Bool) : Bool :=
  decide (val (eightXPlusOne x) ≤
    val (Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)))))

theorem rFinal_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rFinal := by
  obtain ⟨cs⟩ := sqrtStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => sqrtStep^[p.2.length] p.1) := by
    rw [encodeString_eq]
    exact Iter.iter_polyTime_measure sqrtStep cs sqrtMeasure 4
      sqrtMeasure_step sqrtStep_len sqrtMeasure_linear
  have hpow2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pow2List x.length) :=
    cpt_app2 cpt_zeros (cpt_const [true])
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pairB (pairB x (pow2List x.length)) []) :=
    cpt_pairB2 (cpt_pairB2 cpt_id hpow2) (cpt_const [])
  exact cpt_unpairB2_1
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      _ _ (cpt_pair hinit hpow2) hiter)

theorem triDecider_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer triDecider := by
  have h8 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString eightXPlusOne :=
    cpt_app2 (cpt_const [true, false, false]) cpt_id
  have hr80 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      eightXPlusOne rFinal h8 rFinal_poly
  have hr8 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => rFinal (eightXPlusOne x)) := by
    have heq : rFinal ∘ eightXPlusOne = (fun x => rFinal (eightXPlusOne x)) := by
      funext x; dsimp only [Function.comp_apply]
    rwa [heq] at hr80
  have hpairRR : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x => (rFinal (eightXPlusOne x), rFinal (eightXPlusOne x))) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair hr8 hr8
  have hsq0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x => (rFinal (eightXPlusOne x), rFinal (eightXPlusOne x)))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
      hpairRR PvsNP.Units.tf_fun_pair_mul
  have hsqFinal : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)))) := by
    have heq : ((fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) ∘
        (fun x => (rFinal (eightXPlusOne x), rFinal (eightXPlusOne x)))) =
        (fun x => Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)))) := by
      funext x; dsimp only [Function.comp_apply]
    rwa [heq] at hsq0
  have hpairXS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x => (eightXPlusOne x,
        Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x))))) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair h8 hsqFinal
  have hdec0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x => (eightXPlusOne x,
      Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)))))
    (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
    hpairXS binary_le_polytime
  have heq : ((fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) ∘
      (fun x => (eightXPlusOne x,
        Nat.bits (val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)))))) = triDecider := by
    funext x; dsimp only [Function.comp_apply]; unfold triDecider; rfl
  rwa [heq] at hdec0

theorem main_proof :
    ({x : List Bool | ∃ k : ℕ, 2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k * (k + 1)} :
      Language Bool) ∈ PvsNP.P := by
  refine ⟨triDecider, triDecider_poly, ?_⟩
  intro x
  change (∃ k : ℕ, 2 * val x = k * (k + 1)) ↔ triDecider x = true
  have hhi0 : val (eightXPlusOne x) <
      (val [] + 2 ^ ((eightXPlusOne x).length + 1)) *
        (val [] + 2 ^ ((eightXPlusOne x).length + 1)) := by
    have hlt := val_lt_two_pow (eightXPlusOne x)
    have h1 : 2 ^ (eightXPlusOne x).length ≤ 2 ^ ((eightXPlusOne x).length + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ ((eightXPlusOne x).length + 1) ≤
        2 ^ ((eightXPlusOne x).length + 1) * 2 ^ ((eightXPlusOne x).length + 1) :=
      Nat.le_mul_self _
    simp only [val_nil, Nat.zero_add]
    omega
  have hres := sqrtStep_iter (eightXPlusOne x) (eightXPlusOne x).length []
    (by simp [val_nil]) hhi0
  have hrf_lo : val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)) ≤
      val (eightXPlusOne x) := by
    dsimp only [rFinal]
    rw [pow2List_length]
    exact hres.1
  have hrf_hi : val (eightXPlusOne x) <
      (val (rFinal (eightXPlusOne x)) + 1) * (val (rFinal (eightXPlusOne x)) + 1) := by
    dsimp only [rFinal]
    rw [pow2List_length]
    exact hres.2
  simp only [triDecider, decide_eq_true_eq, val_bits, val_eightXPlusOne]
  constructor
  · rintro ⟨k, hk⟩
    have hsq : (2 * k + 1) * (2 * k + 1) = 8 * val x + 1 := by
      have : k * (k + 1) = 2 * val x := hk.symm
      nlinarith
    have hkeq : 2 * k + 1 = val (rFinal (eightXPlusOne x)) := by
      have h1 : val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)) ≤
          (2 * k + 1) * (2 * k + 1) := by rw [val_eightXPlusOne] at hrf_lo; omega
      have h2 : (2 * k + 1) * (2 * k + 1) <
          (val (rFinal (eightXPlusOne x)) + 1) * (val (rFinal (eightXPlusOne x)) + 1) := by
        rw [val_eightXPlusOne] at hrf_hi; omega
      nlinarith
    rw [← hkeq]
    omega
  · intro hge
    have hsq : val (rFinal (eightXPlusOne x)) * val (rFinal (eightXPlusOne x)) = 8 * val x + 1 := by
      rw [val_eightXPlusOne] at hrf_lo
      omega
    have hodd : val (rFinal (eightXPlusOne x)) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (val (rFinal (eightXPlusOne x))) with h0 | h1
      · exfalso
        have hdiv2 : val (rFinal (eightXPlusOne x)) = 2 * (val (rFinal (eightXPlusOne x)) / 2) := by
          omega
        rw [hdiv2] at hsq
        have hlin : 2 * (2 * (val (rFinal (eightXPlusOne x)) / 2) *
            (val (rFinal (eightXPlusOne x)) / 2)) = 8 * val x + 1 := by linarith
        omega
      · exact h1
    refine ⟨val (rFinal (eightXPlusOne x)) / 2, ?_⟩
    have hdiv : val (rFinal (eightXPlusOne x)) = 2 * (val (rFinal (eightXPlusOne x)) / 2) + 1 := by
      omega
    rw [hdiv] at hsq
    nlinarith

end PvsNP.Units.tl_lang_val_tri_p_aux

theorem PvsNP.Units.tl_lang_val_tri_p : ({x : List Bool | ∃ k : ℕ, 2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k * (k + 1)} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_tri_p_aux.main_proof
