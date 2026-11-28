import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_unary_to_binary_polytime,
PvsNP.Units.m2_binary_le_polytime, and PvsNP.Units.m2_polytime_comp of
github.com/makedotfun/pvsnp (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_value_le_length

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := rfl

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : ComputableInPolyTime ea eb f) (heq : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

private def val (x : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)

private theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp only [val, List.map_cons, Nat.ofDigits_cons]

private theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      set b : Bool := decide ((m + 1) % 2 = 1)
      set q : ℕ := (m + 1) / 2
      have hbit : m + 1 = Nat.bit b q := by
        cases hb : b
        · have hmod : (m + 1) % 2 = 0 := by
            have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
            omega
          change m + 1 = 2 * q
          omega
        · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
          change m + 1 = 2 * q + 1
          omega
      have hcond : q = 0 → b = true := by
        intro hq
        have hmod : (m + 1) % 2 = 1 := by omega
        exact decide_eq_true hmod
      have hlt : q < m + 1 := by omega
      rw [hbit, Nat.bits_append_bit q b hcond, val_cons, ih q hlt]
      rw [← hbit]
      cases hb : b
      · have hmod : (m + 1) % 2 = 0 := by
          have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
          omega
        simp only [Bool.toNat_false]
        omega
      · have hmod : (m + 1) % 2 = 1 := of_decide_eq_true hb
        simp only [Bool.toNat_true]
        omega

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ p.2.length)) := by
  have hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => Nat.bits x.length) :=
    PvsNP.Units.m2_unary_to_binary_polytime
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, Nat.bits p.2.length)) := by
    rw [← encodePair_eq]
    refine cptE' (cpt_comp cpt_pairB (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB2 hu))) ?_
    rintro ⟨a, b⟩
    simp only [Function.comp_apply, unpairB_pairB]
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.1, Nat.bits p.2.length))
    (fun p : List Bool × List Bool =>
      decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    hmap PvsNP.Units.m2_binary_le_polytime
  have heq :
      ((fun p : List Bool × List Bool =>
          decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) ∘
        (fun p : List Bool × List Bool => (p.1, Nat.bits p.2.length))) =
      (fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ p.2.length)) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply]
    change decide (Nat.ofDigits (2 : ℕ) (a.map Bool.toNat) ≤ val (Nat.bits b.length)) = _
    rw [val_bits]
  rwa [heq] at hcomp

end PvsNP.Units.m2_tm_value_le_length

theorem PvsNP.Units.m2_tm_value_le_length :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ p.2.length)) :=
  PvsNP.Units.m2_tm_value_le_length.main
