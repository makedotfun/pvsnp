import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.tf_fun_pair_add

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_binary_add_unary

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

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

end PvsNP.Units.m2_tm_binary_add_unary

theorem PvsNP.Units.m2_tm_binary_add_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + p.2.length)) := by
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, Nat.bits p.2.length)) :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x) (fun y : List Bool => Nat.bits y.length)
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
      PvsNP.Units.m2_unary_to_binary_polytime
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) ((Nat.bits p.2.length).map Bool.toNat))) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (f := fun p : List Bool × List Bool => (p.1, Nat.bits p.2.length))
      (g := fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      hmap PvsNP.Units.tf_fun_pair_add
  have heq : (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) ((Nat.bits p.2.length).map Bool.toNat))) =
      (fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + p.2.length)) := by
    funext p
    have hv : Nat.ofDigits (2 : ℕ) ((Nat.bits p.2.length).map Bool.toNat) = p.2.length :=
      PvsNP.Units.m2_tm_binary_add_unary.val_bits p.2.length
    rw [hv]
  rw [← heq]
  exact hcomp
