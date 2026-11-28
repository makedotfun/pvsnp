import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_p_compl

set_option autoImplicit false

namespace PvsNP.Units.m2_z_length_cofinite_p

/-- The homomorphism sending every bit to `[true]`: flattening gives a
replicate of `true` of the same length as the input. -/
private def lenH : Bool → List Bool := fun _ => [true]

private theorem flatMap_lenH {x : List Bool} :
    x.flatMap lenH = List.replicate x.length true := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    show lenH b ++ xs.flatMap lenH = List.replicate (xs.length + 1) true
    rw [ih]
    rfl

end PvsNP.Units.m2_z_length_cofinite_p

open PvsNP.Units.m2_z_length_cofinite_p

theorem PvsNP.Units.m2_z_length_cofinite_p :
    ∀ A : Finset ℕ, ({x : List Bool | x.length ∉ A} : Language Bool) ∈ PvsNP.P := by
  intro A
  -- The finite language of replicates of `true` with lengths in `A`.
  have hFin : ({x : List Bool | x ∈ A.image (fun n => List.replicate n true)} :
      Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite _
  -- Its preimage under `lenH` is the lists whose length is in `A`.
  have hPre : ({x : List Bool | x.flatMap lenH ∈
      ({y : List Bool | y ∈ A.image (fun n => List.replicate n true)} : Language Bool)} :
      Language Bool) ∈ PvsNP.P :=
    (PvsNP.Units.m2_inv_hom_closed lenH _).1 hFin
  have hEq : ({x : List Bool | x.flatMap lenH ∈
        ({y : List Bool | y ∈ A.image (fun n => List.replicate n true)} : Language Bool)} :
        Language Bool)
      = ({x : List Bool | x.length ∈ A} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      rw [flatMap_lenH] at hx
      obtain ⟨n, hnA, hne⟩ := Finset.mem_image.mp hx
      have hlen : n = x.length := by
        have h := congrArg List.length hne
        simpa [List.length_replicate] using h
      rwa [hlen] at hnA
    · intro hx
      rw [flatMap_lenH]
      exact Finset.mem_image.mpr ⟨x.length, hx, rfl⟩
  rw [hEq] at hPre
  -- The target is the complement of that language.
  have hCompl := PvsNP.Units.m2_p_compl _ hPre
  have hTarget : ({x : List Bool | x.length ∉ A} : Language Bool)
      = ({x : List Bool | x.length ∈ A} : Language Bool)ᶜ := by
    ext x
    simp
  rw [hTarget]
  exact hCompl
