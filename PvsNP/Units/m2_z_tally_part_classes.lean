import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np

/-- The all-true members of a language in P (or NP) form a language in P
(or NP). The all-true lists are the preimage of the finite language `{[]}`
(settled unit `m2_p_finite`) under `h true = []`, `h false = [false]`
(settled unit `m2_inv_hom_closed`), hence in P and so in NP (settled unit
`m2_p_subset_np`); intersect with `L` by the settled units `m2_p_inter`
and `m2_np_inter`. -/
theorem PvsNP.Units.m2_z_tally_part_classes :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | x ∈ L ∧ ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.NP → ({x : List Bool | x ∈ L ∧ ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.NP) := by
  intro L
  have hE : ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite {[]}
  have hpre := (PvsNP.Units.m2_inv_hom_closed (fun b => if b then [] else [false])
    ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool)).1 hE
  have hflat : ∀ x : List Bool, (∀ b ∈ x, b = true) ↔
      x.flatMap (fun b => if b then [] else [false]) = [] := by
    intro x
    induction x with
    | nil => simp
    | cons a x ih =>
      simp only [List.flatMap_cons, List.append_eq_nil_iff, List.forall_mem_cons]
      rw [ih]
      constructor
      · rintro ⟨rfl, hx⟩
        refine ⟨?_, hx⟩
        simp
      · rintro ⟨ha, hx⟩
        refine ⟨?_, hx⟩
        cases a with
        | true => rfl
        | false => simp at ha
  have hT : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.P := by
    convert hpre using 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_singleton]
    exact hflat x
  have hTNP : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np hT
  have hS : ({x : List Bool | x ∈ L ∧ ∀ b ∈ x, b = true} : Language Bool)
      = L ⊓ ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2⟩
  constructor
  · intro hL
    rw [hS]
    exact PvsNP.Units.m2_p_inter L _ hL hT
  · intro hL
    rw [hS]
    exact PvsNP.Units.m2_np_inter L _ hL hTNP
