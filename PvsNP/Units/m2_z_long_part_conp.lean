import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_conp_inter

namespace PvsNP.Units.m2_z_long_part_conp

/-- All binary lists of length at most `m`, built by recursion. -/
def shortLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | m + 1 => shortLists m ∪ (shortLists m).image (true :: ·) ∪ (shortLists m).image (false :: ·)

theorem mem_shortLists : ∀ (m : ℕ) (x : List Bool), x ∈ shortLists m ↔ x.length ≤ m := by
  intro m
  induction m with
  | zero =>
    intro x
    simp only [shortLists, Finset.mem_singleton]
    constructor
    · intro hx
      rw [hx]
      simp
    · intro hx
      have : x.length = 0 := Nat.eq_zero_of_le_zero hx
      exact List.length_eq_zero_iff.mp this
  | succ m ih =>
    intro x
    simp only [shortLists, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hx
      rcases hx with (hx | ⟨y, hy, hxy⟩) | ⟨y, hy, hxy⟩
      · exact Nat.le_succ_of_le ((ih x).mp hx)
      · rw [← hxy]
        simp only [List.length_cons]
        exact Nat.succ_le_succ ((ih y).mp hy)
      · rw [← hxy]
        simp only [List.length_cons]
        exact Nat.succ_le_succ ((ih y).mp hy)
    · intro hx
      cases x with
      | nil =>
        exact Or.inl (Or.inl ((ih []).mpr (Nat.zero_le m)))
      | cons b y =>
        simp only [List.length_cons] at hx
        have hy : y.length ≤ m := Nat.le_of_succ_le_succ hx
        cases b with
        | true => exact Or.inl (Or.inr ⟨y, (ih y).mpr hy, rfl⟩)
        | false => exact Or.inr ⟨y, (ih y).mpr hy, rfl⟩

end PvsNP.Units.m2_z_long_part_conp

/-- The members longer than `m` of a coNP language form a coNP language: the
long lists are the complement of the finite language of lists of length at
most `m` (settled unit `m2_p_finite`, hence in NP by `m2_p_subset_np`), so the
long lists are in coNP; intersect with `L` by the settled unit
`m2_conp_inter`. -/
theorem PvsNP.Units.m2_z_long_part_conp :
    ∀ (L : Language Bool) (m : ℕ), L ∈ PvsNP.coNP → ({x : List Bool | x ∈ L ∧ m < x.length} : Language Bool) ∈ PvsNP.coNP := by
  intro L m hL
  have hshort : ({x : List Bool | x ∈ PvsNP.Units.m2_z_long_part_conp.shortLists m} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_finite _)
  have hcompl : ({x : List Bool | m < x.length} : Language Bool)ᶜ
      = ({x : List Bool | x ∈ PvsNP.Units.m2_z_long_part_conp.shortLists m} : Language Bool) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [PvsNP.Units.m2_z_long_part_conp.mem_shortLists]
    omega
  have hlong : ({x : List Bool | m < x.length} : Language Bool) ∈ PvsNP.coNP := by
    show ({x : List Bool | m < x.length} : Language Bool)ᶜ ∈ PvsNP.NP
    rw [hcompl]
    exact hshort
  have hS : ({x : List Bool | x ∈ L ∧ m < x.length} : Language Bool)
      = L ⊓ ({x : List Bool | m < x.length} : Language Bool) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2⟩
  rw [hS]
  exact PvsNP.Units.m2_conp_inter L _ hL hlong
