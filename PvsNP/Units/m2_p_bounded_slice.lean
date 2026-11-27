import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite

namespace PvsNP.Units.m2_p_bounded_slice

theorem finite_length_le : ∀ m : ℕ, {x : List Bool | x.length ≤ m}.Finite
  | 0 => by
      have h : {x : List Bool | x.length ≤ 0} = {[]} := by
        ext x
        simp
      rw [h]
      exact Set.finite_singleton _
  | m + 1 => by
      have hsub : {x : List Bool | x.length ≤ m + 1} ⊆
          {x : List Bool | x.length ≤ m} ∪
            (⋃ b : Bool, (fun x : List Bool => b :: x) '' {x : List Bool | x.length ≤ m}) := by
        intro x hx
        by_cases hle : x.length ≤ m
        · exact Or.inl hle
        · right
          have hlen : x.length = m + 1 := by omega
          cases x with
          | nil => simp at hlen
          | cons b t =>
              simp only [List.length_cons] at hlen
              exact Set.mem_biUnion ⟨b, by simp⟩ ⟨t, by omega, rfl⟩
      exact Set.Finite.subset
        (Set.Finite.union (finite_length_le m)
          (Set.finite_iUnion (fun b =>
            Set.Finite.image _ (finite_length_le m)))) hsub

end PvsNP.Units.m2_p_bounded_slice

theorem PvsNP.Units.m2_p_bounded_slice :
    ∀ (L : Language Bool) (m : ℕ),
      ({x : List Bool | x ∈ L ∧ x.length ≤ m} : Language Bool) ∈ PvsNP.P := by
  intro L m
  have hfin : {x : List Bool | x ∈ L ∧ x.length ≤ m}.Finite :=
    Set.Finite.subset (PvsNP.Units.m2_p_bounded_slice.finite_length_le m)
      (fun x hx => hx.2)
  have h := PvsNP.Units.m2_p_finite hfin.toFinset
  convert h using 2
  ext x
  simp [Set.Finite.mem_toFinset]
