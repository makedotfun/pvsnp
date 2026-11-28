import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_eq_np_npc
import PvsNP.Units.m2_nphard_in_p_iff

set_option autoImplicit false

theorem PvsNP.Units.m2_p_eq_np_iff_cofinite_nphard :
    PvsNP.P = PvsNP.NP ↔ ∃ (L : Language Bool) (S : Finset (List Bool)),
      (∀ x : List Bool, x ∉ L → x ∈ S) ∧ PvsNP.NPHard L := by
  constructor
  · intro hEq
    refine ⟨({x : List Bool | x ≠ []} : Language Bool), ({[]} : Finset (List Bool)), ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton]
      by_contra h
      exact hx h
    · have hfin : ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool)
          ∈ PvsNP.P :=
        PvsNP.Units.m2_p_finite {[]}
      have hL : ({x : List Bool | x ≠ []} : Language Bool) ∈ PvsNP.P := by
        have h := PvsNP.Units.m2_p_compl _ hfin
        have hset : ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool)ᶜ
            = {x : List Bool | x ≠ []} := by
          ext x
          simp [Finset.mem_singleton]
        rw [← hset]
        exact h
      have hne : (∃ y : List Bool, y ∈ ({x : List Bool | x ≠ []} : Language Bool)) :=
        ⟨[true], by simp⟩
      have hnot : (∃ z : List Bool, z ∉ ({x : List Bool | x ≠ []} : Language Bool)) :=
        ⟨[], by simp⟩
      exact (PvsNP.Units.m2_p_eq_np_npc hEq _ hL hne hnot).2
  · rintro ⟨L, S, hS, hhard⟩
    classical
    have hLc : Lᶜ
        = ({x : List Bool | x ∈ S.filter (fun x => x ∉ L)} : Language Bool) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨hS x hx, hx⟩
      · intro h
        exact h.2
    have hLcP : Lᶜ ∈ PvsNP.P := by
      rw [hLc]
      exact PvsNP.Units.m2_p_finite _
    have hLP : L ∈ PvsNP.P := by
      have h := PvsNP.Units.m2_p_compl Lᶜ hLcP
      rwa [compl_compl] at h
    exact PvsNP.Units.m2_nphard_in_p_iff.mp ⟨L, hhard, hLP⟩
