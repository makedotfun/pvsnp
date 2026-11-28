import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_inter

namespace PvsNP.Units.m2_z_tally_conp_compl_np

def dropTrue (b : Bool) : List Bool :=
  match b with
  | true => []
  | false => [false]

theorem flatMap_dropTrue_eq_nil_iff (x : List Bool) :
    x.flatMap dropTrue = [] ↔ x = List.replicate x.length true := by
  rw [List.flatMap_eq_nil_iff, List.eq_replicate_iff]
  refine ⟨fun h => ⟨rfl, fun b hb => ?_⟩, fun ⟨_, h⟩ b hb => ?_⟩
  · have hb' := h b hb
    cases b
    · simp [dropTrue] at hb'
    · rfl
  · rw [h b hb]
    rfl

theorem allTrue_in_P :
    ({x : List Bool | x = List.replicate x.length true} : Language Bool) ∈ PvsNP.P := by
  have hfin : ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite {[]}
  have hpre :
      ({x : List Bool | x.flatMap dropTrue ∈ ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool)} :
        Language Bool) ∈ PvsNP.P :=
    (PvsNP.Units.m2_inv_hom_closed dropTrue _).1 hfin
  have heq :
      ({x : List Bool | x = List.replicate x.length true} : Language Bool) =
      ({x : List Bool | x.flatMap dropTrue ∈ ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool)} :
        Language Bool) := by
    ext x
    change (x = List.replicate x.length true) ↔ (x.flatMap dropTrue ∈ ({[]} : Finset (List Bool)))
    rw [Finset.mem_singleton, flatMap_dropTrue_eq_nil_iff]
  rw [heq]
  exact hpre

theorem inter_eq (A : Set ℕ) :
    ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) =
    ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool)ᶜ ⊓
      ({x : List Bool | x = List.replicate x.length true} : Language Bool) := by
  ext x
  change (∃ n ∈ A, x = List.replicate n true) ↔
    ((¬ ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true) ∧ x = List.replicate x.length true)
  constructor
  · rintro ⟨n, hnA, hxn⟩
    have hlen : x.length = n := by rw [hxn, List.length_replicate]
    refine ⟨?_, ?_⟩
    · rintro ⟨m, hmA, hxm⟩
      have hlen2 : x.length = m := by rw [hxm, List.length_replicate]
      have hnm : n = m := by omega
      subst hnm
      exact hmA hnA
    · rw [hlen]
      exact hxn
  · rintro ⟨hnot, hx⟩
    by_cases hA : x.length ∈ A
    · exact ⟨x.length, hA, hx⟩
    · exact False.elim (hnot ⟨x.length, hA, hx⟩)

end PvsNP.Units.m2_z_tally_conp_compl_np

theorem PvsNP.Units.m2_z_tally_conp_compl_np :
    ∀ A : Set ℕ, ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool) ∈ PvsNP.coNP →
      ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.NP := by
  intro A hA
  rw [PvsNP.Units.m2_z_tally_conp_compl_np.inter_eq A]
  apply PvsNP.Units.m2_np_inter
  · exact hA
  · apply PvsNP.Units.m2_p_subset_np
    exact PvsNP.Units.m2_z_tally_conp_compl_np.allTrue_in_P
