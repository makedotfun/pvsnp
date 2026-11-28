import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union

namespace PvsNP.Units.m2_z_tally_np_compl_conp

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

theorem compl_eq (A : Set ℕ) :
    ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool)ᶜ =
    ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ⊔
      ({x : List Bool | x = List.replicate x.length true} : Language Bool)ᶜ := by
  ext x
  change (¬ ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true) ↔
    ((∃ n ∈ A, x = List.replicate n true) ∨ x ≠ List.replicate x.length true)
  constructor
  · intro h
    by_cases hx : x = List.replicate x.length true
    · by_cases hA : x.length ∈ A
      · exact Or.inl ⟨x.length, hA, hx⟩
      · exact False.elim (h ⟨x.length, hA, hx⟩)
    · exact Or.inr hx
  · rintro (⟨n, hnA, hxn⟩ | hx) ⟨m, hmA, hxm⟩
    · have hlen : n = m := by
        have h1 : x.length = n := by rw [hxn, List.length_replicate]
        have h2 : x.length = m := by rw [hxm, List.length_replicate]
        omega
      subst hlen
      exact hmA hnA
    · apply hx
      have hlen : x.length = m := by rw [hxm, List.length_replicate]
      rw [hlen]
      exact hxm

end PvsNP.Units.m2_z_tally_np_compl_conp

theorem PvsNP.Units.m2_z_tally_np_compl_conp :
    ∀ A : Set ℕ, ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.NP →
      ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool) ∈ PvsNP.coNP := by
  intro A hA
  change ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool)ᶜ ∈ PvsNP.NP
  rw [PvsNP.Units.m2_z_tally_np_compl_conp.compl_eq A]
  apply PvsNP.Units.m2_np_union
  · exact hA
  · apply PvsNP.Units.m2_p_subset_np
    apply PvsNP.Units.m2_p_compl
    exact PvsNP.Units.m2_z_tally_np_compl_conp.allTrue_in_P
