import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_horn_flip_dual_horn :
    ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
      ∀ C ∈ N.map (fun C => C.map (fun l => (!l.1, l.2))), (C.filter (fun l => !l.1)).length ≤ 1 := by
  intro N hH C hC
  obtain ⟨D, hDN, rfl⟩ := List.mem_map.mp hC
  rw [List.filter_map, List.length_map]
  have heq : ((fun l : literal => !l.1) ∘ fun l : literal => (!l.1, l.2)) = fun l : literal => l.1 := by
    funext l
    simp
  rw [heq]
  exact hH D hDN
