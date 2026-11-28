import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_diff
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_inv_hom_closed

namespace PvsNP.Units.m2_z_tally_compl_p

/-- The homomorphism sending `true` to `[]` and `false` to `[false]`. -/
def hom (b : Bool) : List Bool := if b then [] else [false]

theorem allTrue_P :
    ({x : List Bool | x.flatMap hom ∈ ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool)} :
      Language Bool) ∈ PvsNP.P :=
  ((PvsNP.Units.m2_inv_hom_closed hom _).1 (PvsNP.Units.m2_p_finite {[]}))

theorem mem_allTrue (x : List Bool) :
    x.flatMap hom ∈ ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool) ↔
      ∀ b ∈ x, b = true := by
  show x.flatMap hom ∈ ({[]} : Finset (List Bool)) ↔ _
  rw [Finset.mem_singleton, List.flatMap_eq_nil_iff]
  refine forall_congr' fun b => imp_congr_right fun _ => ?_
  cases b <;> simp [hom]

theorem key (p : ℕ → Prop) :
    ({x : List Bool | ∃ n : ℕ, ¬ p n ∧ x = List.replicate n true} : Language Bool) =
      {x : List Bool |
        x ∈ ({x : List Bool | x.flatMap hom ∈
          ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool)} : Language Bool) ∧
        x ∉ ({x : List Bool | ∃ n : ℕ, p n ∧ x = List.replicate n true} : Language Bool)} := by
  ext x
  show (∃ n : ℕ, ¬ p n ∧ x = List.replicate n true) ↔
    (x.flatMap hom ∈ ({x : List Bool | x ∈ ({[]} : Finset (List Bool))} : Language Bool) ∧
      ¬ ∃ n : ℕ, p n ∧ x = List.replicate n true)
  rw [mem_allTrue]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨fun b hb => List.eq_of_mem_replicate hb, ?_⟩
    rintro ⟨m, hm, he⟩
    have := congrArg List.length he
    simp only [List.length_replicate] at this
    exact hn (this ▸ hm)
  · rintro ⟨hall, hnot⟩
    have hx : x = List.replicate x.length true := List.eq_replicate_iff.2 ⟨rfl, hall⟩
    refine ⟨x.length, fun hp => hnot ⟨x.length, hp, hx⟩, hx⟩

end PvsNP.Units.m2_z_tally_compl_p

theorem PvsNP.Units.m2_z_tally_compl_p :
    ∀ A : Set ℕ, ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.P ↔ ({x : List Bool | ∃ n : ℕ, n ∉ A ∧ x = List.replicate n true} : Language Bool) ∈ PvsNP.P := by
  intro A
  constructor
  · intro h
    have := PvsNP.Units.m2_p_diff _ _ PvsNP.Units.m2_z_tally_compl_p.allTrue_P h
    convert this using 1
    exact PvsNP.Units.m2_z_tally_compl_p.key (fun n => n ∈ A)
  · intro h
    have := PvsNP.Units.m2_p_diff _ _ PvsNP.Units.m2_z_tally_compl_p.allTrue_P h
    convert this using 1
    refine Eq.trans ?_ (PvsNP.Units.m2_z_tally_compl_p.key (fun n => n ∉ A))
    ext x
    simp only [Set.mem_setOf_eq, not_not]
