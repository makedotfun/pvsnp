import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_models_count_disjoint_product

theorem PvsNP.Units.m3_y_shift_disjoint_sat :
∀ (N M : cnf) (k : ℕ), (∀ C ∈ N, ∀ l ∈ C, l.2 < k) →
  (SAT (N ++ M.map (fun C => C.map (fun l => (l.1, l.2 + k)))) ↔ SAT N ∧ SAT M) := by
  intro N M k bound
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨hn,hm⟩ := (evalCnf_app_iff _ _ _).1 ha
    let b := (M.flatten.map Prod.snd).filter (fun v => decide (v + k ∈ a))
    refine ⟨⟨a,hn⟩,⟨b,?_⟩⟩
    have equiv := PvsNP.Units.m3_models_count_disjoint_product.evalCnf_shift a M k b (by
      intro C hC l hl
      have mentioned : l.2 ∈ M.flatten.map Prod.snd :=
        List.mem_map.mpr ⟨l,List.mem_flatten.mpr ⟨C,hC,hl⟩,rfl⟩
      simp only [b,List.mem_filter,decide_eq_true_eq,mentioned,true_and])
    change evalCnf b M = true
    rw [← equiv]
    exact hm
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    let w := (a.filter (fun v => decide (v < k))) ++ b.map (fun v => v+k)
    refine ⟨w,(evalCnf_app_iff _ _ _).2 ⟨?_,?_⟩⟩
    · have equiv := PvsNP.Units.m3_models_count_disjoint_product.evalCnf_congr w a N (by
        intro C hC l hl
        have small := bound C hC l hl
        constructor
        · intro mem
          rcases List.mem_append.mp mem with mem | mem
          · exact (List.mem_filter.mp mem).1
          · obtain ⟨v,_,hv⟩ := List.mem_map.mp mem
            change v + k = l.2 at hv
            have ge : k ≤ l.2 := hv ▸ Nat.le_add_left k v
            exact (Nat.not_le_of_lt small ge).elim
        · intro mem
          exact List.mem_append_left _ (List.mem_filter.mpr ⟨mem,decide_eq_true small⟩))
      rw [equiv]
      exact ha
    · have equiv := PvsNP.Units.m3_models_count_disjoint_product.evalCnf_shift w M k b (by
        intro C _ l _
        constructor
        · intro mem
          rcases List.mem_append.mp mem with mem | mem
          · have h := of_decide_eq_true (List.mem_filter.mp mem).2
            omega
          · obtain ⟨v,hv,he⟩ := List.mem_map.mp mem
            change v + k = l.2 + k at he
            have : v = l.2 := Nat.add_right_cancel he
            exact this ▸ hv
        · intro mem
          exact List.mem_append_right _ (List.mem_map.mpr ⟨l.2,mem,rfl⟩))
      rw [equiv]
      exact hb
