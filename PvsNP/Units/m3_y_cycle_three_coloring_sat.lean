import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_cycle_three_coloring_sat

def cycColor (n v : ℕ) : ℕ :=
  if v = n - 1 then 2 else v % 2

lemma cycColor_lt (n v : ℕ) : cycColor n v < 3 := by
  unfold cycColor
  split_ifs <;> omega

lemma cycColor_adj_ne {n : ℕ} (hn : 2 ≤ n) {i : ℕ} (hi : i < n) :
    cycColor n i ≠ cycColor n ((i + 1) % n) := by
  by_cases hlast : i = n - 1
  · subst hlast
    have hmod : (n - 1 + 1) % n = 0 := by
      rw [show n - 1 + 1 = n by omega, Nat.mod_self]
    rw [hmod]
    have h0ne : (0 : ℕ) ≠ n - 1 := by omega
    simp [cycColor, h0ne]
  · have hilt : i + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hilt]
    by_cases hnext : i + 1 = n - 1
    · simp only [cycColor, hlast, hnext, ↓reduceIte]
      omega
    · simp only [cycColor, hlast, hnext, ↓reduceIte]
      omega

def cycAssgn (n : ℕ) : assgn :=
  (List.range n).map (fun v => v * 3 + cycColor n v)

lemma mem_cycAssgn {n v c : ℕ} (hv : v < n) (hc : c < 3) :
    v * 3 + c ∈ cycAssgn n ↔ c = cycColor n v := by
  unfold cycAssgn
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨v', hv', heq⟩
    have hc' : cycColor n v' < 3 := cycColor_lt n v'
    have hvv : v' = v := by omega
    subst hvv
    omega
  · rintro rfl
    exact ⟨v, hv, rfl⟩

end PvsNP.Units.m3_y_cycle_three_coloring_sat

theorem PvsNP.Units.m3_y_cycle_three_coloring_sat :
    ∀ n : ℕ, 2 ≤ n →
      SAT ((List.range n).map (fun v => (List.range 3).map (fun c => (true, v * 3 + c))) ++
        (List.range n).flatMap (fun i =>
          (List.range 3).map (fun c => [(false, i * 3 + c), (false, ((i + 1) % n) * 3 + c)]))) := by
  intro n hn
  let a := PvsNP.Units.m3_y_cycle_three_coloring_sat.cycAssgn n
  refine ⟨a, ?_⟩
  unfold satisfiesCnf
  rw [evalCnf_app_iff]
  constructor
  · rw [evalCnf_clause_iff]
    intro C hC
    obtain ⟨v, hv_mem, rfl⟩ := List.mem_map.mp hC
    have hv : v < n := List.mem_range.mp hv_mem
    let c := PvsNP.Units.m3_y_cycle_three_coloring_sat.cycColor n v
    have hc_lt : c < 3 := PvsNP.Units.m3_y_cycle_three_coloring_sat.cycColor_lt n v
    have hin : v * 3 + c ∈ a :=
      (PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_cycAssgn hv hc_lt).mpr rfl
    rw [evalClause_literal_iff]
    refine ⟨(true, v * 3 + c), List.mem_map.mpr ⟨c, List.mem_range.mpr hc_lt, rfl⟩, ?_⟩
    simp [evalLiteral, evalVar, hin]
  · rw [evalCnf_clause_iff]
    intro C hC
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hC
    obtain ⟨i, hi, c, hc, rfl⟩ := hC
    have hne := PvsNP.Units.m3_y_cycle_three_coloring_sat.cycColor_adj_ne hn hi
    by_cases hci : c = PvsNP.Units.m3_y_cycle_three_coloring_sat.cycColor n i
    · have hcj : c ≠ PvsNP.Units.m3_y_cycle_three_coloring_sat.cycColor n ((i + 1) % n) := by
        rw [hci]; exact hne
      have hnot : ((i + 1) % n) * 3 + c ∉ a := fun hm =>
        hcj ((PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_cycAssgn
          (Nat.mod_lt _ (by omega)) hc).mp hm)
      rw [evalClause_literal_iff]
      exact ⟨(false, ((i + 1) % n) * 3 + c), by simp, by simp [evalLiteral, evalVar, hnot]⟩
    · have hnot : i * 3 + c ∉ a := fun hm =>
        hci ((PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_cycAssgn hi hc).mp hm)
      rw [evalClause_literal_iff]
      exact ⟨(false, i * 3 + c), by simp, by simp [evalLiteral, evalVar, hnot]⟩
