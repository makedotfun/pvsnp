import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_xor_path_models_count

lemma sublist_eq_of_mem_iff :
    ∀ {l a b : List ℕ}, l.Nodup → List.Sublist a l → List.Sublist b l → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], a, b, _, ha, hb, _ => by
    rw [List.sublist_nil.mp ha, List.sublist_nil.mp hb]
  | y :: l, a, b, hnd, ha, hb, hmem => by
    rw [List.nodup_cons] at hnd
    cases ha with
    | cons _ ha' =>
      have hya : y ∉ a := fun h => hnd.1 (ha'.subset h)
      cases hb with
      | cons _ hb' => exact sublist_eq_of_mem_iff hnd.2 ha' hb' hmem
      | cons_cons _ hb' => exact absurd ((hmem y).mpr List.mem_cons_self) hya
    | cons_cons _ ha' =>
      cases hb with
      | cons _ hb' =>
        have hyb : y ∉ b := fun h => hnd.1 (hb'.subset h)
        exact absurd ((hmem y).mp List.mem_cons_self) hyb
      | cons_cons _ hb' =>
        congr 1
        apply sublist_eq_of_mem_iff hnd.2 ha' hb'
        intro x
        by_cases h : x = y
        · subst h
          exact ⟨fun hx => absurd (ha'.subset hx) hnd.1, fun hx => absurd (hb'.subset hx) hnd.1⟩
        · have := hmem x
          simpa [List.mem_cons, h] using this

def xorPathCnf (n : ℕ) : cnf :=
  (List.range n).flatMap (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])

lemma xor_pair_iff (a : assgn) (i : ℕ) :
    (evalClause a [(true, i), (true, i + 1)] = true ∧
      evalClause a [(false, i), (false, i + 1)] = true) ↔
      (i ∈ a ↔ i + 1 ∉ a) := by
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    evalLiteral, evalVar, decide_eq_true_eq]
  by_cases hi : i ∈ a <;> by_cases hi1 : i + 1 ∈ a <;> simp [hi, hi1]

lemma evalCnf_xorPath_iff (n : ℕ) (a : assgn) :
    evalCnf a (xorPathCnf n) = true ↔ ∀ i < n, (i ∈ a ↔ i + 1 ∉ a) := by
  rw [evalCnf_clause_iff]
  simp only [xorPathCnf, List.mem_flatMap, List.mem_range]
  constructor
  · intro h i hi
    refine (xor_pair_iff a i).mp ⟨?_, ?_⟩
    · exact h _ ⟨i, hi, by simp⟩
    · exact h _ ⟨i, hi, by simp⟩
  · rintro h C ⟨i, hi, hC⟩
    have hp := (xor_pair_iff a i).mpr (h i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact hp.1
    · exact hp.2

lemma alternating_iff (n : ℕ) (a : assgn) :
    (∀ i < n, (i ∈ a ↔ i + 1 ∉ a)) →
      ∀ i ≤ n, (i ∈ a ↔ (0 ∈ a ↔ i % 2 = 0)) := by
  intro hstep i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ∈ a ↔ (0 ∈ a ↔ i % 2 = 0) := ih (by omega)
    have hst : i ∈ a ↔ i + 1 ∉ a := hstep i (by omega)
    have hmod : (i + 1) % 2 = 0 ↔ ¬ (i % 2 = 0) := by omega
    by_cases h0 : 0 ∈ a <;> by_cases hm : i % 2 = 0 <;> simp_all

def parityModel (n r : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun i => decide (i % 2 = r))

end PvsNP.Units.m3_y_xor_path_models_count

theorem PvsNP.Units.m3_y_xor_path_models_count :
    ∀ n : ℕ,
      ((List.range (n + 1)).sublists.filter (fun a =>
        evalCnf a ((List.range n).flatMap (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])))).length = 2 := by
  intro n
  classical
  let S := (List.range (n + 1)).sublists.filter (fun a =>
    evalCnf a (PvsNP.Units.m3_y_xor_path_models_count.xorPathCnf n))
  have hS_nd : S.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  let m0 := PvsNP.Units.m3_y_xor_path_models_count.parityModel n 0
  let m1 := PvsNP.Units.m3_y_xor_path_models_count.parityModel n 1
  have hne : m0 ≠ m1 := by
    intro heq
    have h0 : 0 ∈ m0 := by simp [m0, PvsNP.Units.m3_y_xor_path_models_count.parityModel]
    rw [heq] at h0
    simp [m1, PvsNP.Units.m3_y_xor_path_models_count.parityModel] at h0
  have hm0_in : m0 ∈ S := by
    simp only [S, List.mem_filter, List.mem_sublists]
    refine ⟨List.filter_sublist, ?_⟩
    rw [PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff]
    intro i hi
    simp only [m0, PvsNP.Units.m3_y_xor_path_models_count.parityModel, List.mem_filter,
      List.mem_range, decide_eq_true_eq]
    omega
  have hm1_in : m1 ∈ S := by
    simp only [S, List.mem_filter, List.mem_sublists]
    refine ⟨List.filter_sublist, ?_⟩
    rw [PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff]
    intro i hi
    simp only [m1, PvsNP.Units.m3_y_xor_path_models_count.parityModel, List.mem_filter,
      List.mem_range, decide_eq_true_eq]
    omega
  have hfin : S.toFinset = ({m0, m1} : Finset (List ℕ)) := by
    ext a
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ha
      simp only [S, List.mem_filter, List.mem_sublists] at ha
      have hstep := (PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff n a).mp ha.2
      have halt := PvsNP.Units.m3_y_xor_path_models_count.alternating_iff n a hstep
      by_cases h0 : 0 ∈ a
      · left
        apply PvsNP.Units.m3_y_xor_path_models_count.sublist_eq_of_mem_iff
          List.nodup_range ha.1 List.filter_sublist
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro hxa
          have hxlt : x < n + 1 := List.mem_range.mp (ha.1.subset hxa)
          exact ⟨hxlt, ((halt x (by omega)).mp hxa).mp h0⟩
        · rintro ⟨hxlt, hmod⟩
          exact (halt x (by omega)).mpr ⟨fun _ => hmod, fun _ => h0⟩
      · right
        apply PvsNP.Units.m3_y_xor_path_models_count.sublist_eq_of_mem_iff
          List.nodup_range ha.1 List.filter_sublist
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro hxa
          have hxlt : x < n + 1 := List.mem_range.mp (ha.1.subset hxa)
          have hne0 : x % 2 ≠ 0 := fun hm => h0 (((halt x (by omega)).mp hxa).mpr hm)
          exact ⟨hxlt, by omega⟩
        · rintro ⟨hxlt, hmod⟩
          exact (halt x (by omega)).mpr ⟨fun h0' => absurd h0' h0, fun hm => by omega⟩
    · rintro (rfl | rfl)
      · exact hm0_in
      · exact hm1_in
  calc S.length
      = S.toFinset.card := (List.toFinset_card_of_nodup hS_nd).symm
    _ = ({m0, m1} : Finset (List ℕ)).card := by rw [hfin]
    _ = 2 := Finset.card_pair hne
