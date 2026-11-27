import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_implication_chain_models_count

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

def chainCnf (n : ℕ) : cnf :=
  (List.range n).map (fun i => [(false, i), (true, i + 1)])

def suffixModel (n k : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun j => decide (k ≤ j))

lemma mem_suffixModel (n k x : ℕ) :
    x ∈ suffixModel n k ↔ x < n + 1 ∧ k ≤ x := by
  simp [suffixModel]

lemma imp_clause_iff (a : assgn) (i : ℕ) :
    evalClause a [(false, i), (true, i + 1)] = true ↔ (i ∈ a → i + 1 ∈ a) := by
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    evalLiteral, evalVar, decide_eq_true_eq]
  by_cases hi : i ∈ a <;> by_cases hi1 : i + 1 ∈ a <;> simp [hi, hi1]

lemma evalCnf_chain_iff (n : ℕ) (a : assgn) :
    evalCnf a (chainCnf n) = true ↔ ∀ i < n, i ∈ a → i + 1 ∈ a := by
  rw [evalCnf_clause_iff]
  simp only [chainCnf, List.mem_map, List.mem_range]
  constructor
  · intro h i hi hia
    exact (imp_clause_iff a i).mp (h _ ⟨i, hi, rfl⟩) hia
  · rintro h C ⟨i, hi, rfl⟩
    exact (imp_clause_iff a i).mpr (h i hi)

lemma chain_upward {n : ℕ} {a : assgn} (h : ∀ i < n, i ∈ a → i + 1 ∈ a) {k : ℕ} (hk : k ∈ a) :
    ∀ j, k ≤ j → j ≤ n → j ∈ a := by
  intro j hkj hjn
  induction j with
  | zero =>
    have hk0 : k = 0 := by omega
    rwa [← hk0]
  | succ j ih =>
    rcases eq_or_lt_of_le hkj with rfl | hlt
    · exact hk
    · have hj_in : j ∈ a := ih (by omega) (by omega)
      exact h j (by omega) hj_in

end PvsNP.Units.m3_y_implication_chain_models_count

theorem PvsNP.Units.m3_y_implication_chain_models_count :
    ∀ n : ℕ,
      ((List.range (n + 1)).sublists.filter (fun a =>
        evalCnf a ((List.range n).map (fun i => [(false, i), (true, i + 1)])))).length = n + 2 := by
  intro n
  classical
  let S := (List.range (n + 1)).sublists.filter (fun a =>
    evalCnf a (PvsNP.Units.m3_y_implication_chain_models_count.chainCnf n))
  have hS_nd : S.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  have hbij : (Finset.range (n + 2)).card = S.toFinset.card := by
    refine Finset.card_bij
      (fun k _ => PvsNP.Units.m3_y_implication_chain_models_count.suffixModel n k) ?_ ?_ ?_
    · intro k _
      simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists]
      refine ⟨List.filter_sublist, ?_⟩
      rw [PvsNP.Units.m3_y_implication_chain_models_count.evalCnf_chain_iff]
      intro i hi hia
      rw [PvsNP.Units.m3_y_implication_chain_models_count.mem_suffixModel] at hia ⊢
      exact ⟨by omega, by omega⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      rw [Finset.mem_range] at hk₁ hk₂
      by_contra hne
      rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
      · have hm : k₁ ∈ PvsNP.Units.m3_y_implication_chain_models_count.suffixModel n k₁ := by
          rw [PvsNP.Units.m3_y_implication_chain_models_count.mem_suffixModel]
          omega
        rw [heq, PvsNP.Units.m3_y_implication_chain_models_count.mem_suffixModel] at hm
        omega
      · exact hne rfl
      · have hm : k₂ ∈ PvsNP.Units.m3_y_implication_chain_models_count.suffixModel n k₂ := by
          rw [PvsNP.Units.m3_y_implication_chain_models_count.mem_suffixModel]
          omega
        rw [← heq, PvsNP.Units.m3_y_implication_chain_models_count.mem_suffixModel] at hm
        omega
    · intro a ha
      simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists] at ha
      have hchain := (PvsNP.Units.m3_y_implication_chain_models_count.evalCnf_chain_iff n a).mp ha.2
      by_cases hex : ∃ i, i ≤ n ∧ i ∈ a
      · let k := Nat.find hex
        have hk_spec : k ≤ n ∧ k ∈ a := Nat.find_spec hex
        refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
        apply PvsNP.Units.m3_y_implication_chain_models_count.sublist_eq_of_mem_iff
          List.nodup_range List.filter_sublist ha.1
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hxlt, hkx⟩
          exact PvsNP.Units.m3_y_implication_chain_models_count.chain_upward hchain hk_spec.2 x hkx (by omega)
        · intro hxa
          have hxlt : x < n + 1 := List.mem_range.mp (ha.1.subset hxa)
          have hkx : k ≤ x := by
            by_contra hlt
            exact Nat.find_min hex (by omega) ⟨by omega, hxa⟩
          exact ⟨hxlt, hkx⟩
      · refine ⟨n + 1, Finset.mem_range.mpr (by omega), ?_⟩
        apply PvsNP.Units.m3_y_implication_chain_models_count.sublist_eq_of_mem_iff
          List.nodup_range List.filter_sublist ha.1
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hxlt, hnx⟩
          omega
        · intro hxa
          have hxlt : x < n + 1 := List.mem_range.mp (ha.1.subset hxa)
          exact absurd ⟨x, by omega, hxa⟩ hex
  calc S.length
      = S.toFinset.card := (List.toFinset_card_of_nodup hS_nd).symm
    _ = (Finset.range (n + 2)).card := hbij.symm
    _ = n + 2 := Finset.card_range (n + 2)
