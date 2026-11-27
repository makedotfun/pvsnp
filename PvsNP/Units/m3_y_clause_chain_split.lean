import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_clause_chain_split

lemma evalLiteral_congr {a a' : assgn} {l : literal} (h : l.2 ∈ a ↔ l.2 ∈ a') :
    evalLiteral a l = evalLiteral a' l := by
  rcases l with ⟨s, v⟩
  simp only [evalLiteral, evalVar] at h ⊢
  by_cases hv : v ∈ a
  · have hv' : v ∈ a' := h.mp hv
    simp [hv, hv']
  · have hv' : v ∉ a' := fun hx => hv (h.mpr hx)
    simp [hv, hv']

lemma evalClause_congr {a a' : assgn} {C : clause} {z : ℕ}
    (hC : ∀ l ∈ C, l.2 < z) (hmem : ∀ v < z, (v ∈ a ↔ v ∈ a')) :
    evalClause a C = evalClause a' C := by
  apply Bool.eq_iff_iff.mpr
  rw [evalClause_literal_iff, evalClause_literal_iff]
  exact exists_congr fun l => and_congr_right fun hl => by
    rw [evalLiteral_congr (hmem l.2 (hC l hl))]

lemma evalCnf_congr {a a' : assgn} {N : cnf} {z : ℕ}
    (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 < z) (hmem : ∀ v < z, (v ∈ a ↔ v ∈ a')) :
    evalCnf a N = evalCnf a' N := by
  apply Bool.eq_iff_iff.mpr
  rw [evalCnf_clause_iff, evalCnf_clause_iff]
  exact forall_congr' fun C => imp_congr_right fun hC => by
    rw [evalClause_congr (hN C hC) hmem]

end PvsNP.Units.m3_y_clause_chain_split

theorem PvsNP.Units.m3_y_clause_chain_split :
    ∀ (N : cnf) (ls : List literal) (z : var), (∀ l ∈ ls, l.2 < z) → (∀ C ∈ N, ∀ l ∈ C, l.2 < z) →
      (SAT ([(false, z)] :: [(true, z + ls.length)] ::
          ((List.range ls.length).map (fun i => [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)]) ++ N)) ↔
        SAT (ls :: N)) := by
  intro N ls z hls hN
  change ℕ at z
  constructor
  · rintro ⟨a, ha⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha
    rcases ha with ⟨hz0, hzm, hrest⟩
    have hrest' : evalCnf a ((List.range ls.length).map
        (fun i => [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)]) ++ N) = true := hrest
    rw [evalCnf_app_iff] at hrest'
    rcases hrest' with ⟨hchain, haN⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, haN⟩
    by_contra hls_false
    have hls_eq_false : evalClause a ls = false := by
      cases h : evalClause a ls
      · rfl
      · exact absurd h hls_false
    have hz_not : z ∉ a := by
      obtain ⟨l', hl'_m, hl'_t⟩ := (evalClause_literal_iff a [(false, z)]).mp hz0
      simp only [List.mem_singleton] at hl'_m
      subst hl'_m
      intro hza
      simp [evalLiteral, evalVar, hza] at hl'_t
    have hzm_in : z + ls.length ∈ a := by
      obtain ⟨l', hl'_m, hl'_t⟩ := (evalClause_literal_iff a [(true, z + ls.length)]).mp hzm
      simp only [List.mem_singleton] at hl'_m
      subst hl'_m
      by_contra hnot
      simp [evalLiteral, evalVar, hnot] at hl'_t
    have hall_not : ∀ i ≤ ls.length, z + i ∉ a := by
      intro i hi
      induction i with
      | zero => simpa using hz_not
      | succ i ih =>
        have hi_not : z + i ∉ a := ih (by omega)
        have hci : evalClause a [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)] = true := by
          rw [evalCnf_clause_iff] at hchain
          exact hchain _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)
        have hget_mem : ls.getD i (true, 0) ∈ ls := by
          have hilt : i < ls.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some]
          exact List.getElem_mem hilt
        have hlit_false : evalLiteral a (ls.getD i (true, 0)) = false := by
          cases h : evalLiteral a (ls.getD i (true, 0))
          · rfl
          · have htrue : evalClause a ls = true :=
              (evalClause_literal_iff a ls).mpr ⟨_, hget_mem, h⟩
            rw [hls_eq_false] at htrue
            cases htrue
        obtain ⟨l', hl'_m, hl'_t⟩ := (evalClause_literal_iff a _).mp hci
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'_m
        rcases hl'_m with rfl | rfl | rfl
        · intro hzin
          have heq_idx : z + (i + 1) = z + i + 1 := by omega
          have hzin' : z + i + 1 ∈ a := heq_idx ▸ hzin
          simp [evalLiteral, evalVar, hzin'] at hl'_t
        · simp [evalLiteral, evalVar, hi_not] at hl'_t
        · rw [hlit_false] at hl'_t
          cases hl'_t
    exact hall_not ls.length le_rfl hzm_in
  · rintro ⟨a, ha⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha
    rcases ha with ⟨ha_ls, haN⟩
    obtain ⟨l, hl_mem, hl_true⟩ := (evalClause_literal_iff a ls).mp ha_ls
    obtain ⟨k, hk_lt, rfl⟩ := List.mem_iff_getElem.mp hl_mem
    let a' : assgn :=
      a.filter (fun v => decide (v < z)) ++
        ((List.range (ls.length + 1)).filter (fun j => decide (k + 1 ≤ j))).map (fun j => z + j)
    have hbelow : ∀ v < z, (v ∈ a ↔ v ∈ a') := by
      intro v hv
      simp only [a', List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map,
        List.mem_range]
      constructor
      · intro hva
        exact Or.inl ⟨hva, hv⟩
      · rintro (⟨hva, _⟩ | ⟨j, _, heq⟩)
        · exact hva
        · omega
    have hshift : ∀ j ≤ ls.length, (z + j ∈ a' ↔ k + 1 ≤ j) := by
      intro j hj
      simp only [a', List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map,
        List.mem_range]
      constructor
      · rintro (⟨_, hlt⟩ | ⟨j', ⟨_, hkj'⟩, heq⟩)
        · omega
        · omega
      · intro hkj
        exact Or.inr ⟨j, ⟨by omega, hkj⟩, rfl⟩
    refine ⟨a', ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_⟩
    · have hz0 : z ∉ a' := by
        have := hshift 0 (Nat.zero_le _)
        simpa using (fun h => absurd (this.mp h) (by omega))
      simp [evalClause, evalLiteral, evalVar, hz0]
    · have hzm : z + ls.length ∈ a' := (hshift ls.length le_rfl).mpr (by omega)
      simp [evalClause, evalLiteral, evalVar, hzm]
    · show evalCnf a' ((List.range ls.length).map
          (fun i => [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)]) ++ N) = true
      rw [evalCnf_app_iff]
      refine ⟨?_, ?_⟩
      · rw [evalCnf_clause_iff]
        intro C hC
        obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hC
        have hi_lt : i < ls.length := List.mem_range.mp hi_mem
        rcases lt_trichotomy i k with hik | rfl | hki
        · have hnot : z + i + 1 ∉ a' := by
            have := hshift (i + 1) (by omega)
            intro h
            have hk1 := this.mp (by rwa [Nat.add_assoc] at h)
            omega
          rw [evalClause_literal_iff]
          exact ⟨(false, z + i + 1), by simp, by simp [evalLiteral, evalVar, hnot]⟩
        · have hget_eq : ls.getD i (true, 0) = ls[i] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, Option.getD_some]
          have hlit' : evalLiteral a' (ls.getD i (true, 0)) = true := by
            rw [hget_eq]
            rw [← PvsNP.Units.m3_y_clause_chain_split.evalLiteral_congr
              (hbelow ls[i].2 (hls ls[i] (List.getElem_mem hi_lt)))]
            exact hl_true
          rw [evalClause_literal_iff]
          exact ⟨ls.getD i (true, 0), by simp, hlit'⟩
        · have hin : z + i ∈ a' := (hshift i (by omega)).mpr (by omega)
          rw [evalClause_literal_iff]
          exact ⟨(true, z + i), by simp, by simp [evalLiteral, evalVar, hin]⟩
      · rw [← PvsNP.Units.m3_y_clause_chain_split.evalCnf_congr hN hbelow]
        exact haN
