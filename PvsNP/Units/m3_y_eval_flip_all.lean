import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_eval_flip_all_aux

/-- Flipping a literal in `a` is the same as evaluating it in `b`,
    for a variable occurring in `N` (where `b` agrees with the complement of `a`). -/
theorem evalLiteral_flip {N : cnf} {a b : assgn} {s : Bool} {v : var}
    (hv : v ∈ N.flatten.map Prod.snd)
    (hb : ∀ w, w ∈ N.flatten.map Prod.snd → (w ∈ b ↔ w ∉ a)) :
    evalLiteral a (!s, v) = evalLiteral b (s, v) := by
  have hbb : decide (v ∈ b) = !decide (v ∈ a) := by
    by_cases ha : v ∈ a
    · have hnb : v ∉ b := fun h => (hb v hv).mp h ha
      simp [ha, hnb]
    · have hb' : v ∈ b := (hb v hv).mpr ha
      simp [ha, hb']
  simp only [evalLiteral, evalVar]
  by_cases ha : v ∈ a <;> cases s <;> simp [ha, hbb]

end PvsNP.Units.m3_y_eval_flip_all_aux

open PvsNP.Units.m3_y_eval_flip_all_aux

theorem PvsNP.Units.m3_y_eval_flip_all :
    ∀ (N : cnf) (a : assgn),
      evalCnf a (N.map (fun C => C.map (fun l => (!l.1, l.2)))) =
        evalCnf ((N.flatten.map Prod.snd).filter (fun v => decide (v ∉ a))) N := by
  intro N a
  set b := (N.flatten.map Prod.snd).filter (fun v => decide (v ∉ a)) with hb_def
  have hb : ∀ w, w ∈ N.flatten.map Prod.snd → (w ∈ b ↔ w ∉ a) := by
    intro w hw
    rw [hb_def, List.mem_filter]
    constructor
    · intro h
      exact decide_eq_true_eq.mp h.2
    · intro h
      exact ⟨hw, decide_eq_true_eq.mpr h⟩
  -- Literal-level flip, for literals of clauses of `N`.
  have hlit : ∀ (C : clause) (l : literal), C ∈ N → l ∈ C →
      evalLiteral a (!l.1, l.2) = evalLiteral b l := by
    intro C l hC hl
    cases l with
    | mk s v =>
      show evalLiteral a (!s, v) = evalLiteral b (s, v)
      apply evalLiteral_flip
      · apply List.mem_map.mpr
        exact ⟨(s, v), List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩
      · exact hb
  apply Bool.eq_iff_iff.mpr
  simp only [evalCnf, List.all_eq_true]
  constructor
  · intro h C hC
    have h1 := h (C.map (fun l => (!l.1, l.2))) (List.mem_map.mpr ⟨C, hC, rfl⟩)
    rw [evalClause_literal_iff] at h1
    obtain ⟨l, hl, hlt⟩ := h1
    rw [List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    rw [evalClause_literal_iff]
    refine ⟨l', hl', ?_⟩
    rw [← hlit C l' hC hl']
    exact hlt
  · intro h C hC
    rw [List.mem_map] at hC
    obtain ⟨C', hC', rfl⟩ := hC
    have h1 := h C' hC'
    rw [evalClause_literal_iff] at h1
    obtain ⟨l', hl', hlt⟩ := h1
    rw [evalClause_literal_iff]
    refine ⟨(!l'.1, l'.2), List.mem_map.mpr ⟨l', hl', rfl⟩, ?_⟩
    rw [hlit C' l' hC' hl']
    exact hlt
