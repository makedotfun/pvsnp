import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_models_count_unit

/-- The single unit clause is satisfied exactly when its literal is. -/
theorem evalCnf_singleton (a : assgn) (l : literal) :
    evalCnf a [[l]] = evalLiteral a l := by
  simp [evalCnf, evalClause]

/-- Unfolding a literal's evaluation to a `decide` of membership. -/
theorem evalLiteral_decide (a : assgn) (s : Bool) (v : var) :
    evalLiteral a (s, v) = decide (decide (v ∈ a) = s) := rfl

/-- No sublist of `List.range n` contains `n`. -/
theorem not_mem_of_mem_sublists_range {a : List ℕ} {n : ℕ}
    (h : a ∈ (List.range n).sublists) : n ∉ a := by
  rw [List.mem_sublists] at h
  intro hn
  have hn' : n ∈ List.range n := h.subset hn
  exact Nat.lt_irrefl n (List.mem_range.mp hn')

/-- The counting statement, proved by induction on `n`. -/
theorem count_aux : ∀ n : ℕ, ∀ l : literal, l.2 < n →
    (((List.range n).sublists.filter (fun a => evalCnf a [[l]])).length = 2 ^ (n - 1)) := by
  intro n
  induction n with
  | zero =>
      intro l h
      exact (Nat.not_lt_zero _ h).elim
  | succ n ih =>
      intro l hl
      rcases l with ⟨s, v⟩
      have hl' : v < n + 1 := hl
      show ((List.range (n + 1)).sublists.filter
          (fun a => evalCnf a [[(s, v)]])).length = 2 ^ (n + 1 - 1)
      have hsub : (List.range (n + 1)).sublists =
          (List.range n).sublists ++
            ((List.range n).sublists.map (fun a => a ++ [n])) := by
        rw [List.range_succ, List.sublists_concat]
      rw [hsub, List.filter_append, List.length_append, Nat.add_sub_cancel]
      have hmap : ((List.range n).sublists.map (fun a => a ++ [n])).filter
            (fun a => evalCnf a [[(s, v)]]) =
          ((List.range n).sublists.filter
            (fun a => evalCnf (a ++ [n]) [[(s, v)]])).map (fun a => a ++ [n]) :=
        List.filter_map
      rw [hmap, List.length_map]
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hl') with hvn | hvn
      · -- Case `v < n`: appending `n` does not change satisfaction, so the count doubles.
        have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hvn
        have hn1 : 1 ≤ n := hn0
        have hmem : ∀ a : List ℕ, v ∈ a ++ [n] ↔ v ∈ a := by
          intro a
          simp [List.mem_append, Nat.ne_of_lt hvn]
        have hpoint : ∀ a : List ℕ,
            evalCnf (a ++ [n]) [[(s, v)]] = evalCnf a [[(s, v)]] := by
          intro a
          have hd : decide (v ∈ a ++ [n]) = decide (v ∈ a) :=
            decide_eq_decide.mpr (hmem a)
          calc evalCnf (a ++ [n]) [[(s, v)]]
              = decide (decide (v ∈ a ++ [n]) = s) := by
                rw [evalCnf_singleton, evalLiteral_decide]
            _ = decide (decide (v ∈ a) = s) := by rw [hd]
            _ = evalCnf a [[(s, v)]] := by
                rw [evalCnf_singleton, evalLiteral_decide]
        rw [List.filter_congr (fun a _ => hpoint a), ih (s, v) hvn,
          ← two_mul, ← pow_succ', Nat.sub_add_cancel hn1]
      · -- Case `v = n`: exactly one of the two halves is satisfied, whichever way `s` goes.
        -- (`subst` replaces `n` by `v` everywhere, so the rest is stated in terms of `v`.)
        subst hvn
        cases s with
        | false =>
            have h1 : ∀ a ∈ (List.range v).sublists,
                evalCnf a [[(false, v)]] = true := by
              intro a ha
              have hva : v ∉ a := not_mem_of_mem_sublists_range ha
              have hd : decide (v ∈ a) = false := by
                rw [decide_eq_false_iff_not]; exact hva
              calc evalCnf a [[(false, v)]]
                  = decide (decide (v ∈ a) = false) := by
                    rw [evalCnf_singleton, evalLiteral_decide]
                _ = decide (false = false) := by rw [hd]
                _ = true := rfl
            have h2 : ∀ a ∈ (List.range v).sublists,
                evalCnf (a ++ [v]) [[(false, v)]] = false := by
              intro a _
              have hmemv : v ∈ a ++ [v] := by simp
              have hd : decide (v ∈ a ++ [v]) = true := by
                rw [decide_eq_true_eq]; exact hmemv
              calc evalCnf (a ++ [v]) [[(false, v)]]
                  = decide (decide (v ∈ a ++ [v]) = false) := by
                    rw [evalCnf_singleton, evalLiteral_decide]
                _ = decide (true = false) := by rw [hd]
                _ = false := rfl
            rw [List.filter_eq_self.mpr h1,
              List.filter_eq_nil_iff.mpr (fun a ha => by simp [h2 a ha]),
              List.length_sublists, List.length_range]
            simp
        | true =>
            have h1 : ∀ a ∈ (List.range v).sublists,
                evalCnf a [[(true, v)]] = false := by
              intro a ha
              have hva : v ∉ a := not_mem_of_mem_sublists_range ha
              have hd : decide (v ∈ a) = false := by
                rw [decide_eq_false_iff_not]; exact hva
              calc evalCnf a [[(true, v)]]
                  = decide (decide (v ∈ a) = true) := by
                    rw [evalCnf_singleton, evalLiteral_decide]
                _ = decide (false = true) := by rw [hd]
                _ = false := rfl
            have h2 : ∀ a ∈ (List.range v).sublists,
                evalCnf (a ++ [v]) [[(true, v)]] = true := by
              intro a _
              have hmemv : v ∈ a ++ [v] := by simp
              have hd : decide (v ∈ a ++ [v]) = true := by
                rw [decide_eq_true_eq]; exact hmemv
              calc evalCnf (a ++ [v]) [[(true, v)]]
                  = decide (decide (v ∈ a ++ [v]) = true) := by
                    rw [evalCnf_singleton, evalLiteral_decide]
                _ = decide (true = true) := by rw [hd]
                _ = true := rfl
            rw [List.filter_eq_nil_iff.mpr (fun a ha => by simp [h1 a ha]),
              List.filter_eq_self.mpr h2,
              List.length_sublists, List.length_range]
            simp

end PvsNP.Units.m3_y_models_count_unit

theorem PvsNP.Units.m3_y_models_count_unit :
    ∀ (n : ℕ) (l : literal), l.2 < n →
      ((List.range n).sublists.filter (fun a => evalCnf a [[l]])).length = 2 ^ (n - 1) :=
  PvsNP.Units.m3_y_models_count_unit.count_aux
