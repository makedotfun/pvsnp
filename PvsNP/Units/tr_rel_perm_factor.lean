import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.tf_fun_ones_unary

set_option autoImplicit false

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

namespace PvsNP.Units.tr_rel_perm_factor

theorem encodePair_eq : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by funext p; rfl

/-- The pattern: first component of the `pairB`-decoded pair. -/
def pat (q : List Bool × List Bool) : List Bool := (unpairB q.1).1

/-- The text: second component of the `pairB`-decoded pair. -/
def txt (q : List Bool × List Bool) : List Bool := (unpairB q.1).2

/-- The window of `txt` starting at unary offset `q.2`, of length `pat.length`. -/
def window (q : List Bool × List Bool) : List Bool :=
  ((txt q).drop q.2.length).take (pat q).length

/-- The window test: the window is a permutation of the pattern, i.e. same length
and same number of `true`s (for `Bool` lists these two determine the permutation). -/
def windowTest (q : List Bool × List Bool) : Bool :=
  decide ((window q).length ≤ (pat q).length) &&
    decide ((pat q).length ≤ (window q).length) &&
    decide (List.replicate ((window q).count true) true =
      List.replicate ((pat q).count true) true)

/-- The decider: slide the window along the text and take the disjunction. -/
def decider (p : List Bool × List Bool) : Bool :=
  (List.range ((pairB p.1 p.2).length + 1)).any
    (fun i => windowTest (pairB p.1 p.2, List.replicate i true))

theorem pairB_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => pairB p.1 p.2) := by
  rw [← encodePair_eq]; exact cpt_pairB

theorem pat_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString pat :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1) (fun s : List Bool => (unpairB s).1)
    PvsNP.Units.m2_pair_split_polytime.1 cpt_unpairB1

theorem txt_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString txt :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1) (fun s : List Bool => (unpairB s).2)
    PvsNP.Units.m2_pair_split_polytime.1 cpt_unpairB2

theorem drop_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun q : List Bool × List Bool => (txt q).drop q.2.length) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool => (q.2, txt q)) :=
    cpt_pairG PvsNP.Units.m2_pair_split_polytime.2.1 txt_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun q : List Bool × List Bool => (q.2, txt q))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    hpair PvsNP.Units.m2_take_drop_length_polytime.2

theorem window_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString window := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool => (pat q, (txt q).drop q.2.length)) :=
    cpt_pairG pat_poly drop_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun q : List Bool × List Bool => (pat q, (txt q).drop q.2.length))
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    hpair PvsNP.Units.m2_take_drop_length_polytime.1

theorem lenLe1_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool => decide ((window q).length ≤ (pat q).length)) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool => (window q, pat q)) :=
    cpt_pairG window_poly pat_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool => (window q, pat q))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    hpair PvsNP.Units.m2_len_le_polytime

theorem lenLe2_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool => decide ((pat q).length ≤ (window q).length)) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool => (pat q, window q)) :=
    cpt_pairG pat_poly window_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool => (pat q, window q))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    hpair PvsNP.Units.m2_len_le_polytime

theorem ones_window_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun q : List Bool × List Bool => List.replicate ((window q).count true) true) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    window (fun x : List Bool => List.replicate (x.count true) true)
    window_poly PvsNP.Units.tf_fun_ones_unary

theorem ones_pat_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun q : List Bool × List Bool => List.replicate ((pat q).count true) true) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    pat (fun x : List Bool => List.replicate (x.count true) true)
    pat_poly PvsNP.Units.tf_fun_ones_unary

theorem countEq_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool =>
      decide (List.replicate ((window q).count true) true =
        List.replicate ((pat q).count true) true)) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool =>
        (List.replicate ((window q).count true) true,
          List.replicate ((pat q).count true) true)) :=
    cpt_pairG ones_window_poly ones_pat_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun q : List Bool × List Bool =>
      (List.replicate ((window q).count true) true,
        List.replicate ((pat q).count true) true))
    (fun p : List Bool × List Bool => decide (p.1 = p.2))
    hpair PvsNP.Units.m2_eq_polytime

theorem windowTest_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer windowTest := by
  have h12 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun q : List Bool × List Bool =>
        decide ((window q).length ≤ (pat q).length) &&
          decide ((pat q).length ≤ (window q).length)) :=
    PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ lenLe1_poly lenLe2_poly
  have h := PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ h12 countEq_poly
  exact h

theorem decider_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer decider := by
  have hsearch := PvsNP.Units.m2_bounded_unary_search_polytime windowTest windowTest_poly
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => pairB p.1 p.2)
    (fun x : List Bool => (List.range (x.length + 1)).any
      (fun i => windowTest (x, List.replicate i true)))
    pairB_poly hsearch

theorem count_false_add_count_true (l : List Bool) :
    l.count false + l.count true = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b <;> simp <;> omega

theorem perm_of_len_count (w a : List Bool) (hlen : w.length = a.length)
    (hcnt : w.count true = a.count true) : List.Perm w a := by
  rw [List.perm_iff_count]
  intro b
  cases b with
  | false =>
    have hw := count_false_add_count_true w
    have ha := count_false_add_count_true a
    omega
  | true => exact hcnt

theorem window_pairB (p : List Bool × List Bool) (i : ℕ) :
    window (pairB p.1 p.2, List.replicate i true) = (p.2.drop i).take p.1.length := by
  simp [window, txt, pat, unpairB_pairB, List.length_replicate]

theorem pat_pairB (p : List Bool × List Bool) (i : ℕ) :
    pat (pairB p.1 p.2, List.replicate i true) = p.1 := by
  simp [pat, unpairB_pairB]

theorem windowTest_true_iff (q : List Bool × List Bool) :
    windowTest q = true ↔
      (window q).length = (pat q).length ∧ (window q).count true = (pat q).count true := by
  unfold windowTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨le_antisymm h1 h2, ?_⟩
    have h := congrArg List.length h3
    simp only [List.length_replicate] at h
    exact h
  · rintro ⟨hlen, hcnt⟩
    exact ⟨⟨hlen.le, hlen.ge⟩, by rw [hcnt]⟩

theorem decider_true_iff (p : List Bool × List Bool) :
    decider p = true ↔ ∃ y : List Bool, y <:+: p.2 ∧ List.Perm y p.1 := by
  unfold decider
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hV⟩
    have hW := (windowTest_true_iff (pairB p.1 p.2, List.replicate i true)).mp hV
    rw [window_pairB, pat_pairB] at hW
    refine ⟨(p.2.drop i).take p.1.length, ?_, perm_of_len_count _ _ hW.1 hW.2⟩
    refine ⟨p.2.take i, (p.2.drop i).drop p.1.length, ?_⟩
    have h1 : (p.2.drop i).take p.1.length ++
        (p.2.drop i).drop p.1.length = p.2.drop i :=
      List.take_append_drop _ _
    have h2 : p.2.take i ++ p.2.drop i = p.2 := List.take_append_drop i p.2
    rw [List.append_assoc, h1, h2]
  · rintro ⟨y, ⟨s, t, hst⟩, hperm⟩
    have hylen : y.length = p.1.length := hperm.length_eq
    have hcnt : y.count true = p.1.count true := hperm.count_eq true
    have hdrop : p.2.drop s.length = y ++ t := by
      rw [← hst, List.append_assoc, List.drop_left]
    have hwin : window (pairB p.1 p.2, List.replicate s.length true) = y := by
      rw [window_pairB, hdrop, ← hylen, List.take_left]
    have hV : windowTest (pairB p.1 p.2, List.replicate s.length true) = true := by
      rw [windowTest_true_iff, hwin, pat_pairB]
      exact ⟨hylen, hcnt⟩
    refine ⟨s.length, ?_, hV⟩
    rw [List.mem_range]
    have hplen : (pairB p.1 p.2).length = 2 * p.1.length + p.2.length + 1 :=
      pairB_length p.1 p.2
    have hsle : s.length ≤ p.2.length := by
      have h := congrArg List.length hst
      simp only [List.length_append] at h
      omega
    omega

end PvsNP.Units.tr_rel_perm_factor

theorem PvsNP.Units.tr_rel_perm_factor : ∃ f : List Bool × List Bool → Bool,
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
    ∀ p : List Bool × List Bool,
      (∃ y : List Bool, y <:+: p.2 ∧ List.Perm y p.1) ↔ f p = true := by
  refine ⟨PvsNP.Units.tr_rel_perm_factor.decider,
    PvsNP.Units.tr_rel_perm_factor.decider_poly, ?_⟩
  intro p
  exact (PvsNP.Units.tr_rel_perm_factor.decider_true_iff p).symm
