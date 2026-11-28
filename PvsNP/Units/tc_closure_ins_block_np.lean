import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_down_closed

/-!
Closure of `NP` under inserting the block `[true, false]`.

A unary certificate names the position of the block: its length is that position.
The polynomial-time map cuts the two symbols at that position out of the input and
appends them behind the cut, so the output is `cut ++ the two symbols`. Membership
of that output in the marker language `L • [true, false]` (the language of
`NP`-members followed by the block) then says exactly two things: the two symbols
that were cut out really are `[true, false]`, and the cut itself belongs to `L`.

The marker language is in `NP`: by reversal it is the preimage under `reverse` of
`[false, true] • Lᵛ` (block-prefixed strings whose tail tail reverses into `L`),
which is an intersection of a bounded projection with a `P` prefix language.

This proves only the posted closure statement in PvsNP.Defs.
-/

namespace PvsNP.Units.tc_closure_ins_block_np

/-- Take the first two symbols of a string (zero, one or two of them). -/
theorem cpt_takeTwo :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.take 2) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => ([true, false], x))
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    (PvsNP.Units.m2_pair_build_polytime.cpt_pair
      (PvsNP.Units.m2_const_polytime [true, false])
      PvsNP.Units.m2_pair_build_polytime.cpt_id)
    PvsNP.Units.m2_take_drop_length_polytime.1

/-- `y = y.take 2 ++ y.tail.tail`. -/
theorem take_two_append_tail_tail (y : List Bool) :
    y = y.take 2 ++ y.tail.tail := by
  match y with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => rfl

/-- A list of length at most one is its own two-symbol prefix. -/
theorem take_two_short (y : List Bool) (h : y.length ≤ 1) : y.take 2 = y := by
  match y with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => exact absurd h (by simp only [List.length_cons]; omega)

/-- A list of length at most one has empty tail tail. -/
theorem tail_tail_short (y : List Bool) (h : y.length ≤ 1) : y.tail.tail = [] := by
  match y with
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => exact absurd h (by simp only [List.length_cons]; omega)

/-- The string with the two symbols at the certified position cut out. -/
def del (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ (p.1.drop p.2.length).tail.tail

/-- The cut, followed by the two symbols that were cut out. -/
def cand (p : List Bool × List Bool) : List Bool :=
  del p ++ (p.1.drop p.2.length).take 2

theorem cand_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString cand := by
  have htake : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime
      PvsNP.Units.m2_take_drop_length_polytime.1
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime
      PvsNP.Units.m2_take_drop_length_polytime.2
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => s.tail) :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.cpt_tail
  have hd2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1.drop p.2.length).tail.tail) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      (PvsNP.Units.m2_polytime_comp _ _ _ _ _ hdrop htail) htail
  have hdel : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString del :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ htake hd2)
      PvsNP.Units.m2_pair_build_polytime.cpt_append
  have ha2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1.drop p.2.length).take 2) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ hdrop cpt_takeTwo
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ hdel ha2)
    PvsNP.Units.m2_pair_build_polytime.cpt_append

/-- Fixed prefix languages are in `P`. -/
theorem pre_in_P (u : List Bool) : ({x : List Bool | u <+: x} : Language Bool) ∈ PvsNP.P := by
  refine ⟨fun x : List Bool => u.isPrefixOf x, ?_, fun x => ?_⟩
  · have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun x : List Bool => (u, x)) :=
      PvsNP.Units.m2_pair_build_polytime.cpt_pair (PvsNP.Units.m2_const_polytime u)
        PvsNP.Units.m2_pair_build_polytime.cpt_id
    have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeAnswer (fun x : List Bool => (u, x))
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2) hpair
      PvsNP.Units.m2_prefix_polytime
    have hfun : ((fun p : List Bool × List Bool => p.1.isPrefixOf p.2) ∘
        (fun x : List Bool => (u, x))) = (fun x : List Bool => u.isPrefixOf x) := by
      funext x
      rfl
    rw [hfun] at h
    exact h
  · exact List.isPrefixOf_iff_prefix.symm

theorem pre_in_np (u : List Bool) : ({x : List Bool | u <+: x} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_p_subset_np (pre_in_P u)

/-- Dropping two symbols and reversing is a bounded projection of `L`. -/
theorem dropTwo_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    ({v : List Bool | v.tail.tail.reverse ∈ L} : Language Bool) ∈ PvsNP.NP := by
  have hfirst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) :=
    PvsNP.Units.m2_pair_build_polytime.polytime_fst
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => s.tail) :=
    PvsNP.Units.m2_np_projection.PEqualNP.Library.Universal.cpt_tail
  have hrev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => s.reverse) := PvsNP.Units.m2_reverse_polytime
  have hfun : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.tail.tail.reverse) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      (PvsNP.Units.m2_polytime_comp _ _ _ _ _
        (PvsNP.Units.m2_polytime_comp _ _ _ _ _ hfirst htail) htail) hrev
  have h := PvsNP.Units.m2_np_projection L
    (fun p : List Bool × List Bool => p.1.tail.tail.reverse) Polynomial.X hL hfun
  have hset : ({x : List Bool | ∃ c : List Bool, c.length ≤ (Polynomial.X).eval x.length ∧
      (fun p : List Bool × List Bool => p.1.tail.tail.reverse) (x, c) ∈ L} : Language Bool)
      = {v : List Bool | v.tail.tail.reverse ∈ L} := by
    ext x
    constructor
    · rintro ⟨c, _, hc⟩
      exact hc
    · intro hx
      exact ⟨[], by simp [Polynomial.eval_X], hx⟩
  rw [hset] at h
  exact h

/-- Block-prefixed strings whose tail tail reverses into `L` are in `NP`. -/
theorem pset_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    ({v : List Bool | ∃ q : List Bool, q.reverse ∈ L ∧ v = [false, true] ++ q} :
      Language Bool) ∈ PvsNP.NP := by
  have hpre := pre_in_np [false, true]
  have hdrop := dropTwo_in_np L hL
  have hset : ({v : List Bool | ∃ q : List Bool, q.reverse ∈ L ∧ v = [false, true] ++ q} :
      Language Bool) =
      ({v : List Bool | v.tail.tail.reverse ∈ L} ⊓ {v : List Bool | [false, true] <+: v}) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ⟨q, rfl⟩⟩
      show ([false, true] ++ q).tail.tail.reverse ∈ L
      rw [show ([false, true] ++ q) = false :: true :: q from rfl]
      simpa using hq
    · rintro ⟨h1, ⟨q, rfl⟩⟩
      exact ⟨q, by simpa using h1, rfl⟩
  rw [hset]
  exact PvsNP.Units.m2_np_inter _ _ hdrop hpre

/-- `L` followed by the block `[true, false]`. -/
def dot (L : Language Bool) : Language Bool :=
  {w | ∃ z : List Bool, z ∈ L ∧ w = z ++ [true, false]}

/-- The marker language is in `NP`: reversal turns it into a block-prefixed language. -/
theorem dot_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) : dot L ∈ PvsNP.NP := by
  have hpset := pset_in_np L hL
  have hred : PvsNP.KarpReducible (dot L)
      {v : List Bool | ∃ q : List Bool, q.reverse ∈ L ∧ v = [false, true] ++ q} := by
    refine ⟨fun w : List Bool => w.reverse, PvsNP.Units.m2_reverse_polytime, ?_⟩
    intro w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.reverse, by simpa using hz, ?_⟩
      simp
    · rintro ⟨q, hq, hw⟩
      refine ⟨q.reverse, hq, ?_⟩
      have := congrArg List.reverse hw
      simpa using this
  exact PvsNP.Units.m2_np_down_closed _ _ hred hpset

/-- The candidate language: cut at the certified position and check the markers. -/
def one (L : Language Bool) : Language Bool :=
  {x | ∃ c : List Bool, c.length ≤ x.length ∧ cand (x, c) ∈ dot L}

theorem one_in_np (L : Language Bool) (hL : L ∈ PvsNP.NP) : one L ∈ PvsNP.NP := by
  have hd := dot_in_np L hL
  simpa only [one, Language, Polynomial.eval_X] using
    (PvsNP.Units.m2_np_projection (dot L) cand Polynomial.X hd cand_polytime)

/-- Cutting the block out and appending it gives the cut followed by the block. -/
theorem cand_block (u v c : List Bool) (hc : c.length = u.length) :
    cand (u ++ [true, false] ++ v, c) = (u ++ v) ++ [true, false] := by
  have hx : u ++ [true, false] ++ v = u ++ ([true, false] ++ v) :=
    List.append_assoc u [true, false] v
  simp only [cand, del, hx, hc, List.take_left, List.drop_left]
  rw [show ([true, false] ++ v).tail.tail = v from rfl,
    show ([true, false] ++ v).take 2 = [true, false] from rfl]

theorem ins_eq (L : Language Bool) :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L} :
      Language Bool) = one L := by
  ext x
  constructor
  · rintro ⟨u, v, hx, hm⟩
    subst hx
    refine ⟨List.replicate u.length false, ?_, ?_⟩
    · simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil]
      omega
    · refine ⟨u ++ v, hm, ?_⟩
      exact cand_block u v (List.replicate u.length false) (by simp)
  · rintro ⟨c, hc, z, hz, hw⟩
    have hxy : x = x.take c.length ++ x.drop c.length :=
      (List.take_append_drop c.length x).symm
    have hcand : cand (x, c) =
        (x.take c.length ++ (x.drop c.length).tail.tail) ++ (x.drop c.length).take 2 := rfl
    by_cases hlen : 2 ≤ (x.drop c.length).length
    · have hBlen : ((x.drop c.length).take 2).length = 2 := by
        rw [List.length_take, Nat.min_eq_left hlen]
      have hzlen : z.length = (x.take c.length ++ (x.drop c.length).tail.tail).length := by
        have h1 : ((x.take c.length ++ (x.drop c.length).tail.tail) ++
            (x.drop c.length).take 2).length = (z ++ [true, false]).length := by
          rw [← hcand, hw]
        have htf : ([true, false] : List Bool).length = 2 := by simp
        simp only [List.length_append] at h1 ⊢
        omega
      have hB : (x.drop c.length).take 2 = [true, false] := by
        have h1 : ((z ++ [true, false]) : List Bool).drop z.length = [true, false] :=
          List.drop_left
        rw [← hw, hcand, hzlen, List.drop_left] at h1
        exact h1
      have hz' : z = x.take c.length ++ (x.drop c.length).tail.tail := by
        have h2 : ((z ++ [true, false]) : List Bool).take z.length = z := List.take_left
        rw [← hw, hcand, hzlen, List.take_left] at h2
        exact h2.symm
      refine ⟨x.take c.length, (x.drop c.length).tail.tail, ?_, ?_⟩
      · calc x = x.take c.length ++ x.drop c.length := hxy
          _ = x.take c.length ++ ((x.drop c.length).take 2 ++ (x.drop c.length).tail.tail) :=
            congrArg (fun t => x.take c.length ++ t)
              (take_two_append_tail_tail (x.drop c.length))
          _ = x.take c.length ++ ([true, false] ++ (x.drop c.length).tail.tail) :=
            congrArg (fun t => x.take c.length ++ (t ++ (x.drop c.length).tail.tail)) hB
          _ = (x.take c.length ++ [true, false]) ++ (x.drop c.length).tail.tail :=
            (List.append_assoc _ _ _).symm
      · rw [hz'] at hz
        exact hz
    · have hshort : (x.drop c.length).length ≤ 1 := by omega
      have hA : (x.drop c.length).tail.tail = [] := tail_tail_short _ hshort
      have hB : (x.drop c.length).take 2 = x.drop c.length := take_two_short _ hshort
      have hcx : cand (x, c) = x := by
        calc cand (x, c) = (x.take c.length ++ (x.drop c.length).tail.tail) ++
              (x.drop c.length).take 2 := hcand
          _ = (x.take c.length ++ []) ++ x.drop c.length := by rw [hA, hB]
          _ = x := by
            rw [List.append_nil]
            exact hxy.symm
      refine ⟨z, [], ?_, ?_⟩
      · rw [List.append_nil]
        exact hcx.symm.trans hw
      · simpa using hz

end PvsNP.Units.tc_closure_ins_block_np

/-- NP is closed under inserting the block `[true, false]` (TM2). -/
theorem PvsNP.Units.tc_closure_ins_block_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ u v : List Bool, x = u ++ [true, false] ++ v ∧ u ++ v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_ins_block_np.ins_eq]
  exact PvsNP.Units.tc_closure_ins_block_np.one_in_np L hL
