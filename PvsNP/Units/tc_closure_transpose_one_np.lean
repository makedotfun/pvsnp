import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_join_karp_sides

/-
Built on settled units of github.com/makedotfun/pvsnp (Apache License 2.0), which this file
imports: the bounded projection m2_np_projection, the closure lemmas m2_np_inter and
m2_p_subset_np, the length test m2_len_le_polytime, and the polynomial-time pieces
m2_take_drop_length_polytime, m2_pair_split_polytime, m2_tm_pair_fork_polytime,
m2_pair_build_polytime, m2_const_polytime, m2_join_karp_sides and m2_polytime_comp.
The certificate `c` names the swap position `j = (c.drop 2).length`; the swap is
`x.take j ++ [x[j + 1]] ++ [x[j]] ++ x.drop (j + 2)`. The bound `p = X` forces
`j + 1 < x.length` for every certificate in range once `x` has length at least two,
so every certificate gives a genuine adjacent transposition; strings of length under
two are cut out by intersecting with the P-language of strings of length at least two
(the swap is the identity there, so they need the same treatment as the empty string
in the flip-one unit).
-/

namespace PvsNP.Units.tc_closure_transpose_one_np

/-- The swap map: swap the bits at positions `(c.drop 2).length` and `(c.drop 2).length + 1`. -/
def g (p : List Bool × List Bool) : List Bool :=
  p.1.take (p.2.drop 2).length ++
    ((p.1.drop ((p.2.drop 2).length + 1)).take 1 ++
      ((p.1.drop (p.2.drop 2).length).take 1 ++ p.1.drop ((p.2.drop 2).length + 2)))

theorem g_eq (x c : List Bool) : g (x, c) =
    x.take (c.drop 2).length ++
      ((x.drop ((c.drop 2).length + 1)).take 1 ++
        ((x.drop (c.drop 2).length).take 1 ++ x.drop ((c.drop 2).length + 2))) := rfl

/-- The identity is polynomial-time (Mathlib's `idComputableInPolyTime`). -/
theorem hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString id :=
  ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩

/-- Dropping two bits is polynomial-time: take/drop by the length of `[false, false]`. -/
theorem cpt_drop2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun s : List Bool => s.drop 2) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => ([false, false], x))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    (PvsNP.Units.m2_pair_build_polytime (fun _ : List Bool => [false, false]) id
      (PvsNP.Units.m2_const_polytime [false, false]) hid)
    PvsNP.Units.m2_take_drop_length_polytime.2

/-- Taking one bit is polynomial-time: take by the length of `[false]`. -/
theorem cpt_take1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun s : List Bool => s.take 1) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => ([false], x))
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    (PvsNP.Units.m2_pair_build_polytime (fun _ : List Bool => [false]) id
      (PvsNP.Units.m2_const_polytime [false]) hid)
    PvsNP.Units.m2_take_drop_length_polytime.1

theorem cpt_snd_drop2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => p.2.drop 2) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.2)
    (fun s : List Bool => s.drop 2)
    PvsNP.Units.m2_pair_split_polytime.2.1 cpt_drop2

theorem cpt_snd_cons_drop2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => false :: p.2.drop 2) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.2.drop 2)
    (fun x : List Bool => false :: x)
    cpt_snd_drop2
    (PvsNP.Units.m2_join_karp_sides.cpt_cons false)

theorem cpt_snd_cons2_drop2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => false :: false :: p.2.drop 2) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => false :: p.2.drop 2)
    (fun x : List Bool => false :: x)
    cpt_snd_cons_drop2
    (PvsNP.Units.m2_join_karp_sides.cpt_cons false)

theorem cpt_take_j : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.take (p.2.drop 2).length) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.2.drop 2, p.1))
    (fun p : List Bool × List Bool => p.2.take p.1.length)
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_snd_drop2
      PvsNP.Units.m2_pair_split_polytime.1)
    PvsNP.Units.m2_take_drop_length_polytime.1

theorem cpt_drop_j : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.drop (p.2.drop 2).length) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.2.drop 2, p.1))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_snd_drop2
      PvsNP.Units.m2_pair_split_polytime.1)
    PvsNP.Units.m2_take_drop_length_polytime.2

theorem cpt_drop_j1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.drop ((p.2.drop 2).length + 1)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (false :: p.2.drop 2, p.1))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_snd_cons_drop2
      PvsNP.Units.m2_pair_split_polytime.1)
    PvsNP.Units.m2_take_drop_length_polytime.2

theorem cpt_drop_j2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.drop ((p.2.drop 2).length + 2)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (false :: false :: p.2.drop 2, p.1))
    (fun p : List Bool × List Bool => p.2.drop p.1.length)
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_snd_cons2_drop2
      PvsNP.Units.m2_pair_split_polytime.1)
    PvsNP.Units.m2_take_drop_length_polytime.2

theorem cpt_b : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.1.drop ((p.2.drop 2).length + 1)).take 1) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.drop ((p.2.drop 2).length + 1))
    (fun s : List Bool => s.take 1)
    cpt_drop_j1 cpt_take1

theorem cpt_c : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (p.1.drop (p.2.drop 2).length).take 1) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1.drop (p.2.drop 2).length)
    (fun s : List Bool => s.take 1)
    cpt_drop_j cpt_take1

theorem cpt_g : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g := by
  have hCD : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (p.1.drop (p.2.drop 2).length).take 1 ++ p.1.drop ((p.2.drop 2).length + 2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        ((p.1.drop (p.2.drop 2).length).take 1, p.1.drop ((p.2.drop 2).length + 2)))
      (fun p : List Bool × List Bool => p.1 ++ p.2)
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_c cpt_drop_j2)
      PvsNP.Units.m2_pair_split_polytime.2.2
  have hBCD : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        (p.1.drop ((p.2.drop 2).length + 1)).take 1 ++
          ((p.1.drop (p.2.drop 2).length).take 1 ++ p.1.drop ((p.2.drop 2).length + 2))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        ((p.1.drop ((p.2.drop 2).length + 1)).take 1,
          (p.1.drop (p.2.drop 2).length).take 1 ++ p.1.drop ((p.2.drop 2).length + 2)))
      (fun p : List Bool × List Bool => p.1 ++ p.2)
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_b hCD)
      PvsNP.Units.m2_pair_split_polytime.2.2
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      (p.1.take (p.2.drop 2).length,
        (p.1.drop ((p.2.drop 2).length + 1)).take 1 ++
          ((p.1.drop (p.2.drop 2).length).take 1 ++ p.1.drop ((p.2.drop 2).length + 2))))
    (fun p : List Bool × List Bool => p.1 ++ p.2)
    (PvsNP.Units.m2_tm_pair_fork_polytime _ _ cpt_take_j hBCD)
    PvsNP.Units.m2_pair_split_polytime.2.2

/-- The strings of length at least two: the swap needs two adjacent bits. -/
def GE2 : Language Bool := {x | 2 ≤ x.length}

/-- Testing `2 ≤ x.length` is polynomial-time: compare against the length of `[false, false]`. -/
theorem cpt_ge2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
    (fun x : List Bool => decide (2 ≤ x.length)) :=
  PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x : List Bool => ([false, false], x))
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    (PvsNP.Units.m2_pair_build_polytime (fun _ : List Bool => [false, false]) id
      (PvsNP.Units.m2_const_polytime [false, false]) hid)
    PvsNP.Units.m2_len_le_polytime

theorem ge2_mem : GE2 ∈ PvsNP.P := by
  refine ⟨fun x : List Bool => decide (2 ≤ x.length), cpt_ge2, fun x => ?_⟩
  show (2 ≤ x.length) ↔ decide (2 ≤ x.length) = true
  rw [decide_eq_true_iff]

/-- The swap map, written with the two swapped bits exposed. -/
theorem swap_eq (x : List Bool) (j : ℕ) (hj : j + 1 < x.length) :
    x.take j ++ ((x.drop (j + 1)).take 1 ++ ((x.drop j).take 1 ++ x.drop (j + 2))) =
      x.take j ++ x[j + 1] :: x[j] :: x.drop (j + 2) := by
  have h1 : x.drop j = x[j] :: x.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
  have h2 : x.drop (j + 1) = x[j + 1] :: x.drop (j + 2) := List.drop_eq_getElem_cons hj
  rw [h1, h2]
  simp only [List.take_succ_cons, List.take_zero, List.singleton_append]

/-- Splitting a string at a valid swap position. -/
theorem x_eq (x : List Bool) (j : ℕ) (hj : j + 1 < x.length) :
    x = x.take j ++ x[j] :: x[j + 1] :: x.drop (j + 2) := by
  have h1 : x.drop j = x[j] :: x.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
  have h2 : x.drop (j + 1) = x[j + 1] :: x.drop (j + 2) := List.drop_eq_getElem_cons hj
  conv_lhs => rw [← List.take_append_drop j x, h1, h2]

theorem set_eq (L : Language Bool) :
    ({x : List Bool | ∃ (u v : List Bool) (a b : Bool),
        x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L} : Language Bool) =
      ({x : List Bool | ∃ c : List Bool,
        c.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧ g (x, c) ∈ L} :
        Language Bool) ⊓ GE2 := by
  ext x
  simp only [Set.mem_setOf_eq, Polynomial.eval_X]
  constructor
  · rintro ⟨u, v, a, b, rfl, h⟩
    have hlen : (u ++ a :: b :: v).length = u.length + 2 + v.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hlt : u.length + 1 < (u ++ a :: b :: v).length := by
      rw [hlen]
      omega
    have hdrop2 : (List.replicate (u.length + 2) false).drop 2 =
        List.replicate u.length false := by
      have e : List.replicate (u.length + 2) false =
          false :: false :: List.replicate u.length false := by
        rw [show u.length + 2 = (u.length + 1) + 1 from by omega,
          List.replicate_succ, List.replicate_succ]
      rw [e]
      rfl
    have htake : (u ++ a :: b :: v).take u.length = u := List.take_left
    have hget1 : (u ++ a :: b :: v)[u.length] = a := by simp
    have hget2 : (u ++ a :: b :: v)[u.length + 1] = b := by simp
    have hdropv : (u ++ a :: b :: v).drop (u.length + 2) = v := by
      have e : u ++ a :: b :: v = (u ++ [a, b]) ++ v := by simp [List.append_assoc]
      rw [e, ← show (u ++ [a, b]).length = u.length + 2 by simp, List.drop_left]
    have hswap := swap_eq (u ++ a :: b :: v) u.length hlt
    refine ⟨⟨List.replicate (u.length + 2) false, ?_, ?_⟩, ?_⟩
    · rw [List.length_replicate, hlen]
      omega
    · rw [g_eq, hdrop2, List.length_replicate, hswap, htake, hget2, hget1, hdropv]
      exact h
    · show 2 ≤ (u ++ a :: b :: v).length
      rw [hlen]
      omega
  · rintro ⟨⟨c, hc, hg⟩, hge2⟩
    have hn : 2 ≤ x.length := hge2
    have hj : (c.drop 2).length + 1 < x.length := by
      rw [List.length_drop]
      omega
    have hswap := swap_eq x (c.drop 2).length hj
    have hx := x_eq x (c.drop 2).length hj
    refine ⟨x.take (c.drop 2).length, x.drop ((c.drop 2).length + 2),
      x[(c.drop 2).length], x[(c.drop 2).length + 1], hx, ?_⟩
    rw [g_eq, hswap] at hg
    exact hg

end PvsNP.Units.tc_closure_transpose_one_np

/-- NP is closed under swapping two adjacent bits (TM2): guess the swap position as the length
of a certificate, swap, and ask the verifier of `L`. -/
theorem PvsNP.Units.tc_closure_transpose_one_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP → ({x : List Bool | ∃ (u v : List Bool) (a b : Bool), x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_transpose_one_np.set_eq L]
  exact PvsNP.Units.m2_np_inter _ _
    (PvsNP.Units.m2_np_projection L PvsNP.Units.tc_closure_transpose_one_np.g
      Polynomial.X hL PvsNP.Units.tc_closure_transpose_one_np.cpt_g)
    (PvsNP.Units.m2_p_subset_np PvsNP.Units.tc_closure_transpose_one_np.ge2_mem)
