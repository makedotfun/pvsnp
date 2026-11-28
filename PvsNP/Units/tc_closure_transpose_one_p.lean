import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime

/-
Original proof for the make.fun desk campaign `pvsnp`, unit
`tc_closure_transpose_one_p`: P is closed under swapping two adjacent bits (TM2).

Proof idea: `x` is a one-transposition of a string of `L` exactly when some
swap position `i` (with `i + 1 < |x|`) has the swapped string in `L`. The
swap at `i` is `x.take i ++ swapFirstTwo (x.drop i)`, where `swapFirstTwo`
swaps the first two bits; it is polynomial-time as a four-state transducer
(one bit of delay, the first bit is emitted at the end if there is no second
bit). The test "position `i` is valid and the swapped string is in `L`" is
polynomial-time (take/drop from the settled `m2_take_drop_length_polytime`,
the tail test from the settled `cpt_tail1`, Boolean combination from the
settled `m2_tm_pair_bool_combine`), so the bounded unary search over the
positions (settled `m2_bounded_unary_search_polytime`) decides the language.
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_transpose_one_p

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodeString_eq : PvsNP.encodeString = (fun xs : List Bool => xs) := by
  funext xs
  simp [PvsNP.encodeString, Computability.encodingList]

theorem encodePair_eq : PvsNP.encodePair =
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

theorem nonempty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun xs : List Bool => !xs.isEmpty) := by
  have run : ∀ (q : Bool) (xs : List Bool),
      fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
        (fun q => some q) q xs = [q || !xs.isEmpty] := by
    intro q xs
    induction xs generalizing q with
    | nil => simp [fstRun]
    | cons b xs ih => simp [fstRun, ih]
  refine fst_polyTime PvsNP.encodeString PvsNP.encodeAnswer _
    (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false ?_
  intro xs
  simpa [encodeString_eq, PvsNP.encodeAnswer, Computability.encodeBool] using
    (run false xs).symm

/-- Swap the first two bits of a list; a list of length `< 2` is unchanged. -/
def swapFirstTwo : List Bool → List Bool
  | [] => []
  | a :: [] => [a]
  | a :: b :: xs => b :: a :: xs

/-- The transducer for `swapFirstTwo`. States are `(pending, phase)`: `phase =
false` means we have not yet seen the second bit (`pending` holds the first
bit, if any); `phase = true` means the first two bits are consumed and
`pending` is the bit still owed to the output. -/
def swapδ : Option Bool × Bool → Bool → (Option Bool × Bool) × Option Bool
  | (none, false), a => ((some a, false), none)
  | (some a, false), b => ((some a, true), some b)
  | (some a, true), c => ((some c, true), some a)
  | (none, true), c => ((none, true), some c)

def swapFin : Option Bool × Bool → Option Bool
  | (some a, _) => some a
  | (none, _) => none

def swapF : Option Bool × Bool → List Bool → List Bool
  | (none, false), xs => swapFirstTwo xs
  | (some a, false), [] => [a]
  | (some a, false), b :: xs => b :: a :: xs
  | (some a, true), xs => a :: xs
  | (none, true), xs => xs

theorem swapFirstTwo_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString swapFirstTwo := by
  have h0 : ∀ q : Option Bool × Bool, swapF q [] = (swapFin q).toList := by
    intro q
    obtain ⟨o, fl⟩ := q
    cases o <;> cases fl <;> rfl
  have h1 : ∀ (q : Option Bool × Bool) (b : Bool) (x : List Bool),
      swapF q (b :: x) = (swapδ q b).2.toList ++ swapF (swapδ q b).1 x := by
    intro q b x
    obtain ⟨o, fl⟩ := q
    cases o <;> cases fl <;> cases x <;> rfl
  exact PvsNP.Units.m2_transducer_polytime _ swapδ swapFin swapF h0 h1 (none, false)

theorem pieces_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1.take p.2.length) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1.drop p.2.length) := by
  exact ⟨cpt_comp cpt_swap PvsNP.Units.m2_take_drop_length_polytime.1,
    cpt_comp cpt_swap PvsNP.Units.m2_take_drop_length_polytime.2⟩

/-- The string obtained from `x` by swapping the bits at positions `|c|` and
`|c| + 1`, from the pair `(x, c)`. -/
def swapAt (p : List Bool × List Bool) : List Bool :=
  p.1.take p.2.length ++ swapFirstTwo (p.1.drop p.2.length)

theorem swapAt_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString swapAt := by
  have ht := cpt_comp cpt_unpairB pieces_poly.1
  have hd := cpt_comp cpt_unpairB pieces_poly.2
  have hs := cpt_comp hd swapFirstTwo_poly
  have h := cpt_comp cpt_pairB (cpt_app2 ht hs)
  change PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      p.1.take p.2.length ++ swapFirstTwo (p.1.drop p.2.length))
  simpa only [unpairB_pairB, encodeString_eq, encodePair_eq, PvsNP.PolyTimeComputable,
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime] using h

/-- The tail of `x.drop i` is polynomial-time: the drop is (settled
`m2_take_drop_length_polytime`), the tail is the settled `cpt_tail1`, and the
two notions of polynomial-time computability agree after unfolding (the
encodings are rewritten by `encodeString_eq`). -/
theorem drop_tail_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (p.1.drop p.2.length).tail) := by
  have hdrop' : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => p.1.drop p.2.length) := by
    simpa only [encodeString_eq, PvsNP.PolyTimeComputable,
      PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime] using pieces_poly.2
  have htail' : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => (p.1.drop p.2.length).tail) :=
    cpt_comp hdrop' (cpt_tail1 cpt_id)
  simpa only [encodeString_eq, PvsNP.PolyTimeComputable,
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime] using htail'

/-- The test at position `|c|`: the position is valid (`i + 1 < |x|`, i.e. the
drop has at least two bits) and the swapped string is accepted by `f`. -/
def test (f : List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  (!(p.1.drop p.2.length).isEmpty && !((p.1.drop p.2.length).tail).isEmpty) &&
    f (swapAt p)

theorem test_poly (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (test f) := by
  have hne1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => !(p.1.drop p.2.length).isEmpty) :=
    cpt_comp (f := fun p : List Bool × List Bool => p.1.drop p.2.length)
      (g := fun xs : List Bool => !xs.isEmpty) pieces_poly.2 nonempty_poly
  have hne2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => !((p.1.drop p.2.length).tail).isEmpty) :=
    cpt_comp (f := fun p : List Bool × List Bool => (p.1.drop p.2.length).tail)
      (g := fun xs : List Bool => !xs.isEmpty) drop_tail_poly nonempty_poly
  have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        !(p.1.drop p.2.length).isEmpty && !((p.1.drop p.2.length).tail).isEmpty) :=
    PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ hne1 hne2
  have hm : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => f (swapAt p)) := cpt_comp swapAt_poly hf
  exact PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b) _ _ hg hm

theorem search_correct (L : Language Bool) (f : List Bool → Bool)
    (hf : ∀ x : List Bool, x ∈ L ↔ f x = true) (x : List Bool) :
    (∃ (u v : List Bool) (a b : Bool), x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L) ↔
      (List.range (x.length + 1)).any (fun i => test f (x, List.replicate i true)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, v, a, b, rfl, h⟩
    refine ⟨u.length, List.mem_range.mpr (by simp), ?_⟩
    simpa [test, swapAt, swapFirstTwo, List.take_append, List.drop_append] using (hf _).mp h
  · rintro ⟨i, _, h⟩
    cases hd : x.drop i with
    | nil => simp [test, hd] at h
    | cons a rest =>
      cases rest with
      | nil => simp [test, hd] at h
      | cons b v =>
        refine ⟨x.take i, v, a, b, ?_, ?_⟩
        · simpa only [hd] using (List.take_append_drop i x).symm
        · apply (hf _).mpr
          simpa [test, swapAt, swapFirstTwo, hd] using h

end PvsNP.Units.tc_closure_transpose_one_p

/-- P is closed under swapping two adjacent bits (TM2): `x` is a one-transposition
of a string of `L` exactly when some swap position `i` (with `i + 1 < |x|`)
has the swapped string in `L`; the swap is polynomial-time (a four-state
transducer), so the bounded search over the positions
(settled `m2_bounded_unary_search_polytime`) decides it. -/
theorem PvsNP.Units.tc_closure_transpose_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ (u v : List Bool) (a b : Bool),
        x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  rcases hL with ⟨f, hpoly, hcorrect⟩
  refine ⟨_, PvsNP.Units.m2_bounded_unary_search_polytime _
    (PvsNP.Units.tc_closure_transpose_one_p.test_poly f hpoly), ?_⟩
  intro x
  exact PvsNP.Units.tc_closure_transpose_one_p.search_correct L f hcorrect x
