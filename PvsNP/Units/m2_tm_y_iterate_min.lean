import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_bit_lookup_polytime

/-- Iterating a length-bounded polynomial-time map as many times as the shorter of two
strings is long takes polynomial time: truncate the second component to the first
component's length (settled `m2_take_drop_length_polytime`), pair it back with the
first component (settled `m2_bit_lookup_polytime.pair_prod`), and run the settled
iteration machine `m2_iterate_polytime` on the truncated pair; the truncation has
length `min |x| |y|` by `List.length_take`. -/
theorem PvsNP.Units.m2_tm_y_iterate_min :
    ∀ (g : List Bool → List Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
        (∀ y : List Bool, (g y).length ≤ y.length + k) →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
            (fun p : List Bool × List Bool => g^[min p.1.length p.2.length] p.1) := by
  intro g k hg hk
  have hFst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) :=
    PvsNP.Units.m2_pair_split_polytime.1
  have hTake : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2.take p.1.length) :=
    PvsNP.Units.m2_take_drop_length_polytime.main.1
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2.take p.1.length)) :=
    PvsNP.Units.m2_bit_lookup_polytime.pair_prod hFst hTake
  have hIter : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => g^[q.2.length] q.1) :=
    PvsNP.Units.m2_iterate_polytime g k hg hk
  have hComp : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      ((fun q : List Bool × List Bool => g^[q.2.length] q.1) ∘
        (fun p : List Bool × List Bool => (p.1, p.2.take p.1.length))) :=
    PvsNP.Units.m2_polytime_comp _ _ _
      (fun p : List Bool × List Bool => (p.1, p.2.take p.1.length))
      (fun q : List Bool × List Bool => g^[q.2.length] q.1) hPair hIter
  have hEq : ((fun q : List Bool × List Bool => g^[q.2.length] q.1) ∘
        (fun p : List Bool × List Bool => (p.1, p.2.take p.1.length))) =
      (fun p : List Bool × List Bool => g^[min p.1.length p.2.length] p.1) := by
    funext p
    simp only [Function.comp_apply, List.length_take]
  rw [← hEq]
  exact hComp
