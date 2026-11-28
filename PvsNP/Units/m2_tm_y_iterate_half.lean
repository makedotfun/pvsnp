import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_unary_div_const

/-
m2_tm_y_iterate_half: iterating a length-bounded polynomial-time map half as
many times as the input is long takes polynomial time (TM2). Pair `x` with
`1^⌊|x|/2⌋` (the settled unit `m2_pair_build_polytime`, Mathlib's
`Turing.idComputableInPolyTime` for the identity and the settled unit
`m2_tm_unary_div_const` at `k = 2` for the clock), then run the settled unit
`m2_iterate_polytime`; the clock's length is `x.length / 2` by
`List.length_replicate`, and the two stages are composed by the settled unit
`m2_polytime_comp`.
-/

set_option autoImplicit false

theorem PvsNP.Units.m2_tm_y_iterate_half :
    ∀ (g : List Bool → List Bool) (k : ℕ), PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
  (∀ y : List Bool, (g y).length ≤ y.length + k) →
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => g^[x.length / 2] x) := by
  intro g k hg hk
  have hClock : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length / 2) true) :=
    PvsNP.Units.m2_tm_unary_div_const 2
  have hId : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hPair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, List.replicate (x.length / 2) true)) :=
    PvsNP.Units.m2_pair_build_polytime id
      (fun x : List Bool => List.replicate (x.length / 2) true) hId hClock
  have hIter : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => g^[p.2.length] p.1) :=
    PvsNP.Units.m2_iterate_polytime g k hg hk
  have hComp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      ((fun p : List Bool × List Bool => g^[p.2.length] p.1) ∘
        (fun x : List Bool => (x, List.replicate (x.length / 2) true))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (x, List.replicate (x.length / 2) true))
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)
      hPair hIter
  have hEq : ((fun p : List Bool × List Bool => g^[p.2.length] p.1) ∘
        (fun x : List Bool => (x, List.replicate (x.length / 2) true))) =
      (fun x : List Bool => g^[x.length / 2] x) := by
    funext x
    simp [List.length_replicate]
  rw [← hEq]
  exact hComp
