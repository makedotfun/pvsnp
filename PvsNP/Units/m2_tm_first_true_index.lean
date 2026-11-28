import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

import PvsNP.Units.m2_polytime_comp

/-- Writing the position of the first `true` of a string in unary takes polynomial
time: complement the string bit by bit (a filterMap), then take its leading run
of `true`s (`hd`); the two steps compose. -/
theorem PvsNP.Units.m2_tm_first_true_index :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.takeWhile (fun b : Bool => !b)).length true) := by
  -- The leading run of `true`s in `x.map not` is exactly the unary index.
  have key : ∀ x : List Bool,
      (x.map not).takeWhile id =
        List.replicate (x.takeWhile (fun b : Bool => !b)).length true := by
    intro x
    induction x with
    | nil => rfl
    | cons b l ih =>
      cases b with
      | false =>
        show (true :: (l.map not).takeWhile id) =
          (true :: List.replicate (l.takeWhile (fun b : Bool => !b)).length true)
        exact congrArg (fun t => true :: t) ih
      | true => rfl
  -- Bitwise complement as a filterMap.
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map not) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x.map not)
      (fun b : Bool => some (!b)) (by
        intro a
        induction a with
        | nil => rfl
        | cons b l ih =>
          show (!b) :: l.map not = (!b) :: l.filterMap (fun b : Bool => some (!b))
          exact congrArg (fun t => (!b) :: t) ih)
  -- The leading run of `true`s.
  have hhd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.hd :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_hd
  -- Compose.
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x.map not)
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.hd hmap hhd
  have hfun : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.hd ∘
      fun x : List Bool => x.map not) =
      (fun x : List Bool => List.replicate (x.takeWhile (fun b : Bool => !b)).length true) := by
    funext x
    exact key x
  rwa [hfun] at hcomp
