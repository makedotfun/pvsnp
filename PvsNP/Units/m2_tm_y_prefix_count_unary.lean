import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), whose machine combinators come from github.com/open-goat/pequalnp-proofs (formerly
brilliant-hq/pequalnp-proofs) at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License
2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_prefix_count_unary

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := rfl

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : ComputableInPolyTime ea eb f) (heq : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

private def mapTrue (u : List Bool) : List Bool :=
  u.map (fun _ => true)

private theorem cpt_mapTrue :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) mapTrue := by
  refine filterMap_polyTime _ _ _ (fun _ : Bool => some true) ?_
  intro u
  show u.map _ = u.filterMap _
  induction u with
  | nil => rfl
  | cons _ t ih => simp only [List.map_cons, List.filterMap_cons, ih]

private theorem mapTrue_eq_un (u : List Bool) : mapTrue u = un u.length := by
  induction u with
  | nil => rfl
  | cons _ t ih =>
    simp only [mapTrue, List.map_cons, List.length_cons, un, List.replicate_succ] at ih ⊢
    exact congrArg (List.cons true) ih

private theorem unpairB_take (u y : List Bool) :
    (unpairB (mapTrue u ++ false :: y)).1 = y.take u.length := by
  rw [mapTrue_eq_un]
  simp [unpairB, un]

private def keepTrue (x : List Bool) : List Bool :=
  x.filterMap (fun b => if b then some true else none)

private theorem keepTrue_eq_replicate (x : List Bool) :
    keepTrue x = List.replicate (x.count true) true := by
  induction x with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simp only [keepTrue, List.filterMap_cons] at ih ⊢
      have hcnt : (false :: t).count true = t.count true := by simp
      rw [hcnt]
      simpa using ih
    · simp only [keepTrue, List.filterMap_cons] at ih ⊢
      have hcnt : (true :: t).count true = t.count true + 1 := by simp
      rw [hcnt, List.replicate_succ]
      simpa using congrArg (List.cons true) ih

private theorem cpt_keepTrue :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) keepTrue :=
  filterMap_polyTime (fun x : List Bool => x) (fun x : List Bool => x) keepTrue
    (fun b => if b then some true else none) (fun _ => rfl)

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate ((p.2.take p.1.length).count true) true) := by
  rw [← encodePair_eq]
  have hEnc := cpt_app2 (cpt_comp cpt_unpairB1 cpt_mapTrue) (cpt_cons1 false cpt_unpairB2)
  have hTake := cpt_comp hEnc cpt_unpairB1
  have hAll := cpt_comp (cpt_comp cpt_pairB hTake) cpt_keepTrue
  exact cptE' hAll (fun ⟨x, y⟩ => by
    simp only [unpairB_pairB, unpairB_take, keepTrue_eq_replicate])

end PvsNP.Units.m2_tm_y_prefix_count_unary

theorem PvsNP.Units.m2_tm_y_prefix_count_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate ((p.2.take p.1.length).count true) true) :=
  PvsNP.Units.m2_tm_y_prefix_count_unary.main
