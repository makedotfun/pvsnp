import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tf_fun_rotate_count

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem ptc_of_eq {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f g : α → β}
    (h : PvsNP.PolyTimeComputable ea eb f) (heq : f = g) :
    PvsNP.PolyTimeComputable ea eb g := by
  subst heq
  exact h

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

def rotD : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some a, b => (some a, some b)

def rotFin : Option Bool → Option Bool
  | none => none
  | some a => some a

theorem fstRun_rot_some (a : Bool) : ∀ xs : List Bool,
    fstRun rotD rotFin (some a) xs = xs ++ [a]
  | [] => rfl
  | b :: xs => by
    simp only [fstRun, rotD, Option.toList_some, List.cons_append]
    exact congrArg (List.cons b) (fstRun_rot_some a xs)

theorem rot1_eq_fstRun (x : List Bool) :
    x.rotate 1 = fstRun rotD rotFin none x := by
  cases x with
  | nil => rfl
  | cons a xs =>
    simp only [fstRun, rotD, Option.toList_none, List.nil_append, fstRun_rot_some]
    rw [List.rotate_cons_succ, List.rotate_zero]

theorem rot1_poly :
    PvsNP.PolyTimeComputable (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.rotate 1) :=
  fst_polyTime _ _ _ rotD rotFin none rot1_eq_fstRun

theorem rot1_iter : ∀ (k : ℕ) (x : List Bool),
    ((fun s : List Bool => s.rotate 1)^[k] x) = x.rotate k
  | 0, x => by simp
  | k + 1, x => by
    rw [Function.iterate_succ_apply', rot1_iter k x, List.rotate_rotate]

def truesOf (x : List Bool) : List Bool :=
  x.filterMap (fun b => if b then some true else none)

theorem truesOf_poly :
    PvsNP.PolyTimeComputable (fun x : List Bool => x) (fun x : List Bool => x) truesOf :=
  filterMap_polyTime _ _ _ (fun b => if b then some true else none) (fun _ => rfl)

theorem truesOf_length : ∀ x : List Bool, (truesOf x).length = x.count true
  | [] => rfl
  | b :: xs => by
    have ih := truesOf_length xs
    cases b
    · simp only [truesOf, List.filterMap_cons, Bool.false_eq_true, ↓reduceIte] at ih ⊢
      rw [List.count_cons_of_ne (by decide)]
      exact ih
    · simp only [truesOf, List.filterMap_cons, ↓reduceIte, List.length_cons] at ih ⊢
      rw [List.count_cons_self]
      omega

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate (x.count true)) := by
  obtain ⟨c⟩ := rot1_poly
  have hI : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (fun s : List Bool => s.rotate 1)^[p.2.length] p.1) := by
    rw [← encodePair_eq]
    exact Iter.iter_polyTime (fun s : List Bool => s.rotate 1) c 0
      (fun y => by simp)
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, truesOf x)) := by
    rw [← encodePair_eq]
    exact cpt_pair cpt_id truesOf_poly
  have hc := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (x, truesOf x))
    (fun p : List Bool × List Bool => (fun s : List Bool => s.rotate 1)^[p.2.length] p.1)
    hpair hI
  exact ptc_of_eq hc (by
    funext x
    dsimp only [Function.comp_apply]
    rw [truesOf_length, rot1_iter])

end PvsNP.Units.tf_fun_rotate_count

theorem PvsNP.Units.tf_fun_rotate_count :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.rotate (x.count true)) :=
  PvsNP.Units.tf_fun_rotate_count.main
