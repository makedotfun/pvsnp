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

namespace PvsNP.Units.m2_tm_list_code_head

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def headD : Fin 4 → Bool → Fin 4 × Option Bool
  | ⟨0, _⟩, false => (1, none)
  | ⟨0, _⟩, true  => (2, none)
  | ⟨1, _⟩, false => (0, some false)
  | ⟨1, _⟩, true  => (3, none)
  | ⟨2, _⟩, true  => (0, some true)
  | ⟨2, _⟩, false => (3, none)
  | ⟨3, _⟩, _     => (3, none)

private theorem run_done (t : List Bool) :
    fstRun headD (fun _ => none) 3 t = [] := by
  induction t with
  | nil => rfl
  | cons b t ih => simpa [fstRun, headD] using ih

private theorem run_word (w t : List Bool) :
    fstRun headD (fun _ => none) 0 (w.flatMap (fun b => [b, b]) ++ false :: true :: t) = w := by
  induction w with
  | nil =>
    simp [fstRun, headD, run_done]
  | cons b w ih =>
    cases b <;> simpa [List.flatMap_cons, fstRun, headD] using ih

theorem main :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString
      (fun l : List (List Bool) => l.headD []) := by
  refine fst_polyTime
    (fun l : List (List Bool) =>
      (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
    PvsNP.encodeString
    (fun l : List (List Bool) => l.headD [])
    headD (fun _ => none) 0 (fun l => ?_)
  cases l with
  | nil => rfl
  | cons w rest =>
    change w = fstRun headD (fun _ => none) 0
      ((w.flatMap (fun b => [b, b]) ++ [false, true]) ++
        (rest.map (fun w' => w'.flatMap (fun b => [b, b]) ++ [false, true])).flatten)
    rw [List.append_assoc]
    exact (run_word w _).symm

end PvsNP.Units.m2_tm_list_code_head

theorem PvsNP.Units.m2_tm_list_code_head :
    PvsNP.PolyTimeComputable (fun l : List (List Bool) => (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten) PvsNP.encodeString
      (fun l : List (List Bool) => l.headD []) :=
  PvsNP.Units.m2_tm_list_code_head.main
