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

namespace PvsNP.Units.m2_tm_list_code_flatten

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def flatD : Fin 3 → Bool → Fin 3 × Option Bool
  | ⟨0, _⟩, false => (1, none)
  | ⟨0, _⟩, true  => (2, none)
  | ⟨1, _⟩, false => (0, some false)
  | ⟨1, _⟩, true  => (0, none)
  | ⟨2, _⟩, true  => (0, some true)
  | ⟨2, _⟩, false => (0, none)

private theorem run_word (w t : List Bool) :
    fstRun flatD (fun _ => none) 0 (w.flatMap (fun b => [b, b]) ++ false :: true :: t) =
      w ++ fstRun flatD (fun _ => none) 0 t := by
  induction w with
  | nil =>
    simp [fstRun, flatD]
  | cons b w ih =>
    cases b <;> simpa [List.flatMap_cons, fstRun, flatD] using ih

theorem main :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString
      (fun l : List (List Bool) => l.flatten) := by
  refine fst_polyTime
    (fun l : List (List Bool) =>
      (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
    PvsNP.encodeString
    (fun l : List (List Bool) => l.flatten)
    flatD (fun _ => none) 0 (fun l => ?_)
  induction l with
  | nil => rfl
  | cons w rest ih =>
    change w ++ rest.flatten = fstRun flatD (fun _ => none) 0
      ((w.flatMap (fun b => [b, b]) ++ [false, true]) ++
        (rest.map (fun w' => w'.flatMap (fun b => [b, b]) ++ [false, true])).flatten)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [run_word, ← ih]
    rfl

end PvsNP.Units.m2_tm_list_code_flatten

theorem PvsNP.Units.m2_tm_list_code_flatten :
    PvsNP.PolyTimeComputable (fun l : List (List Bool) => (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten) PvsNP.encodeString
      (fun l : List (List Bool) => l.flatten) :=
  PvsNP.Units.m2_tm_list_code_flatten.main
