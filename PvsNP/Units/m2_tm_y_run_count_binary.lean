import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_unary_to_binary_polytime,
and PvsNP.Units.m2_polytime_comp of github.com/makedotfun/pvsnp (Apache License 2.0), whose
machine combinators come from github.com/open-goat/pequalnp-proofs (formerly
brilliant-hq/pequalnp-proofs) at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License
2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_run_count_binary

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def destutterD : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, some b)
  | some a, b => (some b, if a ≠ b then some b else none)

private theorem run_some (t : List Bool) : ∀ a : Bool,
    a :: fstRun destutterD (fun _ => none) (some a) t = (a :: t).destutter (· ≠ ·) := by
  induction t with
  | nil => intro a; simp [fstRun, List.destutter]
  | cons b rest ih =>
    intro a
    by_cases hab : a = b
    · subst hab
      simp only [fstRun, destutterD, ne_eq, not_true_eq_false, ↓reduceIte, List.destutter_cons_cons]
      exact ih a
    · simp only [fstRun, destutterD, hab, ne_eq, not_false_eq_true, ↓reduceIte,
        List.destutter_cons_cons]
      exact congrArg (List.cons a) (ih b)

private theorem run_destutter (x : List Bool) :
    x.destutter (· ≠ ·) = fstRun destutterD (fun _ => none) none x := by
  cases x with
  | nil => rfl
  | cons a t =>
    simpa [fstRun, destutterD] using (run_some t a).symm

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.destutter (· ≠ ·)).length) := by
  have hD : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.destutter (· ≠ ·)) :=
    fst_polyTime PvsNP.encodeString PvsNP.encodeString _ destutterD (fun _ => none) none run_destutter
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.destutter (· ≠ ·))
    (fun x : List Bool => Nat.bits x.length)
    hD PvsNP.Units.m2_unary_to_binary_polytime

end PvsNP.Units.m2_tm_y_run_count_binary

theorem PvsNP.Units.m2_tm_y_run_count_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.destutter (· ≠ ·)).length) :=
  PvsNP.Units.m2_tm_y_run_count_binary.main
