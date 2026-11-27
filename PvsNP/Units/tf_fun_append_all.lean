import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_append_all

/-- Copy the input, then emit one extra bit `b` at the end. -/
def copyEmit (b : Bool) : Unit → List Bool → List Bool
  | _, [] => [b]
  | _, c :: t => c :: copyEmit b () t

def copyEmitStep (b : Bool) : Unit → Bool → Unit × Option Bool
  | _, c => ((), some c)

def copyEmitEnd (b : Bool) : Unit → Option Bool := fun _ => some b

theorem copyEmit_nil (b : Bool) (q : Unit) :
    copyEmit b q [] = (copyEmitEnd b q).toList := by
  cases q
  rfl

theorem copyEmit_cons (b : Bool) (q : Unit) (c : Bool) (x : List Bool) :
    copyEmit b q (c :: x) =
      (copyEmitStep b q c).2.toList ++ copyEmit b (copyEmitStep b q c).1 x := by
  cases q
  rfl

theorem copyEmit_eq (b : Bool) (x : List Bool) : copyEmit b () x = x ++ [b] := by
  induction x with
  | nil => rfl
  | cons c t ih => simp [copyEmit, ih]

/-- Appending a single bit is polynomial-time computable (one finite-state
transducer step). -/
theorem append_single (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ [b]) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => copyEmit b () x) :=
    PvsNP.Units.m2_transducer_polytime Unit (copyEmitStep b) (copyEmitEnd b)
      (copyEmit b) (copyEmit_nil b) (copyEmit_cons b) ()
  simpa [copyEmit_eq] using h

/-- The identity function, as a transducer that copies its input and emits
nothing at the end. -/
def identF : Unit → List Bool → List Bool
  | _, x => x

def identStep : Unit → Bool → Unit × Option Bool
  | _, c => ((), some c)

def identEnd : Unit → Option Bool := fun _ => none

theorem ident_nil (q : Unit) : identF q [] = (identEnd q).toList := by
  cases q
  rfl

theorem ident_cons (q : Unit) (c : Bool) (x : List Bool) :
    identF q (c :: x) =
      (identStep q c).2.toList ++ identF (identStep q c).1 x := by
  cases q
  rfl

/-- Appending the empty string is the identity, hence polynomial-time. -/
theorem append_none :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ []) := by
  have h : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => identF () x) :=
    PvsNP.Units.m2_transducer_polytime Unit identStep identEnd identF
      ident_nil ident_cons ()
  simpa [identF] using h

/-- Appending any fixed string: induct on the string, appending one bit at a
time and composing. -/
theorem append_all : ∀ w : List Bool,
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ w) := by
  intro w
  induction w with
  | nil => exact append_none
  | cons b w ih =>
    have h1 := append_single b
    have hc := PvsNP.Units.m2_polytime_comp (αΓ := Bool) (βΓ := Bool) (γΓ := Bool)
      (α := List Bool) (β := List Bool) (γ := List Bool)
      PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ [b]) (fun x : List Bool => x ++ w) h1 ih
    have hfun : (fun x : List Bool => x ++ (b :: w)) =
        (fun x : List Bool => x ++ w) ∘ (fun x : List Bool => x ++ [b]) := by
      funext x
      simp [List.append_assoc]
    rw [hfun]
    exact hc

end PvsNP.Units.tf_fun_append_all

theorem PvsNP.Units.tf_fun_append_all :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ w) :=
  PvsNP.Units.tf_fun_append_all.append_all
