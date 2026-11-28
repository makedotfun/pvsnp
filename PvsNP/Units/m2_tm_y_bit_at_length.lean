import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_transducer_any_encoding

namespace PvsNP.Units.m2_tm_y_bit_at_length

def hdF : Option Bool → List Bool → List Bool
  | none, [] => [false]
  | none, b :: _ => [b]
  | some v, _ => [v]

theorem cpt_headD :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => x.headD false) := by
  refine PvsNP.Units.m2_tm_transducer_any_encoding (Option Bool) PvsNP.encodeString PvsNP.encodeAnswer
    (fun x : List Bool => x.headD false)
    (fun q b => (match q with | none => some b | some v => some v, none))
    (fun q => some (q.getD false)) hdF ?_ ?_ none ?_
  · intro q; cases q <;> rfl
  · intro q b l; cases q <;> simp [hdF]
  · intro x; cases x <;> rfl

theorem drop_headD (l : List Bool) (n : ℕ) : (l.drop n).headD false = l.getD n false := by
  induction l generalizing n with
  | nil => simp
  | cons b t ih =>
    cases n with
    | zero => simp
    | succ n => simpa using ih n

end PvsNP.Units.m2_tm_y_bit_at_length

theorem PvsNP.Units.m2_tm_y_bit_at_length :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.2.getD p.1.length false) := by
  have heq : (fun p : List Bool × List Bool => p.2.getD p.1.length false) =
      (fun x : List Bool => x.headD false) ∘ (fun p : List Bool × List Bool => p.2.drop p.1.length) := by
    funext p
    exact (PvsNP.Units.m2_tm_y_bit_at_length.drop_headD p.2 p.1.length).symm
  rw [heq]
  exact PvsNP.Units.m2_polytime_comp _ _ _ _ _
    PvsNP.Units.m2_take_drop_length_polytime.2 PvsNP.Units.m2_tm_y_bit_at_length.cpt_headD
