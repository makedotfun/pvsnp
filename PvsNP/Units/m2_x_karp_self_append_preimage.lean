import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- The self-append preimage reduces to the language itself: the map `x ↦ x ++ x` is
polynomial-time (append of two copies of the input, via `cpt_app2 cpt_id cpt_id`), and
membership is definitional. -/
theorem PvsNP.Units.m2_x_karp_self_append_preimage :
    ∀ L : Language Bool,
      PvsNP.KarpReducible ({x : List Bool | x ++ x ∈ L} : Language Bool) L := by
  intro L
  refine ⟨fun x => x ++ x, ?_, fun _ => Iff.rfl⟩
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
