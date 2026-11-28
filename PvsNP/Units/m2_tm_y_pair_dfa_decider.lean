import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_transducer_any_encoding

set_option autoImplicit false

/-- A finite automaton run on the written pair gives a polynomial-time test of pairs (TM2):
the DFA is the transducer of the settled unit `m2_tm_transducer_any_encoding` with
`δ' q s = (δ q s, none)`, `fin q = some (F q)` and `F' q l = [F (l.foldl δ q)]`. -/
theorem PvsNP.Units.m2_tm_y_pair_dfa_decider :
    ∀ (Q : Type) [Fintype Q] (δ : Q → Bool ⊕ Bool → Q) (q₀ : Q) (F : Q → Bool),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => F ((PvsNP.encodePair p).foldl δ q₀)) := by
  intro Q _ δ q₀ F
  exact PvsNP.Units.m2_tm_transducer_any_encoding
    (Q := Q) (ea := PvsNP.encodePair) (eb := PvsNP.encodeAnswer)
    (f := fun p : List Bool × List Bool => F ((PvsNP.encodePair p).foldl δ q₀))
    (δ := fun q s => (δ q s, none)) (fin := fun q => some (F q))
    (F := fun q l => [F (l.foldl δ q)])
    (fun q => rfl)
    (fun q s l => rfl)
    q₀
    (fun a => rfl)
