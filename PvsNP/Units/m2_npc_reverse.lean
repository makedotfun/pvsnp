import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_reverse_closed
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_nphard_transfer

/-!
# m2_npc_reverse: reversing every string of an NP-complete language keeps it NP-complete

In NP: the settled unit `m2_np_reverse_closed`. Hard: `L` reduces to its reversal
by reversal (the settled unit `m2_reverse_polytime` plus `List.reverse_reverse`),
then the settled unit `m2_nphard_transfer`. NP-complete is NP + NP-hard, so both
sides close.
-/

/-- Reversing every string of an NP-complete language keeps it NP-complete (TM2). -/
theorem PvsNP.Units.m2_npc_reverse :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPComplete ({x : List Bool | x.reverse ∈ L} : Language Bool) := by
  intro L hL
  obtain ⟨hNP, hHard⟩ := hL
  refine ⟨PvsNP.Units.m2_np_reverse_closed L hNP, ?_⟩
  apply PvsNP.Units.m2_nphard_transfer L _ hHard
  refine ⟨fun x : List Bool => x.reverse, PvsNP.Units.m2_reverse_polytime, fun x => ?_⟩
  show x ∈ L ↔ (List.reverse x).reverse ∈ L
  rw [List.reverse_reverse]
