import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_unary_monus
import PvsNP.Units.m2_unary_to_binary_polytime

set_option autoImplicit false

/-
Composes three settled units of github.com/makedotfun/pvsnp:
- `PvsNP.Units.m2_tm_unary_monus`: the truncated difference of the two lengths, in unary
  (`List.replicate (p.1.length - p.2.length) true`).
- `PvsNP.Units.m2_unary_to_binary_polytime`: the length of a list, in binary (`Nat.bits`).
- `PvsNP.Units.m2_polytime_comp`: polynomial-time functions compose.
The composite is `Nat.bits (p.1.length - p.2.length)` since
`List.length_replicate : (List.replicate n a).length = n`.
-/

theorem PvsNP.Units.m2_tm_y_binary_lengths_monus :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (p.1.length - p.2.length)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
    PvsNP.encodeString
    (fun p : List Bool × List Bool => List.replicate (p.1.length - p.2.length) true)
    (fun x : List Bool => Nat.bits x.length)
    PvsNP.Units.m2_tm_unary_monus PvsNP.Units.m2_unary_to_binary_polytime
  convert h using 1
  funext p
  simp only [Function.comp, List.length_replicate]
