import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
A file for the unit tf_fun_append, staged by the ONAR lane. Appending a fixed
two-bit string at the end of the input is the constant-append combinator of
lean/PEqualNP/Library/Universal.lean (Apache License 2.0) of
github.com/brilliant-hq/pequalnp-proofs, the way the settled unit
m2_join_karp_sides of github.com/makedotfun/pvsnp (Apache License 2.0) applies
it; nothing is copied, the settled unit is only the reference.
-/

set_option autoImplicit false

/-- Appending `[true, false]` at the end of a string is polynomial-time. -/
theorem PvsNP.Units.tf_fun_append :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ [true, false]) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [true, false])
