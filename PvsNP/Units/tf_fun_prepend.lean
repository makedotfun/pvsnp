import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
A file for the unit tf_fun_prepend, staged by the ONAR lane. Writing a fixed
two-bit string in front of the input is the constant-append combinator of
lean/PEqualNP/Library/Universal.lean (Apache License 2.0) of
github.com/brilliant-hq/pequalnp-proofs, the way the settled unit
m2_join_karp_sides of github.com/makedotfun/pvsnp (Apache License 2.0) applies
it; nothing is copied, the settled unit is only the reference.
-/

set_option autoImplicit false

/-- Writing `[true, false]` in front of a string is polynomial-time. -/
theorem PvsNP.Units.tf_fun_prepend :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => [true, false] ++ x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [true, false])
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
