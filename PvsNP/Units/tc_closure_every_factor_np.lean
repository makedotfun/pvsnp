import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_all_prefixes
import PvsNP.Units.tc_closure_every_suffix_np

/-!
# tc_closure_every_factor_np: NP is closed under "every factor is in L"

Composition of two settled units of github.com/makedotfun/pvsnp
(Apache License 2.0), which this file imports:

* `tc_closure_every_suffix_np`: if `L ∈ NP`, the language of strings whose
  suffixes (`y <:+ x`) all belong to `L` is in `NP`;
* `m2_np_all_prefixes`: if `L ∈ NP`, the language of strings whose prefixes
  (`y <+: x`) all belong to `L` is in `NP`.

A factor (`y <:+: x`) is exactly a prefix of a suffix, so applying the suffix
closure first and the prefix closure second gives the factor closure; the
only new work is that set equality, proved below from the existential
characterisations of `List.IsPrefix`, `List.IsSuffix` and `List.IsInfix`.

Verified by hand, line by line, against the settled statements (no lease is
held for this unit, so `desk check --build` could not be run).
-/

namespace PvsNP.Units.tc_closure_every_factor_np

/-- The factor closure of `L` is the prefix closure of the suffix closure:
`y` is a factor of `x` iff `y` is a prefix of some suffix of `x`. -/
theorem set_eq (L : Language Bool) :
    ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) =
      {x : List Bool | ∀ z : List Bool, z <+: x →
        ∀ y : List Bool, y <:+ z → y ∈ L} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Every prefix of every suffix of `x` is a factor of `x`:
    -- `y <:+ z` gives `y ++ b = z` and `z <+: x` gives `a ++ z = x`,
    -- hence `a ++ y ++ b = x`.
    intro h z hz y hy
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hy
    exact h y ⟨a, b, by rw [← ha, ← hb, List.append_assoc]⟩
  · -- Every factor `y` of `x`, say `a ++ y ++ b = x`, is a prefix of the
    -- suffix `y ++ b` of `x`.
    intro h y hy
    obtain ⟨a, b, hab⟩ := hy
    exact h (y ++ b) ⟨a, by rw [← hab, List.append_assoc]⟩ y ⟨b, rfl⟩

end PvsNP.Units.tc_closure_every_factor_np

/-- NP is closed under "every factor is in L" (TM2): the settled suffix
closure `tc_closure_every_suffix_np` followed by the settled prefix closure
`m2_np_all_prefixes`, along the set equality above. -/
theorem PvsNP.Units.tc_closure_every_factor_np :
    ∀ L : Language Bool, L ∈ PvsNP.NP →
      ({x : List Bool | ∀ y : List Bool, y <:+: x → y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  rw [PvsNP.Units.tc_closure_every_factor_np.set_eq L]
  exact PvsNP.Units.m2_np_all_prefixes _
    (PvsNP.Units.tc_closure_every_suffix_np L hL)
