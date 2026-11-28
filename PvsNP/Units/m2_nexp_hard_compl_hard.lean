import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_exp_subset_nexp
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_exp_hard_nphard

set_option autoImplicit false

namespace PvsNP.Units.m2_nexp_hard_compl_hard

/-- Part 1: every exponential-time language reduces to `Lᶜ`.
For `L'` in exponential time, `L'ᶜ` is too (`m2_exp_compl`), hence in NEXP
(`m2_exp_subset_nexp`), hence `L'ᶜ ≤ L` by the NEXP-hardness hypothesis, and
`L' ≤ Lᶜ` by `m2_karp_compl_iff` with `compl_compl`. -/
theorem exp_hard_compl {L : Language Bool}
    (hHard : ∀ L' : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
        PvsNP.KarpReducible L' L) :
    ∀ L' : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
        PvsNP.KarpReducible L' Lᶜ := by
  intro L' hExp
  have hExpC := PvsNP.Units.m2_exp_compl L' hExp
  have hNexpC := PvsNP.Units.m2_exp_subset_nexp L'ᶜ hExpC
  have hred := hHard L'ᶜ hNexpC
  have h2 := (PvsNP.Units.m2_karp_compl_iff L'ᶜ L).mp hred
  rwa [compl_compl] at h2

end PvsNP.Units.m2_nexp_hard_compl_hard

theorem PvsNP.Units.m2_nexp_hard_compl_hard :
    ∀ L : Language Bool, (∀ L' : Language Bool,
    (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
      PvsNP.KarpReducible L' L) →
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' Lᶜ) ∧ PvsNP.NPHard Lᶜ := by
  intro L hHard
  have hpart := PvsNP.Units.m2_nexp_hard_compl_hard.exp_hard_compl hHard
  exact ⟨hpart, PvsNP.Units.m2_exp_hard_nphard Lᶜ hpart⟩
