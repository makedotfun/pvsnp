import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_split_polytime

/-!
# m2_self_concat_preimage: P, NP and coNP are closed under the square preimage

For every language `L`, the language `{x | x ++ x ∈ L}` lies in the same
class as `L`, for each of `P`, `NP`, `coNP`. Everything is a composition of
settled units of github.com/makedotfun/pvsnp (Apache License 2.0) with the
class definitions in `PvsNP.Defs`:

* `tf_fun_self_append`: `fun x => x ++ x` is `PolyTimeComputable`;
* `m2_polytime_comp`: polytime computability is closed under composition;
* `m2_tm_pair_fork_polytime` and `m2_pair_split_polytime`: the pair map
  `(x, w) ↦ (x ++ x, w)` is polytime, which transports verifiers.

The `P` part precomposes the decider with `x ↦ x ++ x`. The `NP` part
precomposes the verifier with `(x, w) ↦ (x ++ x, w)`; the certificate bound
for input `x` is `p.eval (2 * x.length)`, packaged as the single polynomial
`p.comp (2 * Polynomial.X)`. The `coNP` part is the `NP` part applied to
`Lᶜ`, using `({x | x ++ x ∈ L})ᶜ = {x | x ++ x ∈ Lᶜ}` pointwise.

Verified by hand, line by line, against the settled statements and the
definitions in `PvsNP/Defs/Classes.lean` (no lease is held for this unit,
so `desk check --build` could not be run).
-/

namespace PvsNP.Units.m2_self_concat_preimage

/-- The pair map `(x, w) ↦ (x ++ x, w)` is polytime computable: fork the
first projection with itself, append the pair, and fork with the second
projection. -/
theorem pair_map :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun q : List Bool × List Bool => (q.1 ++ q.1, q.2)) := by
  have hsplit := PvsNP.Units.m2_pair_split_polytime
  have hfst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun q : List Bool × List Bool => q.1 ++ q.1) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      (PvsNP.Units.m2_tm_pair_fork_polytime _ _ hsplit.1 hsplit.1) hsplit.2.2
  exact PvsNP.Units.m2_tm_pair_fork_polytime _ _ hfst hsplit.2.1

/-- The `P` part: precompose a polytime decider with `x ↦ x ++ x`. -/
theorem p_part (L : Language Bool) (hL : L ∈ PvsNP.P) :
    ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P := by
  have hLd : PvsNP.PolyTimeDecidable L := hL
  obtain ⟨f, hf, hiff⟩ := hLd
  have hcomp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (f ∘ (fun x : List Bool => x ++ x)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_self_append hf
  refine ⟨f ∘ (fun x : List Bool => x ++ x), hcomp, ?_⟩
  intro x
  exact hiff (x ++ x)

/-- The `NP` part: precompose a polytime verifier with `(x, w) ↦ (x ++ x, w)`
and absorb the doubled input length into the bound polynomial. -/
theorem np_part (L : Language Bool) (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP := by
  have hLd : ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
      PvsNP.PolyTimeVerifier L V p := hL
  obtain ⟨V, p, hV⟩ := hLd
  obtain ⟨hVc, hiff⟩ := hV
  have hbound : ∀ n : ℕ, p.eval (2 * n) = (p.comp (2 * Polynomial.X)).eval n :=
    fun n => by simp [Polynomial.eval_comp]
  have hV' : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun q : List Bool × List Bool => V (q.1 ++ q.1, q.2)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_self_concat_preimage.pair_map hVc
  refine ⟨(fun q : List Bool × List Bool => V (q.1 ++ q.1, q.2)),
    p.comp (2 * Polynomial.X), hV', ?_⟩
  intro x
  have hx : (x ++ x).length = 2 * x.length := by
    rw [List.length_append]; ring
  constructor
  · intro hxmem
    obtain ⟨w, hw, hwV⟩ := (hiff (x ++ x)).1 hxmem
    exact ⟨w, by simpa [hx, hbound] using hw, hwV⟩
  · rintro ⟨w, hw, hwV⟩
    apply (hiff (x ++ x)).2
    exact ⟨w, by simpa [hx, hbound] using hw, hwV⟩

/-- The `coNP` part: complement of the square preimage is the square
preimage of the complement, so the `NP` part applied to `Lᶜ` finishes. -/
theorem conp_part (L : Language Bool) (hL : L ∈ PvsNP.coNP) :
    ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP := by
  have hLc : Lᶜ ∈ PvsNP.NP := hL
  have h := PvsNP.Units.m2_self_concat_preimage.np_part Lᶜ hLc
  have hset : ({x : List Bool | x ++ x ∈ L} : Language Bool)ᶜ =
      {x : List Bool | x ++ x ∈ Lᶜ} := by
    ext x
    simp [Set.mem_compl_iff]
  show ({x : List Bool | x ++ x ∈ L} : Language Bool)ᶜ ∈ PvsNP.NP
  rw [hset]
  exact h

end PvsNP.Units.m2_self_concat_preimage

/-- P, NP and coNP are closed under taking the strings whose square `xx`
is in `L`: the three parts above. -/
theorem PvsNP.Units.m2_self_concat_preimage :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) ∧
          (L ∈ PvsNP.coNP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) :=
  fun L => ⟨PvsNP.Units.m2_self_concat_preimage.p_part L,
    PvsNP.Units.m2_self_concat_preimage.np_part L,
    PvsNP.Units.m2_self_concat_preimage.conp_part L⟩
