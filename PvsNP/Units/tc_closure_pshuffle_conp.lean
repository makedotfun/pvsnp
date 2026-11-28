import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_np_union

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_p_subset_np,
PvsNP.Units.m2_np_down_closed, PvsNP.Units.m2_np_union, and PvsNP.Units.tc_closure_pshuffle_p
of github.com/makedotfun/pvsnp (Apache License 2.0), whose machine combinators come from
github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_pshuffle_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def pickD : Bool → Bool → Bool × Option Bool
  | true, b  => (false, some b)
  | false, _ => (true, none)

private def pick (q : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => (if q then [b] else []) ++ pick (!q) bs

private theorem run_pick (q : Bool) (x : List Bool) :
    pick q x = fstRun pickD (fun _ => none) q x := by
  induction x generalizing q with
  | nil => rfl
  | cons b bs ih =>
    cases q <;> simpa [pick, fstRun, pickD] using ih _

private theorem cpt_pick (q : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (pick q) :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) (pick q) pickD (fun _ => none)
    q (run_pick q)

private def even (x : List Bool) : Prop :=
  x.foldl (fun q _ => !q) true = true

private def oddB (x : List Bool) : Bool :=
  x.foldl (fun q _ => !q) false

private theorem oddB_eq_not_even (x : List Bool) :
    oddB x = !(x.foldl (fun q _ => !q) true) := by
  have h : ∀ (l : List Bool) (q : Bool),
      l.foldl (fun s _ => !s) (!q) = !(l.foldl (fun s _ => !s) q) := by
    intro l
    induction l with
    | nil => intro q; rfl
    | cons _ t ih =>
      intro q
      simp only [List.foldl_cons]
      exact ih (!q)
  simpa [oddB] using h x true

private theorem run_oddB (x : List Bool) :
    ∀ q : Bool, fstRun (fun s (_ : Bool) => (!s, (none : Option Bool))) (fun s => some s) q x =
      [x.foldl (fun s _ => !s) q] := by
  induction x with
  | nil => intro q; rfl
  | cons _ t ih =>
    intro q
    simpa [fstRun, List.foldl_cons] using ih (!q)

private theorem odd_in_P :
    ({x : List Bool | ¬ even x} : Language Bool) ∈ PvsNP.P := by
  have h : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool oddB :=
    fst_polyTime (fun x : List Bool => x) Computability.encodeBool oddB
      (fun s (_ : Bool) => (!s, (none : Option Bool))) (fun s => some s) false
      (fun x => by simpa [Computability.encodeBool, oddB] using (run_oddB x false).symm)
  refine ⟨oddB, h, fun x => ?_⟩
  change ¬ (x.foldl (fun q _ => !q) true = true) ↔ oddB x = true
  rw [oddB_eq_not_even]
  cases x.foldl (fun q _ => !q) true <;> simp

private theorem unzip (x : List Bool) (he : even x) :
    (pick true x).length = (pick false x).length ∧
      x = (List.zipWith (fun a b => [a, b]) (pick true x) (pick false x)).flatten := by
  match x with
  | [] => exact ⟨rfl, rfl⟩
  | [_] => simp [even] at he
  | a :: b :: xs =>
    have he' : even xs := by simpa [even] using he
    obtain ⟨hlen, hz⟩ := unzip xs he'
    simp [pick, hlen, hz.symm]

private theorem recover (u v : List Bool) (h : u.length = v.length) :
    let x := (List.zipWith (fun a b => [a, b]) u v).flatten
    even x ∧ pick true x = u ∧ pick false x = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons _ _ => simp at h
  | cons a us ih =>
    cases v with
    | nil => simp at h
    | cons b vs =>
      obtain ⟨he, hu, hv⟩ := ih vs (by simpa using h)
      refine ⟨?_, ?_, ?_⟩
      · simpa [even] using he
      · simpa [pick] using hu
      · simpa [pick] using hv

theorem main :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.coNP → L₂ ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧
        x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.coNP := by
  intro L₁ L₂ h1 h2
  change ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧
      x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool)ᶜ ∈ PvsNP.NP
  have hE : ({x : List Bool | ¬ even x} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np odd_in_P
  have hA : ({x : List Bool | pick true x ∈ L₁ᶜ} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_down_closed _ L₁ᶜ ⟨pick true, cpt_pick true, fun _ => Iff.rfl⟩ h1
  have hB : ({x : List Bool | pick false x ∈ L₂ᶜ} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_down_closed _ L₂ᶜ ⟨pick false, cpt_pick false, fun _ => Iff.rfl⟩ h2
  have hunion := PvsNP.Units.m2_np_union _ _ hE (PvsNP.Units.m2_np_union _ _ hA hB)
  have heq :
      (({x : List Bool | ¬ even x} : Language Bool) ⊔
        (({x : List Bool | pick true x ∈ L₁ᶜ} : Language Bool) ⊔
          ({x : List Bool | pick false x ∈ L₂ᶜ} : Language Bool))) =
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧
          x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool)ᶜ := by
    ext x
    change (¬ even x ∨ (pick true x ∉ L₁ ∨ pick false x ∉ L₂)) ↔
      ¬ (∃ u v : List Bool, u.length = v.length ∧
          x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂)
    constructor
    · rintro (hno | hno1 | hno2) ⟨u, v, hlen, rfl, hu, hv⟩
      · exact hno (recover u v hlen).1
      · exact hno1 ((recover u v hlen).2.1.symm ▸ hu)
      · exact hno2 ((recover u v hlen).2.2.symm ▸ hv)
    · intro hnot
      by_cases he : even x
      · by_cases h1x : pick true x ∈ L₁
        · by_cases h2x : pick false x ∈ L₂
          · exfalso
            obtain ⟨hl, hz⟩ := unzip x he
            exact hnot ⟨pick true x, pick false x, hl, hz, h1x, h2x⟩
          · exact Or.inr (Or.inr h2x)
        · exact Or.inr (Or.inl h1x)
      · exact Or.inl he
  exact heq ▸ hunion

end PvsNP.Units.tc_closure_pshuffle_conp

theorem PvsNP.Units.tc_closure_pshuffle_conp :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.coNP → L₂ ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u v : List Bool, u.length = v.length ∧ x = (List.zipWith (fun a b => [a, b]) u v).flatten ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_pshuffle_conp.main
