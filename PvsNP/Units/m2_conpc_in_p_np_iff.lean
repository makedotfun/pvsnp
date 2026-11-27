import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_conpc_in_p_np_iff

theorem p_sub_np (A : Language Bool) (hA : A ∈ PvsNP.P) : A ∈ PvsNP.NP := by
  rcases hA with ⟨f, hf, hiff⟩
  refine ⟨f ∘ Prod.fst, 0,
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
      Prod.fst f PvsNP.Units.m2_pair_split_polytime.1 hf,
    fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨[], by simp, (hiff x).mp hx⟩
  · rintro ⟨_, _, hv⟩
    exact (hiff x).mpr hv

theorem karp_compl {A B : Language Bool} (h : PvsNP.KarpReducible A B) :
    PvsNP.KarpReducible (Aᶜ) (Bᶜ) := by
  rcases h with ⟨f, hf, hiff⟩
  exact ⟨f, hf, fun x => not_congr (hiff x)⟩

theorem main (L : Language Bool) (hL : L ∈ PvsNP.coNP)
    (hhard : ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L) :
    (L ∈ PvsNP.P ↔ PvsNP.P = PvsNP.NP) ∧ (L ∈ PvsNP.NP ↔ PvsNP.NP = PvsNP.coNP) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hLP
    ext A
    refine ⟨p_sub_np A, fun hAnp => ?_⟩
    have hAc_conp : Aᶜ ∈ PvsNP.coNP := by
      show Aᶜᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    have hAc_P : Aᶜ ∈ PvsNP.P :=
      PvsNP.Units.m2_pair_build_polytime.p_down_closed (hhard (Aᶜ) hAc_conp) hLP
    have hAcc_P : Aᶜᶜ ∈ PvsNP.P := PvsNP.Units.m2_pair_build_polytime.p_compl hAc_P
    rwa [compl_compl] at hAcc_P
  · intro heq
    have hLc_np : Lᶜ ∈ PvsNP.NP := hL
    have hLc_P : Lᶜ ∈ PvsNP.P := heq.symm ▸ hLc_np
    have hLcc_P : Lᶜᶜ ∈ PvsNP.P := PvsNP.Units.m2_pair_build_polytime.p_compl hLc_P
    rwa [compl_compl] at hLcc_P
  · intro hLnp
    ext A
    constructor
    · intro hAnp
      have hAc_conp : Aᶜ ∈ PvsNP.coNP := by
        show Aᶜᶜ ∈ PvsNP.NP
        rwa [compl_compl]
      have hred : PvsNP.KarpReducible A (Lᶜ) := by
        have h1 := karp_compl (hhard (Aᶜ) hAc_conp)
        rwa [compl_compl] at h1
      have hLc_conp : Lᶜ ∈ PvsNP.coNP := by
        show Lᶜᶜ ∈ PvsNP.NP
        rwa [compl_compl]
      exact PvsNP.Units.m2_pair_build_polytime.conp_down_closed hred hLc_conp
    · intro hAconp
      exact PvsNP.Units.m2_pair_build_polytime.np_down_closed (hhard A hAconp) hLnp
  · intro heq
    exact heq.symm ▸ hL

end PvsNP.Units.m2_conpc_in_p_np_iff

theorem PvsNP.Units.m2_conpc_in_p_np_iff :
    ∀ L : Language Bool, L ∈ PvsNP.coNP → (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L) →
      (L ∈ PvsNP.P ↔ PvsNP.P = PvsNP.NP) ∧ (L ∈ PvsNP.NP ↔ PvsNP.NP = PvsNP.coNP) :=
  PvsNP.Units.m2_conpc_in_p_np_iff.main
