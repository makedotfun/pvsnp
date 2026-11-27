import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_two_pass_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_prod_map_polytime

namespace PvsNP.Units.m2_self_concat_preimage

theorem filterMap_some (x : List Bool) : x.filterMap some = x := by
  induction x with
  | nil => rfl
  | cons b t ih => simp [ih]

theorem xx_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ x) := by
  have h := PvsNP.Units.m2_two_pass_polytime (fun b => some b) (fun b => some b)
  convert h using 2
  funext x
  simp [filterMap_some]

theorem id_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
  ⟨Turing.idComputableInPolyTime _⟩

end PvsNP.Units.m2_self_concat_preimage

theorem PvsNP.Units.m2_self_concat_preimage :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) ∧
          (L ∈ PvsNP.coNP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) := by
  have hNP : ∀ L : Language Bool,
      L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP := by
    intro L
    rintro ⟨V, p, hV, hiff⟩
    refine ⟨fun q => V (q.1 ++ q.1, q.2), p.comp (Polynomial.C 2 * Polynomial.X), ?_, ?_⟩
    · have hpair := PvsNP.Units.m2_prod_map_polytime _ _
        PvsNP.Units.m2_self_concat_preimage.xx_polytime
        PvsNP.Units.m2_self_concat_preimage.id_polytime
      have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
        PvsNP.encodeAnswer _ V hpair hV
      convert hcomp using 2
      funext q
      rfl
    · intro x
      have hlen : (x ++ x).length = 2 * x.length := by
        simp [List.length_append]
        omega
      constructor
      · intro hx
        obtain ⟨w, hw, hVw⟩ := (hiff (x ++ x)).mp hx
        refine ⟨w, ?_, hVw⟩
        rw [hlen] at hw
        simpa using hw
      · rintro ⟨w, hw, hVw⟩
        apply (hiff (x ++ x)).mpr
        refine ⟨w, ?_, hVw⟩
        rw [hlen]
        simpa using hw
  intro L
  refine ⟨?_, hNP L, ?_⟩
  · rintro ⟨d, hd, hdec⟩
    refine ⟨fun x => d (x ++ x), ?_, fun x => hdec (x ++ x)⟩
    have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeAnswer _ d PvsNP.Units.m2_self_concat_preimage.xx_polytime hd
    convert hcomp using 2
    funext x
    rfl
  · intro hL
    have hc : Lᶜ ∈ PvsNP.NP := hL
    have hpre := hNP (L := Lᶜ) hc
    show ({x : List Bool | x ++ x ∈ L} : Language Bool)ᶜ ∈ PvsNP.NP
    convert hpre using 2
    ext x
    simp
