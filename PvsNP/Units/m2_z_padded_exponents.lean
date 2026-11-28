import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_p_inter

/-
Built from the settled campaign units m2_np_poly_padding_iff (shape_in_P, padPoly),
fr_ladner (dropN), m2_p_down_closed and m2_p_inter (make.fun pvsnp campaign).
The official hint names m2_p_poly_padding_iff, which is not on main at the time of writing;
the P direction below is the same argument as m2_np_poly_padding_iff, with the P closures.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_z_padded_exponents

/-- Polynomial padding by `|x|^k` trues keeps a language in P and out of it (TM2). -/
theorem p_poly_padding_iff (L : Language Bool) (k : ℕ) :
    L ∈ PvsNP.P ↔
      ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
        s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.P := by
  constructor
  · intro hL
    have hShape : ({s : List Bool | ∃ x : List Bool,
        s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool) ∈ PvsNP.P :=
      PvsNP.Units.m2_np_poly_padding_iff.shape_in_P k
    have hPull : ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈ L} :
        Language Bool) ∈ PvsNP.P :=
      PvsNP.Units.m2_p_down_closed _ L
        ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN,
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_dropN,
          fun _ => Iff.rfl⟩ hL
    have hInter := PvsNP.Units.m2_p_inter _ _ hShape hPull
    have heq : (({s : List Bool | ∃ x : List Bool,
          s = PvsNP.Units.m2_np_poly_padding_iff.padPoly k x} : Language Bool) ⊓
        ({s : List Bool | PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN s ∈ L} :
          Language Bool)) =
        ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) := by
      ext s
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) = x :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
        change PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) ∈ L at hx
        rw [hdx] at hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, rfl⟩, ?_⟩
        have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
            (List.replicate (x.length ^ k) true ++ false :: x) = x :=
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
        show PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (List.replicate (x.length ^ k) true ++ false :: x) ∈ L
        rw [hdx]
        exact hx
    rw [← heq]
    exact hInter
  · intro hPad
    refine PvsNP.Units.m2_p_down_closed L _
      ⟨PvsNP.Units.m2_np_poly_padding_iff.padPoly k,
        PvsNP.Units.m2_np_poly_padding_iff.cpt_padPoly k, fun x => ?_⟩ hPad
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hd := congrArg PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN hxy
      have hdx : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (PvsNP.Units.m2_np_poly_padding_iff.padPoly k x) = x :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (x.length ^ k) x
      have hdy : PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN
          (List.replicate (y.length ^ k) true ++ false :: y) = y :=
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.dropN_un (y.length ^ k) y
      rw [hdx, hdy] at hd
      subst hd
      exact hy

end PvsNP.Units.m2_z_padded_exponents

theorem PvsNP.Units.m2_z_padded_exponents :
    ∀ (L : Language Bool) (j k : ℕ),
      (({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (x.length ^ j) true ++ false :: x} : Language Bool) ∈ PvsNP.P ↔
        ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.P) ∧
        (({s : List Bool | ∃ x : List Bool, x ∈ L ∧
            s = List.replicate (x.length ^ j) true ++ false :: x} : Language Bool) ∈ PvsNP.NP ↔
          ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
            s = List.replicate (x.length ^ k) true ++ false :: x} : Language Bool) ∈ PvsNP.NP) := by
  intro L j k
  constructor
  · exact (PvsNP.Units.m2_z_padded_exponents.p_poly_padding_iff L j).symm.trans (PvsNP.Units.m2_z_padded_exponents.p_poly_padding_iff L k)
  · exact (PvsNP.Units.m2_np_poly_padding_iff L j).symm.trans
      (PvsNP.Units.m2_np_poly_padding_iff L k)
