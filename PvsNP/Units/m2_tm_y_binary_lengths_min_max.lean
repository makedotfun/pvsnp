import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_unary_min_max
import PvsNP.Units.m2_unary_to_binary_polytime

/-
Built by composing the settled units PvsNP.Units.m2_tm_unary_min_max
(unary `min` / `max` of the two lengths), PvsNP.Units.m2_unary_to_binary_polytime
(unary length to binary digits, via `List.length_replicate`), and
PvsNP.Units.m2_polytime_comp (composition of polytime functions),
of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

theorem PvsNP.Units.m2_tm_y_binary_lengths_min_max :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (min p.1.length p.2.length)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (max p.1.length p.2.length)) := by
  have hmin : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      ((fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (min p.1.length p.2.length) true)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString _ _
      PvsNP.Units.m2_tm_unary_min_max.1 PvsNP.Units.m2_unary_to_binary_polytime
  have hmax : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      ((fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (max p.1.length p.2.length) true)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString _ _
      PvsNP.Units.m2_tm_unary_min_max.2 PvsNP.Units.m2_unary_to_binary_polytime
  have heq_min : ((fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (min p.1.length p.2.length) true)) =
      (fun p : List Bool × List Bool => Nat.bits (min p.1.length p.2.length)) := by
    funext p
    simp only [Function.comp_apply, List.length_replicate]
  have heq_max : ((fun x : List Bool => Nat.bits x.length) ∘
        (fun p : List Bool × List Bool => List.replicate (max p.1.length p.2.length) true)) =
      (fun p : List Bool × List Bool => Nat.bits (max p.1.length p.2.length)) := by
    funext p
    simp only [Function.comp_apply, List.length_replicate]
  rw [heq_min] at hmin
  rw [heq_max] at hmax
  exact ⟨hmin, hmax⟩
