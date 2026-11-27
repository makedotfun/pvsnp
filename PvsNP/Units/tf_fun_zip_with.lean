import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

/-
The bitwise and of two strings takes polynomial time (TM2).

The proof is a machine in the shape the settled unit `m2_zip_bne_polytime` uses for bitwise
exclusive-or: a working tape holding (a, b, acc), one step that pops a bit from each input and
pushes `a && b` onto `acc`, and a step that stops as soon as either input is exhausted. The two
files differ only in the step's truth table (`a && b` in place of `a != b`), and the list identity
proved here, `zip_and_iter`, is written for this file.

Nothing is copied from that unit: the machine, its step, the bound and the run are laid out here
again for the and, and the identity is proved from scratch.
-/

namespace PvsNP.Units.tf_fun_zip_with

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

theorem unpairB_len_bound (s : List Bool) :
    (unpairB s).1.length + (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  have hsplit : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

theorem pairB_length (a b : List Bool) :
    (pairB a b).length = a.length + a.length + b.length + 1 := by
  simp only [pairB, List.length_append, un_length, List.length_cons]
  omega

/-- The three components of the working tape: the first input, the second input, the answer. -/
def partA (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def partB (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def acc (s : List Bool) : List Bool := (unpairB s).2

/-- One step: pop a bit from each input while both are nonempty and push `a && b`; otherwise
stay where it is, so the run stops when either input is spent. -/
def andStep (s : List Bool) : List Bool :=
  if !(partA s).isEmpty = true then
    if !(partB s).isEmpty = true then
      if (partA s).headD false = true then
        if (partB s).headD false = true then
          pairB (pairB (partA s).tail (partB s).tail) (acc s ++ [true])
        else
          pairB (pairB (partA s).tail (partB s).tail) (acc s ++ [false])
      else
        pairB (pairB (partA s).tail (partB s).tail) (acc s ++ [false])
    else
      pairB (pairB (partA s) (partB s)) (acc s)
  else
    pairB (pairB (partA s) (partB s)) (acc s)

theorem andStep_len (s : List Bool) : (andStep s).length ≤ s.length + 5 := by
  have hbound : 4 * (partA s).length + 2 * (partB s).length + (acc s).length ≤ s.length := by
    have h1 := unpairB_len_bound s
    have h2 := unpairB_len_bound (unpairB s).1
    unfold partA partB acc at *
    omega
  unfold andStep
  split_ifs <;>
    simp only [pairB_length, List.length_append, List.length_singleton, List.length_tail] <;>
    omega

theorem isEmpty_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => !x.isEmpty) := by
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p Bool (fun _ _ => true) false id
  have hfold_true : ∀ y : List Bool, y.foldl (fun _ _ => true) true = true := by
    intro y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => !x.isEmpty := by
    funext x
    have hx := hdec x
    change id (x.foldl (fun _ _ => true) false) = true ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, id, List.isEmpty_nil, Bool.not_true] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, hfold_true, id, List.isEmpty_cons, Bool.not_false] at hx ⊢
      exact hx.1 trivial
  rwa [← heq]

theorem headD_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => x.headD false := by
    funext x
    have hx := hdec x
    change ((x.foldl δ none == some true) = true) ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, List.headD_nil] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, δ, hfold_some, List.headD_cons] at hx ⊢
      cases b with
      | false => cases hcx : c (false :: y) <;> simp_all
      | true => exact hx.1 (by decide)
  rwa [← heq]

theorem andStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString andStep := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString partA :=
    cpt_unpairB1_1 cpt_unpairB1
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString partB :=
    cpt_unpairB2_1 cpt_unpairB1
  have hAcc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString acc :=
    cpt_unpairB2
  have hAne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    partA (fun x => !x.isEmpty) hA isEmpty_poly
  have hBne := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    partB (fun x => !x.isEmpty) hB isEmpty_poly
  have hAhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    partA (fun x => x.headD false) hA headD_poly
  have hBhd := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    partB (fun x => x.headD false) hB headD_poly
  have hpairT := cpt_pairB2 (cpt_tail1 hA) (cpt_tail1 hB)
  have hpushT := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [true]))
  have hpushF := cpt_pairB2 hpairT (cpt_app2 hAcc (cpt_const [false]))
  have hstay := cpt_pairB2 (cpt_pairB2 hA hB) hAcc
  -- both true: push true; both others where the first is true: push false
  have h1 := PvsNP.Units.m2_ite_polytime _ _ _ hBhd hpushT hpushF
  -- the first bit false: push false whatever the second is
  have h2 := PvsNP.Units.m2_ite_polytime _ _ _ hAhd h1 hpushF
  have h3 := PvsNP.Units.m2_ite_polytime _ _ _ hBne h2 hstay
  exact PvsNP.Units.m2_ite_polytime _ _ _ hAne h3 hstay

/-- After `m` steps with the first input of length `m`, the answer holds the pairwise and of the
first `m` bits of each input, and the remaining inputs are their tails. -/
theorem andStep_iter (a b acc₀ : List Bool) :
    (unpairB (andStep^[a.length] (pairB (pairB a b) acc₀))).2 =
      acc₀ ++ List.zipWith (fun x y : Bool => x && y) a b := by
  induction a generalizing b acc₀ with
  | nil =>
    simp only [List.length_nil, Function.iterate_zero, id, unpairB_pairB,
      List.zipWith_nil_left, List.append_nil]
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [List.length_cons, List.zipWith_nil_right, List.append_nil]
      -- the step stays put: the second input is empty
      have hstay : ∀ (m : ℕ) (u : List Bool), (unpairB (andStep^[m] (pairB (pairB u []) acc₀))).2 = acc₀ := by
        intro m
        induction m with
        | zero => intro u; simp [unpairB_pairB]
        | succ m ihm =>
          intro u
          rw [Function.iterate_succ_apply]
          have : andStep (pairB (pairB u []) acc₀) = pairB (pairB u []) acc₀ := by
            unfold andStep partA partB acc
            simp [unpairB_pairB]
          rw [this]
          exact ihm u
      exact hstay (x :: a).length (x :: a)
    | cons y b =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hs : andStep (pairB (pairB (x :: a) (y :: b)) acc₀) =
          pairB (pairB a b) (acc₀ ++ [x && y]) := by
        unfold andStep partA partB acc
        simp only [unpairB_pairB, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
          List.headD_cons, List.tail_cons]
        cases x <;> cases y <;> rfl
      rw [hs, ih b (acc₀ ++ [x && y])]
      simp [List.append_assoc]

end PvsNP.Units.tf_fun_zip_with

theorem PvsNP.Units.tf_fun_zip_with :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) := by
  open PvsNP.Units.fr_ladner.PEqualNP.Library in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
  obtain ⟨hstep⟩ := PvsNP.Units.tf_fun_zip_with.andStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => PvsNP.Units.tf_fun_zip_with.andStep^[p.2.length] p.1) :=
    Iter.iter_polyTime PvsNP.Units.tf_fun_zip_with.andStep hstep 5
      PvsNP.Units.tf_fun_zip_with.andStep_len
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB p.1 p.2) := by
    rw [← PvsNP.Units.tf_fun_zip_with.encodePair_eq]
    exact cpt_pairB
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB s []) :=
    cpt_pairB2 cpt_id (cpt_const [])
  have hrunS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tf_fun_zip_with.andStep^[
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s).1.length]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB s []))).2) :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit cpt_unpairB1) hiter)
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB p.1 p.2)
    (fun s : List Bool => (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.tf_fun_zip_with.andStep^[
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s).1.length]
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB s []))).2) hpb hrunS
  have heq :
      ((fun s : List Bool => (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.tf_fun_zip_with.andStep^[
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s).1.length]
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB s []))).2) ∘
        (fun p : List Bool × List Bool =>
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB p.1 p.2)) =
      (fun p : List Bool × List Bool => List.zipWith (fun a b : Bool => a && b) p.1 p.2) := by
    funext ⟨a, b⟩
    simp only [Function.comp_apply, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
    have h := PvsNP.Units.tf_fun_zip_with.andStep_iter a b []
    simpa using h
  rwa [heq] at hcomp
