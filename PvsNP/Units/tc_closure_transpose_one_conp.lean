import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_transpose_one_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

def takeU (u x : List Bool) : List Bool := (dropU (dropU u x) x.reverse).reverse

theorem cpt_takeU {f g : List Bool → List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => takeU (f s) (g s)) :=
  let hrev : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  cpt_comp (cpt_dropU (cpt_dropU hf hg) (cpt_comp hg hrev)) hrev

theorem takeU_eq (u x : List Bool) : takeU u x = x.take u.length := by
  unfold takeU
  rw [dropU_eq, dropU_eq, List.length_drop]
  have h1 : x.reverse = (x.drop u.length).reverse ++ (x.take u.length).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have h2 : (x.drop u.length).reverse.length = x.length - u.length := by
    rw [List.length_reverse, List.length_drop]
  rw [h1, ← h2, List.drop_left, List.reverse_reverse]

theorem encPair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
    Computability.encodingProd, Computability.encodingList]

def boolToFlag : Bool → List Bool
  | true => []
  | false => [true]

theorem cpt_boolToFlag :
    PvsNP.PolyTimeComputable PvsNP.encodeAnswer PvsNP.encodeString boolToFlag :=
  fst_polyTime PvsNP.encodeAnswer PvsNP.encodeString boolToFlag
    (fun (_ : Unit) b => ((), if b then none else some true)) (fun _ => none) ()
    (fun b => by cases b <;> rfl)

inductive SwapSt : Type
  | s0
  | s1 (a : Bool)
  | s2 (prev : Bool)
  deriving DecidableEq

instance : Fintype SwapSt where
  elems := {.s0, .s1 false, .s1 true, .s2 false, .s2 true}
  complete := by rintro (_ | ⟨_ | _⟩ | ⟨_ | _⟩) <;> simp

def swapDelta : SwapSt → Bool → SwapSt × Option Bool
  | .s0, a => (.s1 a, none)
  | .s1 a, b => (.s2 a, some b)
  | .s2 p, c => (.s2 c, some p)

def swapFin : SwapSt → Option Bool
  | .s0 => none
  | .s1 a => some a
  | .s2 p => some p

def swapHead (r : List Bool) : List Bool := fstRun swapDelta swapFin .s0 r

theorem cpt_swapHead : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) swapHead :=
  fst_polyTime _ _ swapHead swapDelta swapFin .s0 (fun _ => rfl)

theorem fstRun_swap_s2 (p : Bool) (t : List Bool) :
    fstRun swapDelta swapFin (.s2 p) t = p :: t := by
  induction t generalizing p with
  | nil => rfl
  | cons c rest ih =>
    simp only [fstRun, swapDelta, Option.toList_some, List.cons_append, List.nil_append]
    exact congrArg (p :: ·) (ih c)

theorem swapHead_cons_cons (a b : Bool) (t : List Bool) :
    swapHead (a :: b :: t) = b :: a :: t := by
  simp [swapHead, fstRun, swapDelta, fstRun_swap_s2]

theorem swapHead_len (r : List Bool) : (swapHead r).length = r.length := by
  match r with
  | [] => rfl
  | [a] => simp [swapHead, fstRun, swapDelta, swapFin]
  | a :: b :: t => rw [swapHead_cons_cons]; simp

def swapAt (u x : List Bool) : List Bool :=
  takeU u x ++ swapHead (dropU u x)

theorem swapAt_len (u x : List Bool) : (swapAt u x).length = x.length := by
  unfold swapAt
  rw [List.length_append, swapHead_len, takeU_eq, dropU_eq, ← List.length_append, List.take_append_drop]

theorem swapAt_eq (u v : List Bool) (a b : Bool) (idx : List Bool) (hi : idx.length = u.length) :
    swapAt idx (u ++ a :: b :: v) = u ++ b :: a :: v := by
  unfold swapAt
  rw [takeU_eq, dropU_eq, hi, List.take_left, List.drop_left, swapHead_cons_cons]

theorem swapAt_witness (idx x : List Bool) (h : (dropU idx x).tail ≠ []) :
    ∃ u v a b, x = u ++ a :: b :: v ∧ u.length = idx.length ∧ swapAt idx x = u ++ b :: a :: v := by
  rw [dropU_eq] at h
  cases hd : x.drop idx.length with
  | nil => simp [hd] at h
  | cons a rest =>
    cases rest with
    | nil => simp [hd] at h
    | cons b v =>
      have hx : x = x.take idx.length ++ a :: b :: v := by
        rw [← hd, List.take_append_drop]
      have hlen : idx.length ≤ x.length := by
        by_contra hlt
        have : x.drop idx.length = [] := List.drop_eq_nil_iff.mpr (by omega)
        rw [hd] at this; cases this
      have htk : (x.take idx.length).length = idx.length := by
        rw [List.length_take]; omega
      refine ⟨x.take idx.length, v, a, b, hx, htk, ?_⟩
      unfold swapAt
      rw [takeU_eq, dropU_eq, hd, swapHead_cons_cons]

def buildW (ws : List (List Bool)) : List Bool :=
  ws.foldr pairB []

theorem buildW_length (ws : List (List Bool)) (B : ℕ) (hB : ∀ w ∈ ws, w.length ≤ B) :
    (buildW ws).length ≤ ws.length * (2 * B + 2) := by
  induction ws with
  | nil => simp [buildW]
  | cons w t ih =>
    simp only [buildW, List.foldr_cons, pairB_length, List.length_cons]
    have hw : w.length ≤ B := hB w (List.mem_cons_self)
    have ht : (buildW t).length ≤ t.length * (2 * B + 2) := ih (fun x hx => hB x (List.mem_cons_of_mem w hx))
    rw [Nat.add_mul, one_mul]
    change 2 * w.length + (buildW t).length + 1 ≤ _
    omega

theorem main :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ (u v : List Bool) (a b : Bool), x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L} : Language Bool) ∈ PvsNP.coNP := by
  intro L hLco
  obtain ⟨R, p, ⟨d, hdR, hdc⟩, hshort, hLc⟩ := L045 Lᶜ ((PvsNP.Units.fr_ladner.NP_iff Lᶜ).mp hLco)
  have hd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer d := by
    rw [← encPair_eq]; exact hdc
  -- State: pairB bad (pairB x (pairB idx W))
  let checkStep : List Bool → List Bool := fun s =>
    let bad := (unpairB s).1
    let st1 := (unpairB s).2
    let x := (unpairB st1).1
    let st2 := (unpairB st1).2
    let idx := (unpairB st2).1
    let W := (unpairB st2).2
    let rest := dropU idx x
    let sw := swapAt idx x
    let wi := (unpairB W).1
    let W' := (unpairB W).2
    let bad' := sel rest.tail bad (sel (boolToFlag (d (sw, wi))) bad [true])
    pairB bad' (pairB x (pairB (true :: idx) W'))
  have hcheck : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) checkStep := by
    have hbad : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).1) := cpt_unpairB1
    have hst1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).2) := cpt_unpairB2
    have hx := cpt_unpairB1_1 hst1
    have hst2 := cpt_unpairB2_1 hst1
    have hidx := cpt_unpairB1_1 hst2
    have hW := cpt_unpairB2_1 hst2
    have hrest := cpt_dropU hidx hx
    have hsw := cpt_app2 (cpt_takeU hidx hx) (cpt_comp hrest cpt_swapHead)
    have hwi := cpt_unpairB1_1 hW
    have hW' := cpt_unpairB2_1 hW
    have hpSw : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun s : List Bool => (swapAt (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB s).2).1,
          (unpairB (unpairB (unpairB (unpairB s).2).2).2).1)) := by
      have h := cpt_pair hsw hwi
      rw [encPair_eq] at h; exact h
    have hfl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun s => boolToFlag (d (swapAt (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB s).2).1,
          (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))) :=
      PvsNP.Units.m2_polytime_comp _ _ _ _ boolToFlag
        (PvsNP.Units.m2_polytime_comp _ _ _ _ d hpSw hd) cpt_boolToFlag
    have hbad' := cpt_sel (cpt_tail1 hrest) hbad (cpt_sel hfl hbad (cpt_const [true]))
    exact cpt_pairB2 hbad' (cpt_pairB2 hx (cpt_pairB2 (cpt_cons1 true hidx) hW'))
  have hstep_len : ∀ s : List Bool, (checkStep s).length ≤ s.length + 10 := by
    intro s
    have h1 := unpairB_length s
    have h2 := unpairB_length (unpairB s).2
    have h3 := unpairB_length (unpairB (unpairB s).2).2
    have h4 := unpairB_length (unpairB (unpairB (unpairB s).2).2).2
    show (pairB _ (pairB _ (pairB _ _))).length ≤ s.length + 10
    simp only [pairB_length, List.length_cons]
    have hbl : (sel (dropU (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB s).2).1).tail (unpairB s).1
        (sel (boolToFlag (d (swapAt (unpairB (unpairB (unpairB s).2).2).1 (unpairB (unpairB s).2).1,
          (unpairB (unpairB (unpairB (unpairB s).2).2).2).1))) (unpairB s).1 [true])).length ≤
        (unpairB s).1.length + 1 := by
      unfold sel
      split_ifs <;> simp <;> omega
    omega
  have hiter_bad_mono : ∀ (m : ℕ) (x idx W : List Bool),
      (unpairB (checkStep^[m] (pairB [true] (pairB x (pairB idx W))))).1 ≠ [] := by
    intro m
    induction m with
    | zero => intro x idx W; simp [unpairB_pairB]
    | succ m ih =>
      intro x idx W
      rw [Function.iterate_succ_apply]
      have hst : checkStep (pairB [true] (pairB x (pairB idx W))) =
          pairB [true] (pairB x (pairB (true :: idx) (unpairB W).2)) := by
        show pairB _ _ = _
        simp only [unpairB_pairB]
        congr 1
        unfold sel; split_ifs <;> rfl
      rw [hst]
      exact ih x (true :: idx) (unpairB W).2
  have hiter_iff : ∀ (m : ℕ) (x idx W : List Bool),
      (unpairB (checkStep^[m] (pairB [] (pairB x (pairB idx W))))).1 = [] ↔
        ∀ j : ℕ, j < m →
          let idxj := List.replicate j true ++ idx
          (dropU idxj x).tail ≠ [] →
            d (swapAt idxj x, (unpairB ((fun z => (unpairB z).2)^[j] W)).1) = true := by
    intro m
    induction m with
    | zero =>
      intro x idx W
      simp [unpairB_pairB]
    | succ m ih =>
      intro x idx W
      rw [Function.iterate_succ_apply]
      have hst0 : checkStep (pairB [] (pairB x (pairB idx W))) =
          pairB (if (dropU idx x).tail = [] then [] else if boolToFlag (d (swapAt idx x, (unpairB W).1)) = [] then [] else [true])
            (pairB x (pairB (true :: idx) (unpairB W).2)) := by
        show pairB _ _ = _
        simp only [unpairB_pairB, sel]
      rw [hst0]
      by_cases htail : (dropU idx x).tail = []
      · simp only [htail, ↓reduceIte, ih x (true :: idx) (unpairB W).2]
        constructor
        · intro h j hj
          cases j with
          | zero => intro hne; exact absurd htail hne
          | succ j' =>
            have hj' : j' < m := by omega
            have hstep := h j' hj'
            have hrep : List.replicate (j' + 1) true ++ idx = List.replicate j' true ++ (true :: idx) := by
              rw [List.replicate_succ', List.append_assoc]; rfl
            rw [hrep, Function.iterate_succ_apply]
            exact hstep
        · intro h j hj
          have hstep := h (j + 1) (by omega)
          have hrep : List.replicate (j + 1) true ++ idx = List.replicate j true ++ (true :: idx) := by
            rw [List.replicate_succ', List.append_assoc]; rfl
          rw [hrep, Function.iterate_succ_apply] at hstep
          exact hstep
      · simp only [htail, ↓reduceIte]
        by_cases hok : d (swapAt idx x, (unpairB W).1) = true
        · have hfl : boolToFlag (d (swapAt idx x, (unpairB W).1)) = [] := by simp [hok, boolToFlag]
          simp only [hfl, ↓reduceIte, ih x (true :: idx) (unpairB W).2]
          constructor
          · intro h j hj
            cases j with
            | zero => intro _; simpa using hok
            | succ j' =>
              have hstep := h j' (by omega)
              have hrep : List.replicate (j' + 1) true ++ idx = List.replicate j' true ++ (true :: idx) := by
                rw [List.replicate_succ', List.append_assoc]; rfl
              rw [hrep, Function.iterate_succ_apply]
              exact hstep
          · intro h j hj
            have hstep := h (j + 1) (by omega)
            have hrep : List.replicate (j + 1) true ++ idx = List.replicate j true ++ (true :: idx) := by
              rw [List.replicate_succ', List.append_assoc]; rfl
            rw [hrep, Function.iterate_succ_apply] at hstep
            exact hstep
        · have hfl : boolToFlag (d (swapAt idx x, (unpairB W).1)) ≠ [] := by
            cases h : d (swapAt idx x, (unpairB W).1) <;> simp [h, boolToFlag] at hok ⊢
          simp only [hfl, ↓reduceIte]
          constructor
          · intro hbad; exact absurd hbad (hiter_bad_mono m x (true :: idx) (unpairB W).2)
          · intro hall
            have h0 := hall 0 (Nat.zero_lt_succ m)
            simp only [List.replicate_zero, List.nil_append, Function.iterate_zero_apply] at h0
            exact absurd (h0 htail) hok
  obtain ⟨c⟩ := hcheck
  have hI : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => checkStep^[p.2.length] p.1) :=
    Iter.iter_polyTime checkStep c 10 hstep_len
  let runS : List Bool → List Bool := fun s =>
    (unpairB (checkStep^[(unpairB s).1.length] (pairB [] (pairB (unpairB s).1 (pairB [] (unpairB s).2))))).1
  have hrun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) runS := by
    have hx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).1) := cpt_unpairB1
    have hW : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fun s => (unpairB s).2) := cpt_unpairB2
    have hinit := cpt_pairB2 (cpt_const []) (cpt_pairB2 hx (cpt_pairB2 (cpt_const []) hW))
    exact cpt_unpairB1_1 (cpt_comp (f := fun s => (pairB [] (pairB (unpairB s).1 (pairB [] (unpairB s).2)), (unpairB s).1))
      (g := fun p : List Bool × List Bool => checkStep^[p.2.length] p.1) (cpt_pair hinit hx) hI)
  have hdecS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s : List Bool => decide (runS s = [])) := by
    have hp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair (fun s => (runS s, [])) := by
      have h := cpt_pair hrun (cpt_const [])
      rw [encPair_eq] at h; exact h
    exact PvsNP.Units.m2_polytime_comp _ _ _ _ (fun p => decide (p.1 = p.2)) hp PvsNP.Units.m2_eq_polytime
  have hpb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    have h := cpt_pairB; rw [encPair_eq] at h; exact h
  have hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (runS (pairB p.1 p.2) = [])) :=
    PvsNP.Units.m2_polytime_comp _ _ _ (fun p : List Bool × List Bool => pairB p.1 p.2)
      (fun s => decide (runS s = [])) hpb hdecS
  let Ppoly : Polynomial ℕ := Polynomial.X * (Polynomial.C 2 * p + Polynomial.C 2)
  refine ⟨fun (p : List Bool × List Bool) => decide (runS (pairB p.1 p.2) = []), Ppoly, hV, fun x => ?_⟩
  change (¬ ∃ (u v : List Bool) (a b : Bool), x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L) ↔
    ∃ W : List Bool, W.length ≤ Ppoly.eval x.length ∧ decide (runS (pairB x W) = []) = true
  have hrun_eq : ∀ W : List Bool, decide (runS (pairB x W) = []) = true ↔
      ∀ j : ℕ, j < x.length →
        (dropU (List.replicate j true) x).tail ≠ [] →
          d (swapAt (List.replicate j true) x, (unpairB ((fun z => (unpairB z).2)^[j] W)).1) = true := by
    intro W
    rw [decide_eq_true_eq]
    unfold runS
    simp only [unpairB_pairB]
    rw [hiter_iff x.length x [] W]
    simp only [List.append_nil]
  constructor
  · intro hnot
    -- Build witness list of length x.length
    have hex : ∀ j : Fin x.length, ∃ w : List Bool,
        w.length ≤ p.eval x.length ∧
          ((dropU (List.replicate j.1 true) x).tail ≠ [] → d (swapAt (List.replicate j.1 true) x, w) = true) := by
      intro ⟨j, hj⟩
      by_cases htail : (dropU (List.replicate j true) x).tail = []
      · exact ⟨[], Nat.zero_le _, fun h => absurd htail h⟩
      · obtain ⟨u, v, a, b, hx, hu, hsw⟩ := swapAt_witness (List.replicate j true) x htail
        have hnotL : swapAt (List.replicate j true) x ∈ Lᶜ := by
          intro hmem
          rw [hsw] at hmem
          exact hnot ⟨u, v, a, b, hx, hmem⟩
        obtain ⟨w, hw⟩ := (hLc (swapAt (List.replicate j true) x)).mp hnotL
        have hs := hshort _ w hw
        rw [swapAt_len] at hs
        exact ⟨w, hs, fun _ => (hdR _).mp hw⟩
    choose f hf_len hf_ok using hex
    let ws : List (List Bool) := List.ofFn f
    let W := buildW ws
    have hWlen : W.length ≤ Ppoly.eval x.length := by
      have hb := buildW_length ws (p.eval x.length) (by
        intro w hw
        rw [List.mem_ofFn] at hw
        obtain ⟨j, rfl⟩ := hw
        exact hf_len j)
      have hwl : ws.length = x.length := List.length_ofFn
      rw [hwl] at hb
      simpa [Ppoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] using hb
    have hpeel : ∀ (l : List (List Bool)) (j : ℕ) (hj : j < l.length),
        (unpairB ((fun z => (unpairB z).2)^[j] (buildW l))).1 = l[j] := by
      intro l
      induction l with
      | nil => intro j hj; cases hj
      | cons hd tl ih =>
        intro j hj
        cases j with
        | zero => simp [buildW, unpairB_pairB]
        | succ j' =>
          rw [Function.iterate_succ_apply]
          have h1 : (unpairB (buildW (hd :: tl))).2 = buildW tl := by simp [buildW, unpairB_pairB]
          rw [h1]
          exact ih j' (by simpa using hj)
    refine ⟨W, hWlen, (hrun_eq W).mpr fun j hj htail => ?_⟩
    have hjw : j < ws.length := by simpa [ws] using hj
    rw [hpeel ws j hjw]
    have hget : ws[j]'hjw = f ⟨j, hj⟩ := by simp [ws]
    rw [hget]
    exact hf_ok ⟨j, hj⟩ htail
  · rintro ⟨W, _, hW⟩
    have hall := (hrun_eq W).mp hW
    rintro ⟨u, v, a, b, rfl, hmem⟩
    have hlt : u.length < (u ++ a :: b :: v).length := by simp
    have htail : (dropU (List.replicate u.length true) (u ++ a :: b :: v)).tail ≠ [] := by
      rw [dropU_eq, List.length_replicate, List.drop_left]
      simp
    have hok := hall u.length hlt htail
    have hsw : swapAt (List.replicate u.length true) (u ++ a :: b :: v) = u ++ b :: a :: v :=
      swapAt_eq u v a b (List.replicate u.length true) (List.length_replicate)
    rw [hsw] at hok
    have hnotL : u ++ b :: a :: v ∈ Lᶜ := (hLc _).mpr ⟨_, (hdR _).mpr hok⟩
    exact hnotL hmem

end PvsNP.Units.tc_closure_transpose_one_conp

theorem PvsNP.Units.tc_closure_transpose_one_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ (u v : List Bool) (a b : Bool), x = u ++ a :: b :: v ∧ u ++ b :: a :: v ∈ L} : Language Bool) ∈ PvsNP.coNP :=
  PvsNP.Units.tc_closure_transpose_one_conp.main
