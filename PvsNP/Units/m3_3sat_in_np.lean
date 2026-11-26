import Mathlib
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_3sat_in_np

open CookLevin CookLevin.Lang EvalCnfCmd EvalCnfTM SATStr CnfWellFormed

/-- 3-SAT language on bit strings. -/
def threeSatLang (x : List Bool) : Prop :=
  (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)

/-- Pure model of the 3-SAT clause-length scanner.
State: `(inLit, pending, c1, c2, c3, ov)`. -/
def step3 : Bool × Bool × Bool × Bool × Bool × Bool → Nat →
    Bool × Bool × Bool × Bool × Bool × Bool
  | (false, _, c1, c2, c3, ov), cell =>
      if cell = 1 then
        if c3 then (true, false, c1, c2, c3, true)
        else if c2 then (true, false, c1, c2, true, ov)
        else if c1 then (true, false, c1, true, false, ov)
        else (true, false, true, false, false, ov)
      else (false, false, false, false, false, ov)
  | (true, false, c1, c2, c3, ov), _ => (true, true, c1, c2, c3, ov)
  | (true, true, c1, c2, c3, ov), cell =>
      if cell = 1 then (true, true, c1, c2, c3, ov)
      else (false, true, c1, c2, c3, ov)

def run3 (l : List Nat) : Bool × Bool × Bool × Bool × Bool × Bool :=
  l.foldl step3 (false, false, false, false, false, false)

def take3 (l : List Nat) (i : Nat) : Bool × Bool × Bool × Bool × Bool × Bool :=
  (l.take i).foldl step3 (false, false, false, false, false, false)

lemma take3_zero (l : List Nat) :
    take3 l 0 = (false, false, false, false, false, false) := rfl

lemma take3_length (l : List Nat) : take3 l l.length = run3 l := by
  rw [take3, List.take_length]; rfl

lemma take3_succ (l : List Nat) (i : Nat) (hi : i < l.length) :
    take3 l (i + 1) = step3 (take3 l i) l[i] := by
  rw [take3, take3, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma step3_replicate_one (v : Nat) (c1 c2 c3 ov : Bool) :
    (List.replicate v 1).foldl step3 (true, true, c1, c2, c3, ov) =
      (true, true, c1, c2, c3, ov) := by
  induction v with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    show (List.replicate n 1).foldl step3 (step3 (true, true, c1, c2, c3, ov) 1) = _
    rw [show step3 (true, true, c1, c2, c3, ov) 1 = (true, true, c1, c2, c3, ov) from rfl]
    exact ih

private def bumpCount (c1 c2 c3 ov : Bool) : Bool × Bool × Bool × Bool :=
  if c3 then (c1, c2, c3, true)
  else if c2 then (c1, c2, true, ov)
  else if c1 then (c1, true, false, ov)
  else (true, false, false, ov)

private lemma step3_encodeLit (l : literal) (p c1 c2 c3 ov : Bool) :
    (encodeLit l).foldl step3 (false, p, c1, c2, c3, ov) =
      let r := bumpCount c1 c2 c3 ov
      (false, true, r.1, r.2.1, r.2.2.1, r.2.2.2) := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).foldl step3
      (false, p, c1, c2, c3, ov) = _
  show (List.replicate v 1 ++ [0]).foldl step3
      (step3 (step3 (false, p, c1, c2, c3, ov) 1) (if pol then 1 else 0)) = _
  cases c3 <;> cases c2 <;> cases c1 <;> cases pol <;>
    simp [step3, bumpCount, List.foldl_append, step3_replicate_one]

private def countFlags (n : Nat) : Bool × Bool × Bool :=
  match n with
  | 0 => (false, false, false)
  | 1 => (true, false, false)
  | 2 => (true, true, false)
  | _ => (true, true, true)

private lemma bumpCount_countFlags (n : Nat) (ov : Bool) :
    let f := countFlags n
    bumpCount f.1 f.2.1 f.2.2 ov =
      let f' := countFlags (n + 1)
      (f'.1, f'.2.1, f'.2.2, ov || decide (3 ≤ n)) := by
  match n with
  | 0 => simp [countFlags, bumpCount]
  | 1 => simp [countFlags, bumpCount]
  | 2 => simp [countFlags, bumpCount]
  | n + 3 => simp [countFlags, bumpCount]

private lemma step3_clauseBody (C : clause) (p : Bool) (n : Nat) (ov : Bool)
    (hn : 3 < n → ov = true) :
    ∃ q, (CnfSerialize.clauseBody C).foldl step3
        (false, p, (countFlags n).1, (countFlags n).2.1, (countFlags n).2.2, ov) =
      (false, q, (countFlags (n + C.length)).1, (countFlags (n + C.length)).2.1,
        (countFlags (n + C.length)).2.2, ov || decide (3 < n + C.length)) := by
  induction C generalizing p n ov with
  | nil =>
    refine ⟨p, ?_⟩
    simp only [CnfSerialize.clauseBody, List.foldl_nil, List.length_nil, Nat.add_zero]
    by_cases h : 3 < n
    · simp [h, hn h]
    · simp [h]
  | cons l C ih =>
    rw [CnfSerialize.clauseBody_cons, List.foldl_append, step3_encodeLit]
    have hb := bumpCount_countFlags n ov
    dsimp only at hb
    rw [hb]
    have hn' : 3 < n + 1 → (ov || decide (3 ≤ n)) = true := by
      intro h; simp [show 3 ≤ n by omega]
    obtain ⟨q, hq⟩ := ih true (n + 1) (ov || decide (3 ≤ n)) hn'
    refine ⟨q, ?_⟩
    rw [hq]
    have hlen : n + 1 + C.length = n + (l :: C).length := by simp; omega
    have hover : ((ov || decide (3 ≤ n)) || decide (3 < n + 1 + C.length)) =
        (ov || decide (3 < n + (l :: C).length)) := by
      cases ov
      · by_cases h1 : 3 ≤ n
        · have h2 : 3 < n + (l :: C).length := by simp; omega
          rw [decide_eq_true h1, decide_eq_true h2]; rfl
        · simp only [Bool.false_or, decide_eq_false h1, hlen]
      · simp
    rw [hover, hlen]

private lemma step3_encodeClause (C : clause) (p : Bool) (ov : Bool) :
    (encodeClause C).foldl step3 (false, p, false, false, false, ov) =
      (false, false, false, false, false, ov || decide (3 < C.length)) := by
  obtain ⟨q, hq⟩ := step3_clauseBody C p 0 ov (by omega)
  simp only [countFlags, Nat.zero_add] at hq
  rw [CnfSerialize.encodeClause_eq, List.foldl_append, hq]
  rfl

private def anyLongClause (N : cnf) : Bool :=
  N.any (fun C => decide (3 < C.length))

private lemma anyLongClause_eq_false_iff (N : cnf) :
    anyLongClause N = false ↔ ∀ C ∈ N, C.length ≤ 3 := by
  simp only [anyLongClause, List.any_eq_false, decide_eq_true_iff, not_lt]

private lemma step3_encodeCnf (N : cnf) (ov : Bool) :
    (encodeCnf N).foldl step3 (false, false, false, false, false, ov) =
      (false, false, false, false, false, ov || anyLongClause N) := by
  induction N generalizing ov with
  | nil => simp [encodeCnf, anyLongClause]
  | cons C N ih =>
    rw [CnfSerialize.encodeCnf_cons, List.foldl_append, step3_encodeClause C false ov, ih]
    simp [anyLongClause, Bool.or_assoc]

lemma run3_encodeCnf (N : cnf) :
    (run3 (encodeCnf N)).2.2.2.2.2 = anyLongClause N := by
  simp [run3, step3_encodeCnf]

-- Scratch registers for the 3-SAT clause-length check (reusing WCUR..WSB, plus 25..28)
abbrev C1 : Var := 25
abbrev C2 : Var := 26
abbrev C3 : Var := 27
abbrev OVER : Var := 28

def check3Pre : Cmd :=
  Cmd.op (.copy WCUR CNF_STREAM) ;;
  Cmd.op (.clear WSA) ;;
  Cmd.op (.clear WSB) ;;
  Cmd.op (.clear C1) ;;
  Cmd.op (.clear C2) ;;
  Cmd.op (.clear C3) ;;
  Cmd.op (.clear OVER)

def bumpCountCmd : Cmd :=
  Cmd.ifBit C3
    (Cmd.op (.clear OVER) ;; Cmd.op (.appendOne OVER))
    (Cmd.ifBit C2
      (Cmd.op (.clear C3) ;; Cmd.op (.appendOne C3))
      (Cmd.ifBit C1
        (Cmd.op (.clear C2) ;; Cmd.op (.appendOne C2))
        (Cmd.op (.clear C1) ;; Cmd.op (.appendOne C1))))

def check3Body : Cmd :=
  Cmd.op (.head WHD WCUR) ;;
  Cmd.op (.tail WCUR WCUR) ;;
  Cmd.ifBit WSA
    (Cmd.ifBit WSB
      (Cmd.ifBit WHD (Cmd.op (.clear WHD)) (Cmd.op (.clear WSA)))
      (Cmd.op (.clear WSB) ;; Cmd.op (.appendOne WSB)))
    (Cmd.ifBit WHD
      (Cmd.op (.clear WSA) ;; Cmd.op (.appendOne WSA) ;; Cmd.op (.clear WSB) ;; bumpCountCmd)
      (Cmd.op (.clear WSB) ;; Cmd.op (.clear C1) ;; Cmd.op (.clear C2) ;; Cmd.op (.clear C3)))

def check3Post : Cmd :=
  Cmd.ifBit OVER badBranch (Cmd.op (.clear WHD))

def check3Cmd : Cmd :=
  check3Pre ;; (Cmd.forBnd WIDX WCUR check3Body ;; check3Post)

def threeSatBuild : Cmd := satStrBuild ;; check3Cmd

def threeSatMfc : Cmd := threeSatBuild ;; EvalCnfSplit.certDecode

private lemma bumpCountCmd_run (s : State) (c1 c2 c3 ov : Bool)
    (hC1 : State.get s C1 = flagOf c1)
    (hC2 : State.get s C2 = flagOf c2)
    (hC3 : State.get s C3 = flagOf c3)
    (hO : State.get s OVER = flagOf ov) :
    let t := bumpCountCmd.eval s
    let r := bumpCount c1 c2 c3 ov
    (∀ q, q ≠ C1 → q ≠ C2 → q ≠ C3 → q ≠ OVER → State.get t q = State.get s q) ∧
    State.get t C1 = flagOf r.1 ∧
    State.get t C2 = flagOf r.2.1 ∧
    State.get t C3 = flagOf r.2.2.1 ∧
    State.get t OVER = flagOf r.2.2.2 := by
  dsimp only [bumpCountCmd, bumpCount]
  cases c3
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hC3]; simp [flagOf])]
    cases c2
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hC2]; simp [flagOf])]
      cases c1
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hC1]; simp [flagOf])]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun q h1 _ _ _ => State.get_set_ne _ _ _ _ h1, ?_, ?_, ?_, ?_⟩
        · rfl
        · rw [State.get_set_ne _ C1 _ C2 (by decide)]; exact hC2
        · rw [State.get_set_ne _ C1 _ C3 (by decide)]; exact hC3
        · rw [State.get_set_ne _ C1 _ OVER (by decide)]; exact hO
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hC1]; rfl)]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
          Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun q _ h2 _ _ => State.get_set_ne _ _ _ _ h2, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ C2 _ C1 (by decide)]; exact hC1
        · rfl
        · rw [State.get_set_ne _ C2 _ C3 (by decide)]; exact hC3
        · rw [State.get_set_ne _ C2 _ OVER (by decide)]; exact hO
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hC2]; rfl)]
      simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
        Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun q _ _ h3 _ => State.get_set_ne _ _ _ _ h3, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ C3 _ C1 (by decide)]; exact hC1
      · rw [State.get_set_ne _ C3 _ C2 (by decide)]; exact hC2
      · rfl
      · rw [State.get_set_ne _ C3 _ OVER (by decide)]; exact hO
  · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hC3]; rfl)]
    simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set, ↓reduceIte]
    refine ⟨fun q _ _ _ h4 => State.get_set_ne _ _ _ _ h4, ?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ OVER _ C1 (by decide)]; exact hC1
    · rw [State.get_set_ne _ OVER _ C2 (by decide)]; exact hC2
    · rw [State.get_set_ne _ OVER _ C3 (by decide)]; exact hC3
    · rfl

set_option maxHeartbeats 1000000 in
private lemma check3Body_run (l : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hC : State.get s WCUR = l.drop i)
    (hA : State.get s WSA = flagOf (take3 l i).1)
    (hB : State.get s WSB = flagOf (take3 l i).2.1)
    (h1 : State.get s C1 = flagOf (take3 l i).2.2.1)
    (h2 : State.get s C2 = flagOf (take3 l i).2.2.2.1)
    (h3 : State.get s C3 = flagOf (take3 l i).2.2.2.2.1)
    (hO : State.get s OVER = flagOf (take3 l i).2.2.2.2.2) :
    let s' := check3Body.eval s
    State.get s' WCUR = l.drop (i + 1) ∧
    State.get s' WSA = flagOf (take3 l (i + 1)).1 ∧
    State.get s' WSB = flagOf (take3 l (i + 1)).2.1 ∧
    State.get s' C1 = flagOf (take3 l (i + 1)).2.2.1 ∧
    State.get s' C2 = flagOf (take3 l (i + 1)).2.2.2.1 ∧
    State.get s' C3 = flagOf (take3 l (i + 1)).2.2.2.2.1 ∧
    State.get s' OVER = flagOf (take3 l (i + 1)).2.2.2.2.2 := by
  have hcons : State.get s WCUR = l[i] :: l.drop (i + 1) := by
    rw [hC]; exact List.drop_eq_getElem_cons hi
  have e1 : (Cmd.op (Op.head WHD WCUR)).eval s = s.set WHD [l[i]] := by
    simp only [Cmd.eval_op, Op.eval, hcons, List.head?_cons]
  have hC1 : State.get (s.set WHD [l[i]]) WCUR = l[i] :: l.drop (i + 1) := by
    rw [State.get_set_ne s WHD _ WCUR (by decide)]; exact hcons
  have e2 : (Cmd.op (Op.tail WCUR WCUR)).eval (s.set WHD [l[i]]) =
      (s.set WHD [l[i]]).set WCUR (l.drop (i + 1)) := by
    simp only [Cmd.eval_op, Op.eval, hC1, List.tail_cons]
  dsimp only
  rw [check3Body, Cmd.eval_seq, e1, Cmd.eval_seq, e2]
  set t : State := (s.set WHD [l[i]]).set WCUR (l.drop (i + 1)) with ht
  have hT_C : State.get t WCUR = l.drop (i + 1) := State.get_set_eq _ _ _
  have hT_HD : State.get t WHD = [l[i]] := by
    rw [ht, State.get_set_ne _ WCUR _ WHD (by decide)]; exact State.get_set_eq _ _ _
  have hT_A : State.get t WSA = flagOf (take3 l i).1 := by
    rw [ht, State.get_set_ne _ WCUR _ WSA (by decide), State.get_set_ne _ WHD _ WSA (by decide)]; exact hA
  have hT_B : State.get t WSB = flagOf (take3 l i).2.1 := by
    rw [ht, State.get_set_ne _ WCUR _ WSB (by decide), State.get_set_ne _ WHD _ WSB (by decide)]; exact hB
  have hT_1 : State.get t C1 = flagOf (take3 l i).2.2.1 := by
    rw [ht, State.get_set_ne _ WCUR _ C1 (by decide), State.get_set_ne _ WHD _ C1 (by decide)]; exact h1
  have hT_2 : State.get t C2 = flagOf (take3 l i).2.2.2.1 := by
    rw [ht, State.get_set_ne _ WCUR _ C2 (by decide), State.get_set_ne _ WHD _ C2 (by decide)]; exact h2
  have hT_3 : State.get t C3 = flagOf (take3 l i).2.2.2.2.1 := by
    rw [ht, State.get_set_ne _ WCUR _ C3 (by decide), State.get_set_ne _ WHD _ C3 (by decide)]; exact h3
  have hT_O : State.get t OVER = flagOf (take3 l i).2.2.2.2.2 := by
    rw [ht, State.get_set_ne _ WCUR _ OVER (by decide), State.get_set_ne _ WHD _ OVER (by decide)]; exact hO
  rw [take3_succ l i hi]
  rcases hm : take3 l i with ⟨a, b, c1, c2, c3, ov⟩
  rw [hm] at hT_A hT_B hT_1 hT_2 hT_3 hT_O
  by_cases hcell : l[i] = 1
  · have hHD : State.get t WHD = [1] := by rw [hT_HD, hcell]
    cases a with
    | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
      cases b with
      | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl), Cmd.eval_ifBit_true _ _ _ _ hHD]
        simp only [Cmd.eval_op, Op.eval, step3, hcell, ↓reduceIte]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WHD _ WCUR (by decide)]; exact hT_C
        · rw [State.get_set_ne _ WHD _ WSA (by decide)]; exact hT_A
        · rw [State.get_set_ne _ WHD _ WSB (by decide)]; exact hT_B
        · rw [State.get_set_ne _ WHD _ C1 (by decide)]; exact hT_1
        · rw [State.get_set_ne _ WHD _ C2 (by decide)]; exact hT_2
        · rw [State.get_set_ne _ WHD _ C3 (by decide)]; exact hT_3
        · rw [State.get_set_ne _ WHD _ OVER (by decide)]; exact hT_O
      | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [flagOf])]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set, step3]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WSB _ WCUR (by decide)]; exact hT_C
        · rw [State.get_set_ne _ WSB _ WSA (by decide)]; exact hT_A
        · rfl
        · rw [State.get_set_ne _ WSB _ C1 (by decide)]; exact hT_1
        · rw [State.get_set_ne _ WSB _ C2 (by decide)]; exact hT_2
        · rw [State.get_set_ne _ WSB _ C3 (by decide)]; exact hT_3
        · rw [State.get_set_ne _ WSB _ OVER (by decide)]; exact hT_O
    | false =>
      rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [flagOf]),
        Cmd.eval_ifBit_true _ _ _ _ hHD]
      simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set, List.nil_append]
      set u : State := (t.set WSA [1]).set WSB [] with hu
      have hU_C : State.get u WCUR = l.drop (i + 1) := by
        rw [hu, State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide)]; exact hT_C
      have hU_A : State.get u WSA = [1] := by
        rw [hu, State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
      have hU_B : State.get u WSB = [] := State.get_set_eq _ _ _
      have hU_1 : State.get u C1 = flagOf c1 := by
        rw [hu, State.get_set_ne _ WSB _ C1 (by decide), State.get_set_ne _ WSA _ C1 (by decide)]; exact hT_1
      have hU_2 : State.get u C2 = flagOf c2 := by
        rw [hu, State.get_set_ne _ WSB _ C2 (by decide), State.get_set_ne _ WSA _ C2 (by decide)]; exact hT_2
      have hU_3 : State.get u C3 = flagOf c3 := by
        rw [hu, State.get_set_ne _ WSB _ C3 (by decide), State.get_set_ne _ WSA _ C3 (by decide)]; exact hT_3
      have hU_O : State.get u OVER = flagOf ov := by
        rw [hu, State.get_set_ne _ WSB _ OVER (by decide), State.get_set_ne _ WSA _ OVER (by decide)]; exact hT_O
      obtain ⟨hfr, hr1, hr2, hr3, hrO⟩ := bumpCountCmd_run u c1 c2 c3 ov hU_1 hU_2 hU_3 hU_O
      have hstep_eq : step3 (false, b, c1, c2, c3, ov) l[i] =
          let r := bumpCount c1 c2 c3 ov
          (true, false, r.1, r.2.1, r.2.2.1, r.2.2.2) := by
        cases c3 <;> cases c2 <;> cases c1 <;> simp [step3, bumpCount, hcell]
      rw [hstep_eq]
      refine ⟨?_, ?_, ?_, hr1, hr2, hr3, hrO⟩
      · rw [hfr WCUR (by decide) (by decide) (by decide) (by decide)]; exact hU_C
      · rw [hfr WSA (by decide) (by decide) (by decide) (by decide)]; exact hU_A
      · rw [hfr WSB (by decide) (by decide) (by decide) (by decide)]; exact hU_B
  · have hHD : State.get t WHD ≠ [1] := by rw [hT_HD]; simpa using hcell
    cases a with
    | true =>
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_A]; rfl)]
      cases b with
      | true =>
        rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_B]; rfl), Cmd.eval_ifBit_false _ _ _ _ hHD]
        simp only [Cmd.eval_op, Op.eval, step3, if_neg hcell]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WSA _ WCUR (by decide)]; exact hT_C
        · rw [State.get_set_eq]; rfl
        · rw [State.get_set_ne _ WSA _ WSB (by decide)]; exact hT_B
        · rw [State.get_set_ne _ WSA _ C1 (by decide)]; exact hT_1
        · rw [State.get_set_ne _ WSA _ C2 (by decide)]; exact hT_2
        · rw [State.get_set_ne _ WSA _ C3 (by decide)]; exact hT_3
        · rw [State.get_set_ne _ WSA _ OVER (by decide)]; exact hT_O
      | false =>
        rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_B]; simp [flagOf])]
        simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set, step3]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ WSB _ WCUR (by decide)]; exact hT_C
        · rw [State.get_set_ne _ WSB _ WSA (by decide)]; exact hT_A
        · rfl
        · rw [State.get_set_ne _ WSB _ C1 (by decide)]; exact hT_1
        · rw [State.get_set_ne _ WSB _ C2 (by decide)]; exact hT_2
        · rw [State.get_set_ne _ WSB _ C3 (by decide)]; exact hT_3
        · rw [State.get_set_ne _ WSB _ OVER (by decide)]; exact hT_O
    | false =>
      rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_A]; simp [flagOf]),
        Cmd.eval_ifBit_false _ _ _ _ hHD]
      simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, step3, if_neg hcell]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ C3 _ WCUR (by decide), State.get_set_ne _ C2 _ WCUR (by decide),
          State.get_set_ne _ C1 _ WCUR (by decide), State.get_set_ne _ WSB _ WCUR (by decide)]
        exact hT_C
      · rw [State.get_set_ne _ C3 _ WSA (by decide), State.get_set_ne _ C2 _ WSA (by decide),
          State.get_set_ne _ C1 _ WSA (by decide), State.get_set_ne _ WSB _ WSA (by decide)]
        exact hT_A
      · rw [State.get_set_ne _ C3 _ WSB (by decide), State.get_set_ne _ C2 _ WSB (by decide),
          State.get_set_ne _ C1 _ WSB (by decide), State.get_set_eq]; rfl
      · rw [State.get_set_ne _ C3 _ C1 (by decide), State.get_set_ne _ C2 _ C1 (by decide),
          State.get_set_eq]; rfl
      · rw [State.get_set_ne _ C3 _ C2 (by decide), State.get_set_eq]; rfl
      · rw [State.get_set_eq]; rfl
      · rw [State.get_set_ne _ C3 _ OVER (by decide), State.get_set_ne _ C2 _ OVER (by decide),
          State.get_set_ne _ C1 _ OVER (by decide), State.get_set_ne _ WSB _ OVER (by decide)]
        exact hT_O

private lemma check3Loop_run (l : List Nat) (s0 : State)
    (hC : State.get s0 WCUR = l)
    (hA : State.get s0 WSA = [])
    (hB : State.get s0 WSB = [])
    (h1 : State.get s0 C1 = [])
    (h2 : State.get s0 C2 = [])
    (h3 : State.get s0 C3 = [])
    (hO : State.get s0 OVER = []) :
    State.get ((Cmd.forBnd WIDX WCUR check3Body).eval s0) OVER =
      flagOf (run3 l).2.2.2.2.2 := by
  have hlen : (State.get s0 WCUR).length = l.length := by rw [hC]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct check3Body WIDX l.length s0
    (fun i st =>
      State.get st WCUR = l.drop i ∧
      State.get st WSA = flagOf (take3 l i).1 ∧
      State.get st WSB = flagOf (take3 l i).2.1 ∧
      State.get st C1 = flagOf (take3 l i).2.2.1 ∧
      State.get st C2 = flagOf (take3 l i).2.2.2.1 ∧
      State.get st C3 = flagOf (take3 l i).2.2.2.2.1 ∧
      State.get st OVER = flagOf (take3 l i).2.2.2.2.2)
    ⟨by simpa using hC, hA, hB, h1, h2, h3, hO⟩
    (by
      rintro i st hi ⟨hc, ha, hb, h1', h2', h3', ho⟩
      refine check3Body_run l i hi _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [State.get_set_ne _ WIDX _ WCUR (by decide)]; exact hc
      · rw [State.get_set_ne _ WIDX _ WSA (by decide)]; exact ha
      · rw [State.get_set_ne _ WIDX _ WSB (by decide)]; exact hb
      · rw [State.get_set_ne _ WIDX _ C1 (by decide)]; exact h1'
      · rw [State.get_set_ne _ WIDX _ C2 (by decide)]; exact h2'
      · rw [State.get_set_ne _ WIDX _ C3 (by decide)]; exact h3'
      · rw [State.get_set_ne _ WIDX _ OVER (by decide)]; exact ho)
  simp only [take3_length] at key
  exact key.2.2.2.2.2.2

/-- Effective CNF passed to `evalCnfCmd`: `cnfOf x` if all clauses have length ≤ 3, else `botCnf`. -/
def cnf3Of (x : List Bool) : cnf :=
  if anyLongClause (cnfOf x) then botCnf else cnfOf x

def g3Str (v : List Bool × List Bool) : cnf × assgn :=
  (cnf3Of v.1, EvalCnfSplit.decodeBits v.2)

lemma threeSatBuild_get (x c : List Bool) :
    State.get (threeSatBuild.eval (strEIn (x, c))) OUTPUT = [] ∧
    State.get (threeSatBuild.eval (strEIn (x, c))) CLAUSE_TALLY =
        List.replicate (cnf3Of x).length 1 ∧
    State.get (threeSatBuild.eval (strEIn (x, c))) CNF_STREAM = encodeCnf (cnf3Of x) ∧
    State.get (threeSatBuild.eval (strEIn (x, c))) ASSGN = strBits c := by
  obtain ⟨hOUT, hTAL, hCNF, hASS⟩ := satStrBuild_get x c
  rw [threeSatBuild, Cmd.eval_seq]
  set s := satStrBuild.eval (strEIn (x, c)) with hs
  rw [check3Cmd, Cmd.eval_seq, Cmd.eval_seq]
  set s0 := check3Pre.eval s with hs0
  have hs0_C : State.get s0 WCUR = encodeCnf (cnfOf x) := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ WCUR (by decide), State.get_set_ne _ C3 _ WCUR (by decide),
      State.get_set_ne _ C2 _ WCUR (by decide), State.get_set_ne _ C1 _ WCUR (by decide),
      State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide),
      State.get_set_eq]
    exact hCNF
  have hs0_A : State.get s0 WSA = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ WSA (by decide), State.get_set_ne _ C3 _ WSA (by decide),
      State.get_set_ne _ C2 _ WSA (by decide), State.get_set_ne _ C1 _ WSA (by decide),
      State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
  have hs0_B : State.get s0 WSB = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ WSB (by decide), State.get_set_ne _ C3 _ WSB (by decide),
      State.get_set_ne _ C2 _ WSB (by decide), State.get_set_ne _ C1 _ WSB (by decide),
      State.get_set_eq]
  have hs0_1 : State.get s0 C1 = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ C1 (by decide), State.get_set_ne _ C3 _ C1 (by decide),
      State.get_set_ne _ C2 _ C1 (by decide), State.get_set_eq]
  have hs0_2 : State.get s0 C2 = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ C2 (by decide), State.get_set_ne _ C3 _ C2 (by decide),
      State.get_set_eq]
  have hs0_3 : State.get s0 C3 = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ OVER _ C3 (by decide), State.get_set_eq]
  have hs0_O : State.get s0 OVER = [] := by
    rw [hs0, check3Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_eq]
  have hs0_frame : ∀ q : Var, q ∉ check3Pre.writes → State.get s0 q = State.get s q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  set u := (Cmd.forBnd WIDX WCUR check3Body).eval s0 with hu
  have hu_O : State.get u OVER = flagOf (anyLongClause (cnfOf x)) := by
    rw [hu, check3Loop_run (encodeCnf (cnfOf x)) s0 hs0_C hs0_A hs0_B hs0_1 hs0_2 hs0_3 hs0_O,
      run3_encodeCnf]
  have hu_frame : ∀ q : Var, q ∉ (Cmd.forBnd WIDX WCUR check3Body).writes → State.get u q = State.get s0 q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  have hu_OUT : State.get u OUTPUT = [] := by
    rw [hu_frame OUTPUT (by decide), hs0_frame OUTPUT (by decide)]; exact hOUT
  have hu_TAL : State.get u CLAUSE_TALLY = List.replicate (cnfOf x).length 1 := by
    rw [hu_frame CLAUSE_TALLY (by decide), hs0_frame CLAUSE_TALLY (by decide)]; exact hTAL
  have hu_CNF : State.get u CNF_STREAM = encodeCnf (cnfOf x) := by
    rw [hu_frame CNF_STREAM (by decide), hs0_frame CNF_STREAM (by decide)]; exact hCNF
  have hu_ASS : State.get u ASSGN = strBits c := by
    rw [hu_frame ASSGN (by decide), hs0_frame ASSGN (by decide)]; exact hASS
  dsimp only [check3Post, cnf3Of]
  cases hlong : anyLongClause (cnfOf x)
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hu_O, hlong]; simp [flagOf])]
    simp only [Cmd.eval_op, Op.eval, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ WHD _ OUTPUT (by decide)]; exact hu_OUT
    · rw [State.get_set_ne _ WHD _ CLAUSE_TALLY (by decide)]; exact hu_TAL
    · rw [State.get_set_ne _ WHD _ CNF_STREAM (by decide)]; exact hu_CNF
    · rw [State.get_set_ne _ WHD _ ASSGN (by decide)]; exact hu_ASS
  · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hu_O, hlong]; rfl)]
    simp only [badBranch, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set,
      ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.get_set_ne _ CLAUSE_TALLY _ OUTPUT (by decide),
        State.get_set_ne _ CNF_STREAM _ OUTPUT (by decide)]; exact hu_OUT
    · rfl
    · rw [State.get_set_ne _ CLAUSE_TALLY _ CNF_STREAM (by decide), State.get_set_eq]; rfl
    · rw [State.get_set_ne _ CLAUSE_TALLY _ ASSGN (by decide),
        State.get_set_ne _ CNF_STREAM _ ASSGN (by decide)]; exact hu_ASS

theorem threeSatBuild_bridge (x c : List Bool) :
    AgreeBelow 19 (threeSatBuild.eval (strEIn (x, c))) (EvalCnfSplit.satEIn (cnf3Of x, c)) := by
  obtain ⟨h0, h1, h2, h3⟩ := threeSatBuild_get x c
  have hframe : ∀ q : Var, q ∉ threeSatBuild.writes →
      State.get (threeSatBuild.eval (strEIn (x, c))) q = State.get (strEIn (x, c)) q :=
    fun q hq => Cmd.eval_get_of_not_writes _ _ q hq
  intro r hr
  interval_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rw [hframe 4 (by decide)]; rfl
  · rw [hframe 5 (by decide)]; rfl
  · rw [hframe 6 (by decide)]; rfl
  · rw [hframe 7 (by decide)]; rfl
  · rw [hframe 8 (by decide)]; rfl
  · rw [hframe 9 (by decide)]; rfl
  · rw [hframe 10 (by decide)]; rfl
  · rw [hframe 11 (by decide)]; rfl
  · rw [hframe 12 (by decide)]; rfl
  · rw [hframe 13 (by decide)]; rfl
  · rw [hframe 14 (by decide)]; rfl
  · rw [hframe 15 (by decide)]; rfl
  · rw [hframe 16 (by decide)]; rfl
  · rw [hframe 17 (by decide)]; rfl
  · rw [hframe 18 (by decide)]; rfl

theorem threeSatMfc_bridge (v : List Bool × List Bool) :
    AgreeBelow 16 (threeSatMfc.eval (strEIn v)) (encodeState (g3Str v)) := by
  rcases v with ⟨x, c⟩
  have h1 : AgreeBelow 19 (EvalCnfSplit.certDecode.eval (threeSatBuild.eval (strEIn (x, c))))
      (EvalCnfSplit.certDecode.eval (EvalCnfSplit.satEIn (cnf3Of x, c))) :=
    Cmd.eval_agree _ 19 EvalCnfSplit.certDecode_usesBelow (threeSatBuild_bridge x c)
  have h2 := EvalCnfSplit.certDecode_bridge (cnf3Of x, c)
  intro r hr
  rw [threeSatMfc, Cmd.eval_seq]
  exact (h1 r (by omega)).trans (h2 r hr)

def regs3 : Nat := 2 ^ 29 - 1

theorem threeSatMfc_chk : (threeSatMfc.chk regs3).1 = true := by decide

theorem threeSatMfc_usesBelow : Cmd.UsesBelow threeSatMfc 29 := by
  simp [threeSatMfc, threeSatBuild, check3Cmd, check3Pre, check3Body, bumpCountCmd, check3Post,
    satStrBuild, satStrPre, satStrPostA, satStrPostB, badBranch, scanBody,
    EvalCnfSplit.certDecode, EvalCnfSplit.decodeBody, Cmd.UsesBelow, Op.UsesBelow,
    WCUR, WIDX, WHD, WSA, WSB, WTAL, C1, C2, C3, OVER, EvalCnfSplit.DCUR, EvalCnfSplit.DIDX,
    EvalCnfSplit.DHD, OUTPUT, CLAUSE_TALLY, CNF_STREAM, ASSGN]

theorem threeSatMfc_cost : ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ v : List Bool × List Bool, threeSatMfc.cost (strEIn v) ≤ budget (encodable.size v) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk threeSatMfc regs3 threeSatMfc_chk
  refine ⟨fun n => K * (n + 1) ^ (D + 1), ?_, ?_, fun v => hb (strEIn v) _ (strEIn_size_le v)⟩
  · refine inOPoly_mul (inOPoly_const K) ⟨D + 1, 2 ^ (D + 1), 1, ?_⟩
    intro n hn
    calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
  · exact fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

lemma size_cnf3Of_le (x : List Bool) : encodable.size (cnf3Of x) ≤ encodable.size x + 1 := by
  dsimp only [cnf3Of]
  split
  · have hbot : encodable.size botCnf = 1 := by decide
    omega
  · exact size_cnfOf_le x

lemma size_g3Str_le (v : List Bool × List Bool) :
    encodable.size (g3Str v) ≤ gArg (encodable.size v) := by
  rcases v with ⟨x, c⟩
  have hx := size_cnf3Of_le x
  have hc := EvalCnfSplit.size_decodeBits_le c
  have hn : encodable.size ((x, c) : List Bool × List Bool)
      = encodable.size x + encodable.size c + 1 := rfl
  show encodable.size (cnf3Of x) + encodable.size (EvalCnfSplit.decodeBits c) + 1
      ≤ gArg (encodable.size ((x, c) : List Bool × List Bool))
  rw [hn]
  show _ ≤ (encodable.size x + encodable.size c + 1) * (encodable.size x + encodable.size c + 1)
    + (encodable.size x + encodable.size c + 1) + 2
  nlinarith [Nat.zero_le (encodable.size x), Nat.zero_le (encodable.size c)]

noncomputable def bound3 : Nat → Nat :=
  fun n => threeSatMfc_cost.choose n + EvalCnfTM.timeBound (gArg n) + 1

theorem bound3_poly : inOPoly bound3 :=
  inOPoly_add (inOPoly_add threeSatMfc_cost.choose_spec.1
    (inOPoly_comp (f := gArg) (g := EvalCnfTM.timeBound) gArg_poly EvalCnfTM.timeBound_inOPoly))
    (inOPoly_const 1)

theorem bound3_mono : monotonic bound3 := by
  intro a b hab
  have h1 := threeSatMfc_cost.choose_spec.2.1 a b hab
  have h2 := EvalCnfTM.timeBound_monotonic _ _ (gArg_mono a b hab)
  show _ + _ + 1 ≤ _ + _ + 1
  omega

theorem le_bound3 (n : Nat) : n ≤ bound3 n := by
  have h1 : n ≤ EvalCnfTM.timeBound (gArg n) :=
    le_trans (le_gArg n) (le_trans (le_timeBound (gArg n))
      (EvalCnfTM.timeBound_monotonic _ _ (Nat.le_refl _)))
  show n ≤ _ + _ + 1
  omega

noncomputable def precompose3Data :
    EvalCnfTM.evalCnfDecidesLang.FreePrecomposeData g3Str where
  mfc := threeSatMfc
  eIn := strEIn
  newBound := bound3
  newBound_poly := bound3_poly
  newBound_mono := bound3_mono
  bridge := threeSatMfc_bridge
  encodeIn_size := fun v => le_trans (strEIn_size_le v) (le_bound3 _)
  cost_bound := fun v => by
    have h1 : threeSatMfc.cost (strEIn v) ≤ threeSatMfc_cost.choose (encodable.size v) :=
      threeSatMfc_cost.choose_spec.2.2 v
    have h2 : evalCnfCmd.cost (threeSatMfc.eval (strEIn v)) =
        evalCnfCmd.cost (encodeState (g3Str v)) :=
      Cmd.cost_agree _ 16 evalCnfCmd_usesBelow (threeSatMfc_bridge v)
    have h3 : evalCnfCmd.cost (encodeState (g3Str v)) ≤
        EvalCnfTM.timeBound (gArg (encodable.size v)) :=
      le_trans (evalCnfCmd_cost_bound _)
        (EvalCnfTM.timeBound_monotonic _ _ (size_g3Str_le v))
    show (threeSatMfc ;; evalCnfCmd).cost (strEIn v) ≤ bound3 (encodable.size v)
    rw [Cmd.cost_seq, h2]
    show 1 + threeSatMfc.cost (strEIn v) + _ ≤ threeSatMfc_cost.choose _ + EvalCnfTM.timeBound (gArg _) + 1
    omega
  enc_bit := strEIn_bit
  regBound := 29
  usesBelow := ⟨threeSatMfc_usesBelow, Cmd.UsesBelow_mono (by omega) evalCnfCmd_usesBelow⟩
  width_le := fun v => by
    rcases v with ⟨x, c⟩
    show (strEIn (x, c)).length ≤ 29
    rw [strEIn_lit]
    simp

def threeSatRel (x c : List Bool) : Prop :=
  satisfiesCnf (EvalCnfSplit.decodeBits c) (cnf3Of x)

noncomputable def threeSatVerifier :
    DecidesLang (fun v : List Bool × List Bool => threeSatRel v.1 v.2) bound3 :=
  EvalCnfTM.evalCnfDecidesLang.precomposeFree g3Str precompose3Data

theorem threeSatRel_correct : polyCertRel threeSatLang threeSatRel := by
  obtain ⟨R⟩ := EvalCnfSplit.satRel_correct
  refine ⟨⟨fun n => R.bound (n + 1), ?_, ?_, ?_, ?_⟩⟩
  · rintro x c h
    dsimp only [threeSatRel, cnf3Of] at h
    cases hlong : anyLongClause (cnfOf x)
    · rw [hlong] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ⟨(anyLongClause_eq_false_iff (cnfOf x)).mp hlong, ⟨EvalCnfSplit.decodeBits c, h⟩⟩
    · rw [hlong] at h
      simp only [↓reduceIte] at h
      exact absurd ⟨EvalCnfSplit.decodeBits c, h⟩ not_sat_botCnf
  · rintro x ⟨hlen, hsat⟩
    obtain ⟨c, hrel, hsize⟩ := R.complete hsat
    have hlong : anyLongClause (cnfOf x) = false :=
      (anyLongClause_eq_false_iff (cnfOf x)).mpr hlen
    refine ⟨c, ?_, le_trans hsize (R.bound_mono _ _ (size_cnfOf_le x))⟩
    simp only [threeSatRel, cnf3Of, hlong, Bool.false_eq_true, ↓reduceIte]
    exact hrel
  · exact inOPoly_comp (f := fun n => n + 1) (g := R.bound)
      (inOPoly_add inOPoly_id (inOPoly_const 1)) R.bound_poly
  · exact fun a b hab => R.bound_mono _ _ (by omega)

noncomputable def threeSatWitness : CookLevin.Lang.NPWitnessStr threeSatLang where
  rel := threeSatRel
  dBound := bound3
  dBound_poly := bound3_poly
  dBound_mono := bound3_mono
  verifier := threeSatVerifier
  rel_correct := threeSatRel_correct
  encX := certState
  encodeIn_eq := fun _ _ => rfl
  xWidth := 1
  encX_width := fun _ => rfl
  encX_size := fun x => by
    have h : State.size (certState x) = x.length := CookLevin.Lang.State.size_certState x
    have h2 : x.length ≤ encodable.size x := CookLevin.length_le_size x
    have h3 := le_bound3 (encodable.size x)
    omega
  sizeLB := fun n => 2 * n
  sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
  encX_sizeLB := fun x => by
    rw [CookLevin.Lang.State.size_certState]
    exact CookLevin.size_le_two_mul_length x
  encX_canonical := fun _ => rfl

end PvsNP.Units.m3_3sat_in_np

theorem PvsNP.Units.m3_3sat_in_np :
    CookLevin.inNP (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) :=
  CookLevin.Lang.inNPCmd_inNP ⟨PvsNP.Units.m3_3sat_in_np.threeSatWitness⟩
