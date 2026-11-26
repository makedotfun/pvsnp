import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m1_flat_to_st

open Turing

/-! ## Tape `nth` lemmas for `Turing.Tape` -/

private lemma nth_zero {Γ : Type} [Inhabited Γ] (T : Tape Γ) :
    T.nth 0 = T.head := rfl

private lemma nth_write {Γ : Type} [Inhabited Γ] (T : Tape Γ) (b : Γ) (z : ℤ) :
    (T.write b).nth z = if z = 0 then b else T.nth z := by
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private lemma nth_move_left {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (T.move Dir.left).nth z = T.nth (z - 1) := by
  rcases T with ⟨a, L, R⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      show L.head = L.nth 0
      exact (ListBlank.nth_zero L).symm
    | succ k =>
      show (ListBlank.cons a R).nth k = _
      cases k with
      | zero =>
        rw [ListBlank.nth_zero, ListBlank.head_cons]; rfl
      | succ m =>
        rw [ListBlank.nth_succ, ListBlank.tail_cons]
        have h : (Int.ofNat (m + 1 + 1)) - 1 = Int.ofNat (m + 1) := by
          change ((m + 2 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ); omega
        rw [h]; rfl
  | negSucc n =>
    show L.tail.nth n = L.nth (n + 1)
    exact (ListBlank.nth_succ L n).symm

private lemma nth_move_right {Γ : Type} [Inhabited Γ] (T : Tape Γ) (z : ℤ) :
    (T.move Dir.right).nth z = T.nth (z + 1) := by
  rcases T with ⟨a, L, R⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero =>
      show R.head = R.nth 0
      exact (ListBlank.nth_zero R).symm
    | succ k =>
      show R.tail.nth k = R.nth (k + 1)
      exact (ListBlank.nth_succ R k).symm
  | negSucc n =>
    cases n with
    | zero =>
      show (ListBlank.cons a L).nth 0 = a
      rw [ListBlank.nth_zero, ListBlank.head_cons]
    | succ m =>
      show (ListBlank.cons a L).nth (m + 1) = L.nth m
      rw [ListBlank.nth_succ, ListBlank.tail_cons]

private lemma right₀_nth_eq_nth {Γ : Type} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    T.right₀.nth i = T.nth (i : ℤ) := by
  rcases T with ⟨a, L, R⟩
  cases i with
  | zero =>
    show (ListBlank.cons a R).nth 0 = a
    rw [ListBlank.nth_zero, ListBlank.head_cons]
  | succ k =>
    show (ListBlank.cons a R).nth (k + 1) = R.nth k
    rw [ListBlank.nth_succ, ListBlank.tail_cons]

private lemma nth_mk₁ {Γ : Type} [Inhabited Γ] (l : List Γ) (z : ℤ) :
    (Tape.mk₁ l).nth z =
      match z with
      | Int.ofNat n => l.getD n default
      | Int.negSucc _ => default := by
  cases z with
  | ofNat n =>
    cases l with
    | nil =>
      cases n with
      | zero => rfl
      | succ k =>
        show (ListBlank.mk ([] : List Γ)).nth k = default
        rw [ListBlank.nth_mk]; rfl
    | cons a rest =>
      cases n with
      | zero => rfl
      | succ k =>
        show (ListBlank.mk rest).nth k = rest.getD k default
        rw [ListBlank.nth_mk]
        simp [List.getI, List.getD_eq_getElem?_getD]
  | negSucc n =>
    show (ListBlank.mk ([] : List Γ)).nth n = default
    rw [ListBlank.nth_mk]; rfl

/-! ## Step-reachability helper for `TM0` -/

private def Reaches {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (c₁ c₂ : TM0.Cfg Γ Λ) (k : ℕ) : Prop :=
  (flip bind (TM0.step δ))^[k] (some c₁) = some c₂

private lemma reaches_refl {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (c : TM0.Cfg Γ Λ) : Reaches δ c c 0 := rfl

private lemma reaches_step {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) {c₁ c₂ : TM0.Cfg Γ Λ}
    (h : TM0.step δ c₁ = some c₂) : Reaches δ c₁ c₂ 1 := by
  unfold Reaches; simp [flip, h]

private lemma reaches_trans {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) {c₁ c₂ c₃ : TM0.Cfg Γ Λ} {k₁ k₂ : ℕ}
    (h1 : Reaches δ c₁ c₂ k₁) (h2 : Reaches δ c₂ c₃ k₂) :
    Reaches δ c₁ c₃ (k₁ + k₂) := by
  unfold Reaches at h1 h2 ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

private lemma step_write {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (q q' : Λ) (T : Tape Γ) (b : Γ)
    (h : δ q T.head = some (q', TM0.Stmt.write b)) :
    TM0.step δ ⟨q, T⟩ = some ⟨q', T.write b⟩ := by
  simp [TM0.step, h]

private lemma step_move {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (δ : TM0.Machine Γ Λ) (q q' : Λ) (T : Tape Γ) (d : Dir)
    (h : δ q T.head = some (q', TM0.Stmt.move d)) :
    TM0.step δ ⟨q, T⟩ = some ⟨q', T.move d⟩ := by
  simp [TM0.step, h]

/-! ## Simulation alphabet and states -/

inductive SimSym (N : ℕ) : Type where
  | blank
  | inpBit (b : Bool)
  | outBit (b : Bool)
  | leftWall
  | cell (v : Fin N)
  | frontier
  deriving DecidableEq

instance (N : ℕ) : Inhabited (SimSym N) := ⟨SimSym.blank⟩

instance (N : ℕ) : Fintype (SimSym N) :=
  Fintype.ofEquiv (Unit ⊕ Bool ⊕ Bool ⊕ Unit ⊕ Fin N ⊕ Unit)
    { toFun := fun
        | .inl () => .blank
        | .inr (.inl b) => .inpBit b
        | .inr (.inr (.inl b)) => .outBit b
        | .inr (.inr (.inr (.inl ()))) => .leftWall
        | .inr (.inr (.inr (.inr (.inl v)))) => .cell v
        | .inr (.inr (.inr (.inr (.inr ())))) => .frontier
      invFun := fun
        | .blank => .inl ()
        | .inpBit b => .inr (.inl b)
        | .outBit b => .inr (.inr (.inl b))
        | .leftWall => .inr (.inr (.inr (.inl ())))
        | .cell v => .inr (.inr (.inr (.inr (.inl v))))
        | .frontier => .inr (.inr (.inr (.inr (.inr ()))))
      left_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl }

inductive SimState (S N : ℕ) : Type where
  | initLeft
  | initWriteWall
  | initBack0
  | initShiftWrite (carry : Fin N)
  | initShiftMove (nextCarry : Fin N)
  | initEndMove0
  | initEndWrite0
  | initEndMove3
  | initEndWrite3
  | initEndMoveF
  | initEndWriteF
  | initRewind
  | sim (q : Fin S)
  | frontMoveR (q' : Fin S) (d : TMMove)
  | frontWriteF (q' : Fin S) (d : TMMove)
  | frontMoveL (q' : Fin S) (d : TMMove)
  | doMove (q' : Fin S) (d : TMMove)
  | checkLeftWall (q' : Fin S)
  | outRewind
  | outAt0
  | outScan
  | outScanMove
  | outBack
  | halt
  deriving DecidableEq

instance (S N : ℕ) : Inhabited (SimState S N) := ⟨SimState.initLeft⟩

private def tmMoveEquiv : TMMove ≃ Fin 3 where
  toFun := fun | .Lmove => 0 | .Rmove => 1 | .Nmove => 2
  invFun := fun | ⟨0, _⟩ => .Lmove | ⟨1, _⟩ => .Rmove | ⟨2, _⟩ => .Nmove
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ⟨i, hi⟩; interval_cases i <;> rfl

instance (S N : ℕ) : Fintype (SimState S N) :=
  Fintype.ofEquiv
    (Fin 16 ⊕ Fin N ⊕ Fin N ⊕ Fin S ⊕
      (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ (Fin S × Fin 3) ⊕ Fin S)
    { toFun := fun
        | .inl ⟨0, _⟩ => .initLeft
        | .inl ⟨1, _⟩ => .initWriteWall
        | .inl ⟨2, _⟩ => .initBack0
        | .inl ⟨3, _⟩ => .initEndMove0
        | .inl ⟨4, _⟩ => .initEndWrite0
        | .inl ⟨5, _⟩ => .initEndMove3
        | .inl ⟨6, _⟩ => .initEndWrite3
        | .inl ⟨7, _⟩ => .initEndMoveF
        | .inl ⟨8, _⟩ => .initEndWriteF
        | .inl ⟨9, _⟩ => .initRewind
        | .inl ⟨10, _⟩ => .outRewind
        | .inl ⟨11, _⟩ => .outAt0
        | .inl ⟨12, _⟩ => .outScan
        | .inl ⟨13, _⟩ => .outScanMove
        | .inl ⟨14, _⟩ => .outBack
        | .inl ⟨15, _⟩ => .halt
        | .inl ⟨_ + 16, h⟩ => absurd h (by omega)
        | .inr (.inl c) => .initShiftWrite c
        | .inr (.inr (.inl c)) => .initShiftMove c
        | .inr (.inr (.inr (.inl q))) => .sim q
        | .inr (.inr (.inr (.inr (.inl (q, m))))) => .frontMoveR q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inl (q, m)))))) => .frontWriteF q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m))))))) => .frontMoveL q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, m)))))))) => .doMove q (tmMoveEquiv.symm m)
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q))))))) => .checkLeftWall q
      invFun := fun
        | .initLeft => .inl 0
        | .initWriteWall => .inl 1
        | .initBack0 => .inl 2
        | .initEndMove0 => .inl 3
        | .initEndWrite0 => .inl 4
        | .initEndMove3 => .inl 5
        | .initEndWrite3 => .inl 6
        | .initEndMoveF => .inl 7
        | .initEndWriteF => .inl 8
        | .initRewind => .inl 9
        | .outRewind => .inl 10
        | .outAt0 => .inl 11
        | .outScan => .inl 12
        | .outScanMove => .inl 13
        | .outBack => .inl 14
        | .halt => .inl 15
        | .initShiftWrite c => .inr (.inl c)
        | .initShiftMove c => .inr (.inr (.inl c))
        | .sim q => .inr (.inr (.inr (.inl q)))
        | .frontMoveR q d => .inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d)))))
        | .frontWriteF q d => .inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d))))))
        | .frontMoveL q d => .inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d)))))))
        | .doMove q d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, tmMoveEquiv d))))))))
        | .checkLeftWall q => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr q)))))))
      left_inv := by
        rintro (⟨i, hi⟩ | c | c | q | ⟨q, m⟩ | ⟨q, m⟩ | ⟨q, m⟩ | ⟨q, m⟩ | q)
        · interval_cases i <;> rfl
        · rfl
        · rfl
        · rfl
        · simp
        · simp
        · simp
        · simp
        · rfl
      right_inv := by
        intro st
        cases st <;> simp }

/-! ## Transition function for simulating a 1-tape `FlatTM` -/

private def simDelta (M : FlatTM) (hvalid : validFlatTM M) :
    TM0.Machine (SimSym (max M.sig 4)) (SimState M.states (max M.sig 4)) :=
  let N := max M.sig 4
  have h4 : 4 ≤ N := le_max_right _ _
  let c0 : Fin N := ⟨0, by omega⟩
  let c1 : Fin N := ⟨1, by omega⟩
  let c2 : Fin N := ⟨2, by omega⟩
  let c3 : Fin N := ⟨3, by omega⟩
  let qStart : Fin M.states := ⟨M.start, hvalid.1⟩
  fun st sym =>
    match st with
    | .initLeft => some (.initWriteWall, .move .left)
    | .initWriteWall => some (.initBack0, .write .leftWall)
    | .initBack0 => some (.initShiftWrite c3, .move .right)
    | .initShiftWrite carry =>
      match sym with
      | .inpBit b => some (.initShiftMove (if b then c2 else c1), .write (.cell carry))
      | _ => some (.initEndMove0, .write (.cell carry))
    | .initShiftMove nextCarry => some (.initShiftWrite nextCarry, .move .right)
    | .initEndMove0 => some (.initEndWrite0, .move .right)
    | .initEndWrite0 => some (.initEndMove3, .write (.cell c0))
    | .initEndMove3 => some (.initEndWrite3, .move .right)
    | .initEndWrite3 => some (.initEndMoveF, .write (.cell c3))
    | .initEndMoveF => some (.initEndWriteF, .move .right)
    | .initEndWriteF => some (.initRewind, .write .frontier)
    | .initRewind =>
      match sym with
      | .leftWall => some (.sim qStart, .move .right)
      | _ => some (.initRewind, .move .left)
    | .sim q =>
      if M.halt.getD q.val false then
        some (.outRewind, .write sym)
      else
        let cur : Option ℕ :=
          match sym with
          | .cell v => some v.val
          | _ => none
        match M.trans.find? (fun e => e.src_state == q.val && decide (e.src_tape_vals = [cur])) with
        | none => some (.outRewind, .write sym)
        | some e =>
          let q' : Fin M.states := if h : e.dst_state < M.states then ⟨e.dst_state, h⟩ else q
          let w : Option ℕ := e.dst_write_vals.headD none
          let d : TMMove := e.move_dirs.headD .Nmove
          match w with
          | none => some (.doMove q' d, .write sym)
          | some v =>
            let vf : Fin N := if h : v < N then ⟨v, h⟩ else c0
            match sym with
            | .cell _ => some (.doMove q' d, .write (.cell vf))
            | .frontier => some (.frontMoveR q' d, .write (.cell vf))
            | _ => some (.doMove q' d, .write sym)
    | .frontMoveR q' d => some (.frontWriteF q' d, .move .right)
    | .frontWriteF q' d => some (.frontMoveL q' d, .write .frontier)
    | .frontMoveL q' d => some (.doMove q' d, .move .left)
    | .doMove q' d =>
      match d with
      | .Nmove => some (.sim q', .write sym)
      | .Rmove => some (.sim q', .move .right)
      | .Lmove => some (.checkLeftWall q', .move .left)
    | .checkLeftWall q' =>
      match sym with
      | .leftWall => some (.sim q', .move .right)
      | _ => some (.sim q', .write sym)
    | .outRewind =>
      match sym with
      | .leftWall => some (.outAt0, .move .right)
      | _ => some (.outRewind, .move .left)
    | .outAt0 =>
      match sym with
      | .frontier => some (.halt, .write sym)
      | _ => some (.outScan, .move .right)
    | .outScan =>
      match sym with
      | .cell v =>
        if v.val ≠ 0 ∧ v.val ≠ 3 then
          some (.outScanMove, .write (.outBit (v.val == 2)))
        else
          some (.outBack, .move .left)
      | _ => some (.outBack, .move .left)
    | .outScanMove => some (.outScan, .move .right)
    | .outBack =>
      match sym with
      | .outBit _ => some (.outBack, .move .left)
      | _ => some (.halt, .move .right)
    | .halt => none

private def simMachine (M : FlatTM) (hvalid : validFlatTM M) :
    PvsNP.SingleTape.Machine Bool Bool where
  Γ := SimSym (max M.sig 4)
  Λ := SimState M.states (max M.sig 4)
  inp := SimSym.inpBit
  out := SimSym.outBit
  inp_injective := fun _ _ h => SimSym.inpBit.inj h
  out_injective := fun _ _ h => SimSym.outBit.inj h
  inp_ne_blank := fun _ h => by cases h
  out_ne_blank := fun _ h => by cases h
  δ := simDelta M hvalid

/-! ## Tape invariant -/

private def TapeMatch (N : ℕ) (T : Tape (SimSym N)) (head : ℕ) (right : List ℕ) : Prop :=
  (∀ k : ℤ, k < -1 → T.nth (k - head) = SimSym.blank) ∧
  T.nth (-1 - head) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < right.length),
    ∃ hlt : right[i] < N, T.nth ((i : ℤ) - head) = SimSym.cell ⟨right[i], hlt⟩) ∧
  T.nth ((right.length : ℤ) - head) = SimSym.frontier ∧
  (∀ i : ℕ, right.length < i → T.nth ((i : ℤ) - head) = SimSym.blank)

private lemma tapeMatch_head_lt {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hlt : head < right.length) :
    ∃ hv : right[head] < N, T.head = SimSym.cell ⟨right[head], hv⟩ := by
  obtain ⟨hv, heq⟩ := h.2.2.1 head hlt
  refine ⟨hv, ?_⟩
  have hz : ((head : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at heq
  exact heq

private lemma tapeMatch_head_eq {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (heq : head = right.length) :
    T.head = SimSym.frontier := by
  have h1 := h.2.2.2.1
  have hz : ((right.length : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at h1
  exact h1

private lemma tapeMatch_head_gt {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hgt : right.length < head) :
    T.head = SimSym.blank := by
  have h1 := h.2.2.2.2 head hgt
  have hz : ((head : ℤ) - head) = 0 := by omega
  rw [hz, nth_zero] at h1
  exact h1

private lemma tapeMatch_move_right {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) :
    TapeMatch N (T.move Dir.right) (head + 1) right := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_move_right, show k - (head + 1 : ℕ) + 1 = k - head by omega]; exact h1 k hk
  · rw [nth_move_right, show (-1 : ℤ) - (head + 1 : ℕ) + 1 = -1 - head by omega]; exact h2
  · obtain ⟨hv, heq⟩ := h3 i hi
    refine ⟨hv, ?_⟩
    rw [nth_move_right, show (i : ℤ) - (head + 1 : ℕ) + 1 = (i : ℤ) - head by omega]; exact heq
  · rw [nth_move_right, show (right.length : ℤ) - (head + 1 : ℕ) + 1 = (right.length : ℤ) - head by omega]
    exact h4
  · rw [nth_move_right, show (i : ℤ) - (head + 1 : ℕ) + 1 = (i : ℤ) - head by omega]; exact h5 i hi

private lemma tapeMatch_move_left {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T (head + 1) right) :
    TapeMatch N (T.move Dir.left) head right := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_move_left, show k - head - 1 = k - (head + 1 : ℕ) by omega]; exact h1 k hk
  · rw [nth_move_left, show (-1 : ℤ) - head - 1 = -1 - (head + 1 : ℕ) by omega]; exact h2
  · obtain ⟨hv, heq⟩ := h3 i hi
    refine ⟨hv, ?_⟩
    rw [nth_move_left, show (i : ℤ) - head - 1 = (i : ℤ) - (head + 1 : ℕ) by omega]; exact heq
  · rw [nth_move_left, show (right.length : ℤ) - head - 1 = (right.length : ℤ) - (head + 1 : ℕ) by omega]
    exact h4
  · rw [nth_move_left, show (i : ℤ) - head - 1 = (i : ℤ) - (head + 1 : ℕ) by omega]; exact h5 i hi

private lemma tapeMatch_write_in_range {N : ℕ} {T : Tape (SimSym N)} {head : ℕ} {right : List ℕ}
    (h : TapeMatch N T head right) (hlt : head < right.length) (v : Fin N) :
    TapeMatch N (T.write (.cell v)) head (right.take head ++ v.val :: right.drop (head + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hlen : (right.take head ++ v.val :: right.drop (head + 1)).length = right.length := by
    simp [List.length_take, List.length_drop]; omega
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [nth_write, if_neg (by omega)]; exact h1 k hk
  · rw [nth_write, if_neg (by omega)]; exact h2
  · by_cases hieq : i = head
    · subst hieq
      have hget : (right.take i ++ v.val :: right.drop (i + 1))[i] = v.val := by
        rw [List.getElem_append_right (by simp)]
        simp [List.length_take, Nat.le_of_lt hlt]
      refine ⟨by rw [hget]; exact v.isLt, ?_⟩
      rw [nth_write, if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
    · have hi' : i < right.length := by omega
      have hget : (right.take head ++ v.val :: right.drop (head + 1))[i] = right[i] := by
        by_cases hlti : i < head
        · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
        · have hgt : head < i := by omega
          rw [List.getElem_append_right (by simp; omega)]
          have hltake : (right.take head).length = head := by simp; omega
          have hsub : i - (right.take head).length = (i - head - 1) + 1 := by omega
          simp only [hsub, List.getElem_cons_succ, List.getElem_drop]
          congr 1; omega
      obtain ⟨hv, heq⟩ := h3 i hi'
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [nth_write, if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
  · rw [hlen, nth_write, if_neg (by omega)]; exact h4
  · rw [hlen] at hi; rw [nth_write, if_neg (by omega)]; exact h5 i hi

private lemma tapeMatch_write_frontier {N : ℕ} {T : Tape (SimSym N)} {right : List ℕ}
    (h : TapeMatch N T right.length right) (v : Fin N) :
    TapeMatch N ((((T.write (.cell v)).move .right).write .frontier).move .left)
      right.length (right ++ [v.val]) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hstep : ∀ z : ℤ,
      ((((T.write (.cell v)).move .right).write .frontier).move .left).nth z =
        if z = 1 then .frontier else if z = 0 then .cell v else T.nth z := by
    intro z
    rw [nth_move_left, nth_write]
    by_cases hz1 : z = 1
    · subst hz1; simp
    · rw [if_neg (by omega), if_neg hz1, nth_move_right, show z - 1 + 1 = z by omega, nth_write]
  have hlen : (right ++ [v.val]).length = right.length + 1 := by simp
  refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h1 k hk
  · rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h2
  · rw [hlen] at hi
    by_cases hilt : i < right.length
    · have hget : (right ++ [v.val])[i] = right[i] := List.getElem_append_left hilt
      obtain ⟨hv, heq⟩ := h3 i hilt
      refine ⟨by rw [hget]; exact hv, ?_⟩
      rw [hstep, if_neg (by omega), if_neg (by omega), heq]
      congr 1; exact Fin.ext hget.symm
    · have hieq : i = right.length := by omega
      subst hieq
      have hget : (right ++ [v.val])[right.length] = v.val := by simp
      refine ⟨by rw [hget]; exact v.isLt, ?_⟩
      rw [hstep, if_neg (by omega), if_pos (by omega)]
      congr 1; exact Fin.ext hget.symm
  · rw [hlen, hstep, if_pos (by omega)]
  · rw [hlen] at hi
    rw [hstep, if_neg (by omega), if_neg (by omega)]; exact h5 i (by omega)

/-! ## Phase 1: Init (`M.init x` → `TapeMatch` of `stringTape x` at head 0) -/

private lemma init_rewind_loop (M : FlatTM) (hvalid : validFlatTM M)
    (right : List ℕ) :
    ∀ (head : ℕ) (T : Tape (SimSym (max M.sig 4))),
      TapeMatch (max M.sig 4) T head right →
      ∃ T', Reaches (simDelta M hvalid) ⟨.initRewind, T⟩ ⟨.sim ⟨M.start, hvalid.1⟩, T'⟩ (head + 2) ∧
        TapeMatch (max M.sig 4) T' 0 right := by
  intro head
  induction head with
  | zero =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      cases right with
      | nil => rw [tapeMatch_head_eq hT rfl]; intro h; cases h
      | cons r rs =>
        obtain ⟨_, heq⟩ := tapeMatch_head_lt hT (by simp)
        rw [heq]; intro h; cases h
    have hstep1 : TM0.step (simDelta M hvalid) ⟨.initRewind, T⟩ = some ⟨.initRewind, T.move .left⟩ := by
      apply step_move
      unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    have hwall : (T.move .left).head = SimSym.leftWall := by
      rw [← nth_zero, nth_move_left]
      have h2 := hT.2.1
      simpa using h2
    have hstep2 : TM0.step (simDelta M hvalid) ⟨.initRewind, T.move .left⟩ =
        some ⟨.sim ⟨M.start, hvalid.1⟩, (T.move .left).move .right⟩ := by
      apply step_move
      simp [simDelta, hwall]
    have h12 : Reaches (simDelta M hvalid) ⟨.initRewind, T⟩
        ⟨.sim ⟨M.start, hvalid.1⟩, (T.move .left).move .right⟩ (0 + 2) := by
      show Reaches (simDelta M hvalid) ⟨.initRewind, T⟩
        ⟨.sim ⟨M.start, hvalid.1⟩, (T.move .left).move .right⟩ (1 + 1)
      exact reaches_trans (simDelta M hvalid) (reaches_step (simDelta M hvalid) hstep1)
        (reaches_step (simDelta M hvalid) hstep2)
    refine ⟨(T.move .left).move .right, h12, ?_⟩
    have hsame : ∀ z : ℤ, ((T.move .left).move .right).nth z = T.nth z := by
      intro z; rw [nth_move_right, nth_move_left]; congr 1; omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT
    exact ⟨fun k hk => by rw [hsame]; exact h1 k hk, by rw [hsame]; exact h2,
      fun i hi => by obtain ⟨hv, heq⟩ := h3 i hi; exact ⟨hv, by rw [hsame]; exact heq⟩,
      by rw [hsame]; exact h4, fun i hi => by rw [hsame]; exact h5 i hi⟩
  | succ k ih =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      rcases lt_trichotomy (k + 1) right.length with hlt | heq | hgt
      · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT hlt; rw [hhd]; intro h; cases h
      · rw [tapeMatch_head_eq hT heq]; intro h; cases h
      · rw [tapeMatch_head_gt hT hgt]; intro h; cases h
    have hstep1 : TM0.step (simDelta M hvalid) ⟨.initRewind, T⟩ = some ⟨.initRewind, T.move .left⟩ := by
      apply step_move
      unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    obtain ⟨T', hreach, hT'⟩ := ih (T.move .left) (tapeMatch_move_left hT)
    refine ⟨T', ?_, hT'⟩
    have htot := reaches_trans _ (reaches_step _ hstep1) hreach
    have hcnt : 1 + (k + 2) = k + 1 + 2 := by omega
    rwa [hcnt] at htot

private def InitShiftInv (N : ℕ) (T : Tape (SimSym N)) (pos : ℕ)
    (written : List ℕ) (rem : List Bool) : Prop :=
  written.length = pos ∧
  (∀ k : ℤ, k < -1 → T.nth (k - pos) = SimSym.blank) ∧
  T.nth (-1 - pos) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < written.length),
    ∃ hv : written[i] < N, T.nth ((i : ℤ) - pos) = SimSym.cell ⟨written[i], hv⟩) ∧
  (∀ (j : ℕ) (hj : j < rem.length), T.nth (j : ℤ) = SimSym.inpBit rem[j]) ∧
  (∀ j : ℕ, rem.length ≤ j → T.nth (j : ℤ) = SimSym.blank)

private def InitDoneInv (N : ℕ) (T : Tape (SimSym N)) (pos : ℕ) (written : List ℕ) : Prop :=
  written.length = pos + 1 ∧
  (∀ k : ℤ, k < -1 → T.nth (k - pos) = SimSym.blank) ∧
  T.nth (-1 - pos) = SimSym.leftWall ∧
  (∀ (i : ℕ) (hi : i < written.length),
    ∃ hv : written[i] < N, T.nth ((i : ℤ) - pos) = SimSym.cell ⟨written[i], hv⟩) ∧
  (∀ j : ℕ, 1 ≤ j → T.nth (j : ℤ) = SimSym.blank)

private lemma init_shift_loop (M : FlatTM) (hvalid : validFlatTM M) :
    ∀ (rem : List Bool) (written : List ℕ) (carry : Fin (max M.sig 4))
      (T : Tape (SimSym (max M.sig 4))),
      InitShiftInv (max M.sig 4) T written.length written rem →
      ∃ T', Reaches (simDelta M hvalid) ⟨.initShiftWrite carry, T⟩
          ⟨.initEndMove0, T'⟩ (2 * rem.length + 1) ∧
        InitDoneInv (max M.sig 4) T' (written.length + rem.length)
          (written ++ carry.val :: CookLevin.symbolsOf rem) := by
  intro rem
  induction rem with
  | nil =>
    intro written carry T hInv
    have hhd : T.head = SimSym.blank := by
      rw [← nth_zero]; exact hInv.2.2.2.2.2 0 (by simp)
    have hstep : TM0.step (simDelta M hvalid) ⟨.initShiftWrite carry, T⟩ =
        some ⟨.initEndMove0, T.write (.cell carry)⟩ := by
      apply step_write
      simp [simDelta, hhd]
    refine ⟨T.write (.cell carry), reaches_step _ hstep, ?_⟩
    obtain ⟨_, h1, h2, h3, _, h5⟩ := hInv
    refine ⟨by simp [CookLevin.symbolsOf], fun k hk => ?_, ?_, fun i hi => ?_, fun j hj => ?_⟩
    · rw [nth_write, if_neg (by omega)]; simpa using h1 k hk
    · rw [nth_write, if_neg (by omega)]; simpa using h2
    · simp only [CookLevin.symbolsOf, List.map_nil, List.length_append, List.length_cons,
        List.length_nil] at hi
      by_cases hilt : i < written.length
      · have hget : (written ++ carry.val :: CookLevin.symbolsOf [])[i] = written[i] :=
          List.getElem_append_left hilt
        obtain ⟨hv, heq⟩ := h3 i hilt
        refine ⟨by rw [hget]; exact hv, ?_⟩
        rw [nth_write, if_neg (by omega)]
        simpa [hget] using heq
      · have hieq : i = written.length := by omega
        subst hieq
        have hget : (written ++ carry.val :: CookLevin.symbolsOf [])[written.length] = carry.val := by
          simp [CookLevin.symbolsOf]
        refine ⟨by rw [hget]; exact carry.isLt, ?_⟩
        rw [nth_write, if_pos (by simp)]
        congr 1; exact Fin.ext hget.symm
    · rw [nth_write, if_neg (by omega)]; exact h5 j (by simp)
  | cons b bs ih =>
    intro written carry T hInv
    have hhd : T.head = SimSym.inpBit b := by
      rw [← nth_zero]
      have := hInv.2.2.2.2.1 0 (by simp)
      simpa using this
    let nextC : Fin (max M.sig 4) :=
      if b then ⟨2, by omega⟩ else ⟨1, by omega⟩
    have hstep1 : TM0.step (simDelta M hvalid) ⟨.initShiftWrite carry, T⟩ =
        some ⟨.initShiftMove nextC, T.write (.cell carry)⟩ := by
      apply step_write
      simp [simDelta, hhd, nextC]
    have hstep2 : TM0.step (simDelta M hvalid) ⟨.initShiftMove nextC, T.write (.cell carry)⟩ =
        some ⟨.initShiftWrite nextC, (T.write (.cell carry)).move .right⟩ := by
      apply step_move
      simp [simDelta]
    have hInv' : InitShiftInv (max M.sig 4) ((T.write (.cell carry)).move .right)
        (written ++ [carry.val]).length (written ++ [carry.val]) bs := by
      obtain ⟨_, h1, h2, h3, h4, h5⟩ := hInv
      have hlen : (written ++ [carry.val]).length = written.length + 1 := by simp
      refine ⟨rfl, fun k hk => ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩
      · rw [hlen, nth_move_right, nth_write, if_neg (by omega)]
        rw [show k - (written.length + 1 : ℕ) + 1 = k - written.length by omega]
        exact h1 k hk
      · rw [hlen, nth_move_right, nth_write, if_neg (by omega)]
        rw [show (-1 : ℤ) - (written.length + 1 : ℕ) + 1 = -1 - written.length by omega]
        exact h2
      · rw [hlen] at hi ⊢
        rw [nth_move_right, show (i : ℤ) - (written.length + 1 : ℕ) + 1 = (i : ℤ) - written.length by omega]
        by_cases hilt : i < written.length
        · have hget : (written ++ [carry.val])[i] = written[i] := List.getElem_append_left hilt
          obtain ⟨hv, heq⟩ := h3 i hilt
          refine ⟨by rw [hget]; exact hv, ?_⟩
          rw [nth_write, if_neg (by omega), heq]
          congr 1; exact Fin.ext hget.symm
        · have hieq : i = written.length := by omega
          subst hieq
          have hget : (written ++ [carry.val])[written.length] = carry.val := by simp
          refine ⟨by rw [hget]; exact carry.isLt, ?_⟩
          rw [nth_write, if_pos (by omega)]
          congr 1; exact Fin.ext hget.symm
      · rw [nth_move_right, nth_write, if_neg (by omega)]
        have := h4 (j + 1) (by simp; omega)
        simpa using this
      · rw [nth_move_right, nth_write, if_neg (by omega)]
        have := h5 (j + 1) (by simp; omega)
        simpa using this
    obtain ⟨T', hreach, hDone⟩ := ih (written ++ [carry.val]) nextC _ hInv'
    refine ⟨T', ?_, ?_⟩
    · have htot := reaches_trans _ (reaches_trans _ (reaches_step _ hstep1) (reaches_step _ hstep2)) hreach
      have hlen : 1 + 1 + (2 * bs.length + 1) = 2 * (b :: bs).length + 1 := by simp; omega
      rw [hlen] at htot
      exact htot
    · have hnextVal : nextC.val = (if b then 2 else 1) := by cases b <;> rfl
      have hlist : written ++ [carry.val] ++ nextC.val :: CookLevin.symbolsOf bs =
          written ++ carry.val :: CookLevin.symbolsOf (b :: bs) := by
        simp [CookLevin.symbolsOf, hnextVal, List.append_assoc]
      have hpos : (written ++ [carry.val]).length + bs.length =
          written.length + (b :: bs).length := by simp; omega
      rw [hlist, hpos] at hDone
      exact hDone

private lemma phase1_init (M : FlatTM) (hvalid : validFlatTM M) (x : List Bool) :
    ∃ T', Reaches (simDelta M hvalid)
        ⟨SimState.initLeft, Tape.mk₁ (x.map SimSym.inpBit)⟩
        ⟨SimState.sim ⟨M.start, hvalid.1⟩, T'⟩ (3 * x.length + 15) ∧
      TapeMatch (max M.sig 4) T' 0 (CookLevin.stringTape x) := by
  let N := max M.sig 4
  let T0 : Tape (SimSym N) := Tape.mk₁ (x.map SimSym.inpBit)
  show ∃ T', Reaches (simDelta M hvalid) ⟨SimState.initLeft, T0⟩ _ _ ∧ _
  have hs1 : TM0.step (simDelta M hvalid) ⟨.initLeft, T0⟩ = some ⟨.initWriteWall, T0.move .left⟩ :=
    step_move _ _ _ _ _ rfl
  have hs2 : TM0.step (simDelta M hvalid) ⟨.initWriteWall, T0.move .left⟩ =
      some ⟨.initBack0, (T0.move .left).write .leftWall⟩ :=
    step_write _ _ _ _ _ rfl
  let T1 := ((T0.move .left).write .leftWall).move .right
  have hs3 : TM0.step (simDelta M hvalid) ⟨.initBack0, (T0.move .left).write .leftWall⟩ =
      some ⟨.initShiftWrite ⟨3, by omega⟩, T1⟩ :=
    step_move _ _ _ _ _ rfl
  have hT1_nth : ∀ z : ℤ, T1.nth z = if z = -1 then .leftWall else T0.nth z := by
    intro z
    simp only [T1, nth_move_right, nth_write]
    by_cases hz : z = -1
    · subst hz; simp
    · rw [if_neg (by omega), if_neg hz, nth_move_left, show z + 1 - 1 = z by omega]
  have hInv0 : InitShiftInv N T1 0 [] x := by
    refine ⟨rfl, fun k hk => ?_, ?_, fun i hi => by simp at hi, fun j hj => ?_, fun j hj => ?_⟩
    · rw [hT1_nth, if_neg (by omega), nth_mk₁]
      cases hk' : k - (0 : ℕ) with
      | ofNat n =>
        have h0 : (0 : ℤ) ≤ Int.ofNat n := Int.ofNat_nonneg n
        omega
      | negSucc _ => rfl
    · rw [hT1_nth, if_pos (by omega)]
    · rw [hT1_nth, if_neg (by omega), nth_mk₁]
      simp [List.getD_eq_getElem?_getD, hj]
    · rw [hT1_nth, if_neg (by omega), nth_mk₁]
      dsimp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
  obtain ⟨T2, hrShift, hDone⟩ := init_shift_loop M hvalid x [] ⟨3, by omega⟩ T1 hInv0
  -- Append 0, 3, frontier (6 steps)
  let T3 := T2.move .right
  let T4 := T3.write (.cell ⟨0, by omega⟩)
  let T5 := T4.move .right
  let T6 := T5.write (.cell ⟨3, by omega⟩)
  let T7 := T6.move .right
  let T8 := T7.write .frontier
  have ha1 : TM0.step (simDelta M hvalid) ⟨.initEndMove0, T2⟩ = some ⟨.initEndWrite0, T3⟩ :=
    step_move _ _ _ _ _ rfl
  have ha2 : TM0.step (simDelta M hvalid) ⟨.initEndWrite0, T3⟩ = some ⟨.initEndMove3, T4⟩ :=
    step_write _ _ _ _ _ rfl
  have ha3 : TM0.step (simDelta M hvalid) ⟨.initEndMove3, T4⟩ = some ⟨.initEndWrite3, T5⟩ :=
    step_move _ _ _ _ _ rfl
  have ha4 : TM0.step (simDelta M hvalid) ⟨.initEndWrite3, T5⟩ = some ⟨.initEndMoveF, T6⟩ :=
    step_write _ _ _ _ _ rfl
  have ha5 : TM0.step (simDelta M hvalid) ⟨.initEndMoveF, T6⟩ = some ⟨.initEndWriteF, T7⟩ :=
    step_move _ _ _ _ _ rfl
  have ha6 : TM0.step (simDelta M hvalid) ⟨.initEndWriteF, T7⟩ = some ⟨.initRewind, T8⟩ :=
    step_write _ _ _ _ _ rfl
  have hT8_nth : ∀ z : ℤ, T8.nth z =
      if z = 0 then .frontier
      else if z = -1 then .cell ⟨3, by omega⟩
      else if z = -2 then .cell ⟨0, by omega⟩
      else T2.nth (z + 3) := by
    intro z
    simp only [T8, T7, T6, T5, T4, T3, nth_write, nth_move_right]
    by_cases h0 : z = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : z = -1
      · subst h1; simp
      · rw [if_neg (by omega), if_neg h1]
        by_cases h2 : z = -2
        · subst h2; simp
        · rw [if_neg (by omega), if_neg h2]; congr 1; omega
  have hTM8 : TapeMatch N T8 (x.length + 3) (CookLevin.stringTape x) := by
    obtain ⟨_, h1, h2, h3, h5⟩ := hDone
    have hstrLen : (CookLevin.stringTape x).length = x.length + 3 := by
      simp [CookLevin.stringTape, CookLevin.symbolsOf]
    refine ⟨fun k hk => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · rw [hT8_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [show k - (x.length + 3 : ℕ) + 3 = k - (0 + x.length : ℕ) by omega]
      exact h1 k hk
    · rw [hT8_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [show (-1 : ℤ) - (x.length + 3 : ℕ) + 3 = -1 - (0 + x.length : ℕ) by omega]
      exact h2
    · rw [hstrLen] at hi
      by_cases hi1 : i < x.length + 1
      · have hpre : (CookLevin.stringTape x)[i] = ([] ++ 3 :: CookLevin.symbolsOf x)[i]'(by simp [CookLevin.symbolsOf]; omega) := by
          unfold CookLevin.stringTape
          have h1' : 3 :: (CookLevin.symbolsOf x ++ [0, 3]) = (3 :: CookLevin.symbolsOf x) ++ [0, 3] := rfl
          simp only [List.nil_append, h1']
          exact List.getElem_append_left (by simp [CookLevin.symbolsOf]; omega)
        obtain ⟨hv, heq⟩ := h3 i (by simp [CookLevin.symbolsOf]; omega)
        simp only [List.length_nil] at heq
        refine ⟨by rw [hpre]; exact hv, ?_⟩
        rw [hT8_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [show (i : ℤ) - (x.length + 3 : ℕ) + 3 = (i : ℤ) - (0 + x.length : ℕ) by omega, heq]
        congr 1; exact Fin.ext hpre.symm
      · by_cases hi2 : i = x.length + 1
        · subst hi2
          have hget : (CookLevin.stringTape x)[x.length + 1] = 0 := by
            unfold CookLevin.stringTape
            have h1' : 3 :: (CookLevin.symbolsOf x ++ [0, 3]) = (3 :: CookLevin.symbolsOf x) ++ [0, 3] := rfl
            simp only [h1']
            rw [List.getElem_append_right (by simp [CookLevin.symbolsOf])]
            simp [CookLevin.symbolsOf]
          refine ⟨by rw [hget]; omega, ?_⟩
          rw [hT8_nth, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          congr 1; exact Fin.ext hget.symm
        · have hi3 : i = x.length + 2 := by omega
          subst hi3
          have hget : (CookLevin.stringTape x)[x.length + 2] = 3 := by
            unfold CookLevin.stringTape
            have h1' : 3 :: (CookLevin.symbolsOf x ++ [0, 3]) = (3 :: CookLevin.symbolsOf x) ++ [0, 3] := rfl
            simp only [h1']
            rw [List.getElem_append_right (by simp [CookLevin.symbolsOf])]
            simp [CookLevin.symbolsOf]
          refine ⟨by rw [hget]; omega, ?_⟩
          rw [hT8_nth, if_neg (by omega), if_pos (by omega)]
          congr 1; exact Fin.ext hget.symm
    · rw [hstrLen, hT8_nth, if_pos (by omega)]
    · rw [hstrLen] at hi
      rw [hT8_nth, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have := h5 (i - x.length) (by omega)
      simpa [show ((i - x.length : ℕ) : ℤ) = (i : ℤ) - (x.length + 3 : ℕ) + 3 by omega] using this
  obtain ⟨T', hrRew, hTM'⟩ := init_rewind_loop M hvalid (CookLevin.stringTape x) (x.length + 3) T8 hTM8
  refine ⟨T', ?_, hTM'⟩
  have hrPre : Reaches (simDelta M hvalid) ⟨.initLeft, T0⟩ ⟨.initShiftWrite ⟨3, by omega⟩, T1⟩ 3 :=
    reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) (reaches_step _ hs3)
  have hrEnd : Reaches (simDelta M hvalid) ⟨.initEndMove0, T2⟩ ⟨.initRewind, T8⟩ 6 :=
    reaches_trans _ (reaches_trans _ (reaches_trans _ (reaches_step _ ha1) (reaches_step _ ha2))
      (reaches_trans _ (reaches_step _ ha3) (reaches_step _ ha4)))
      (reaches_trans _ (reaches_step _ ha5) (reaches_step _ ha6))
  have hrAll := reaches_trans _ (reaches_trans _ (reaches_trans _ hrPre hrShift) hrEnd) hrRew
  have hcnt : 3 + (2 * x.length + 1) + 6 + (x.length + 3 + 2) = 3 * x.length + 15 := by omega
  rw [hcnt] at hrAll
  exact hrAll

/-! ## Phase 2: Simulating `runFlatTM` -/

private lemma doMove_sim (M : FlatTM) (hvalid : validFlatTM M)
    (q' : Fin M.states) (d : TMMove) (head : ℕ) (right : List ℕ)
    (T : Tape (SimSym (max M.sig 4)))
    (hT : TapeMatch (max M.sig 4) T head right) :
    ∃ (T' : Tape (SimSym (max M.sig 4))) (k : ℕ), k ≤ 2 ∧
      Reaches (simDelta M hvalid) ⟨.doMove q' d, T⟩ ⟨.sim q', T'⟩ k ∧
      TapeMatch (max M.sig 4) T' (moveTapeHead ([], head, right) d).2.1 right := by
  cases d with
  | Nmove =>
    have hs : TM0.step (simDelta M hvalid) ⟨.doMove q' .Nmove, T⟩ =
        some ⟨.sim q', T.write T.head⟩ := step_write _ _ _ _ _ rfl
    have hwr : T.write T.head = T := by cases T; rfl
    rw [hwr] at hs
    exact ⟨T, 1, by omega, reaches_step _ hs, hT⟩
  | Rmove =>
    have hs : TM0.step (simDelta M hvalid) ⟨.doMove q' .Rmove, T⟩ =
        some ⟨.sim q', T.move .right⟩ := step_move _ _ _ _ _ rfl
    exact ⟨T.move .right, 1, by omega, reaches_step _ hs, tapeMatch_move_right hT⟩
  | Lmove =>
    have hs1 : TM0.step (simDelta M hvalid) ⟨.doMove q' .Lmove, T⟩ =
        some ⟨.checkLeftWall q', T.move .left⟩ := step_move _ _ _ _ _ rfl
    cases head with
    | zero =>
      have hwall : (T.move .left).head = SimSym.leftWall := by
        rw [← nth_zero, nth_move_left]; simpa using hT.2.1
      have hs2 : TM0.step (simDelta M hvalid) ⟨.checkLeftWall q', T.move .left⟩ =
          some ⟨.sim q', (T.move .left).move .right⟩ := by
        apply step_move; simp [simDelta, hwall]
      refine ⟨(T.move .left).move .right, 2, le_rfl,
        reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2), ?_⟩
      have hsame : ∀ z : ℤ, ((T.move .left).move .right).nth z = T.nth z := by
        intro z; rw [nth_move_right, nth_move_left]; congr 1; omega
      obtain ⟨h1, h2, h3, h4, h5⟩ := hT
      exact ⟨fun k hk => by rw [hsame]; exact h1 k hk, by rw [hsame]; exact h2,
        fun i hi => by obtain ⟨hv, heq⟩ := h3 i hi; exact ⟨hv, by rw [hsame]; exact heq⟩,
        by rw [hsame]; exact h4, fun i hi => by rw [hsame]; exact h5 i hi⟩
    | succ h0 =>
      have hT' := tapeMatch_move_left hT
      have hnotW : (T.move .left).head ≠ SimSym.leftWall := by
        rcases lt_trichotomy h0 right.length with hlt | heq | hgt
        · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT' hlt; rw [hhd]; intro h; cases h
        · rw [tapeMatch_head_eq hT' heq]; intro h; cases h
        · rw [tapeMatch_head_gt hT' hgt]; intro h; cases h
      have hs2 : TM0.step (simDelta M hvalid) ⟨.checkLeftWall q', T.move .left⟩ =
          some ⟨.sim q', (T.move .left).write (T.move .left).head⟩ := by
        apply step_write
        unfold simDelta
        cases hhd : (T.move .left).head with
        | leftWall => exact absurd hhd hnotW
        | _ => rfl
      have hwr : (T.move .left).write (T.move .left).head = T.move .left := by
        cases T.move .left; rfl
      rw [hwr] at hs2
      exact ⟨T.move .left, 2, le_rfl,
        reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2), hT'⟩

private lemma sim_runFlatTM (M : FlatTM) (hvalid : validFlatTM M) (htapes : M.tapes = 1) :
    ∀ (n : ℕ) (q : Fin M.states) (head : ℕ) (right : List ℕ)
      (T : Tape (SimSym (max M.sig 4))) (cfg : FlatTMConfig),
      TapeMatch (max M.sig 4) T head right →
      runFlatTM n M ⟨q.val, [([], head, right)]⟩ = some cfg →
      haltingStateReached M cfg = true →
      ∃ (head' : ℕ) (right' : List ℕ) (T' : Tape (SimSym (max M.sig 4))) (k : ℕ),
        cfg.tapes = [([], head', right')] ∧
        head' ≤ head + n ∧
        right'.length ≤ right.length + n ∧
        k ≤ 6 * n + 1 ∧
        Reaches (simDelta M hvalid) ⟨.sim q, T⟩ ⟨.outRewind, T'⟩ k ∧
        TapeMatch (max M.sig 4) T' head' right' := by
  intro n
  induction n with
  | zero =>
    intro q head right T cfg hT hrun hhalt
    simp only [runFlatTM, Option.some.injEq] at hrun
    subst hrun
    have hqhalt : M.halt.getD q.val false = true := hhalt
    have hs : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
        some ⟨.outRewind, T.write T.head⟩ := by
      apply step_write
      dsimp [simDelta]; rw [if_pos hqhalt]
    have hwr : T.write T.head = T := by cases T; rfl
    rw [hwr] at hs
    exact ⟨head, right, T, 1, rfl, le_rfl, le_rfl, le_rfl, reaches_step _ hs, hT⟩
  | succ m ih =>
    intro q head right T cfg hT hrun hhalt
    by_cases hqhalt : M.halt.getD q.val false = true
    · have hrun' : some ⟨q.val, [([], head, right)]⟩ = some cfg := by
        rw [runFlatTM] at hrun
        have hh : haltingStateReached M ⟨q.val, [([], head, right)]⟩ = true := hqhalt
        rw [hh] at hrun
        simpa using hrun
      injection hrun' with hcfg
      subst hcfg
      have hs : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
          some ⟨.outRewind, T.write T.head⟩ := by
        apply step_write; dsimp [simDelta]; rw [if_pos hqhalt]
      have hwr : T.write T.head = T := by cases T; rfl
      rw [hwr] at hs
      exact ⟨head, right, T, 1, rfl, by omega, by omega, by omega, reaches_step _ hs, hT⟩
    · have hqhaltF : M.halt.getD q.val false = false := by
        cases h : M.halt.getD q.val false <;> simp_all
      have hcur_eq : (match T.head with | SimSym.cell v => some v.val | _ => none) =
          currentTapeSymbol ([], head, right) := by
        unfold currentTapeSymbol
        rcases lt_trichotomy head right.length with hlt | heq | hgt
        · obtain ⟨hv, hhd⟩ := tapeMatch_head_lt hT hlt
          rw [hhd, dif_pos hlt]; rfl
        · rw [tapeMatch_head_eq hT heq, dif_neg (show ¬ head < right.length by omega)]
        · rw [tapeMatch_head_gt hT hgt, dif_neg (show ¬ head < right.length by omega)]
      have hpred : (fun e : FlatTMTransEntry =>
          entryMatchesConfig e ⟨q.val, [([], head, right)]⟩) =
          (fun e : FlatTMTransEntry =>
            e.src_state == q.val && decide (e.src_tape_vals =
              [match T.head with | SimSym.cell v => some v.val | _ => none])) := by
        funext e
        simp [entryMatchesConfig, hcur_eq]
      rw [runFlatTM, show haltingStateReached M ⟨q.val, [([], head, right)]⟩ = false from hqhaltF] at hrun
      simp only [Bool.false_eq_true, ↓reduceIte, stepFlatTM, Option.bind_eq_bind, hpred] at hrun
      cases hfind : M.trans.find? (fun e => e.src_state == q.val &&
          decide (e.src_tape_vals = [match T.head with | SimSym.cell v => some v.val | _ => none])) with
      | none =>
        rw [hfind] at hrun
        simp only [Option.bind_none, Option.some.injEq] at hrun
        subst hrun
        simp only [haltingStateReached, hqhaltF, Bool.false_eq_true] at hhalt
      | some e =>
        have he_mem : e ∈ M.trans := List.mem_of_find?_eq_some hfind
        have he_val := hvalid.2.2 e he_mem
        have hdst_lt : e.dst_state < M.states := he_val.2.1
        have hlen_w : e.dst_write_vals.length = 1 := by rw [he_val.2.2.2.1, htapes]
        have hlen_d : e.move_dirs.length = 1 := by rw [he_val.2.2.2.2.1, htapes]
        rcases List.length_eq_one_iff.mp hlen_w with ⟨w, hw⟩
        rcases List.length_eq_one_iff.mp hlen_d with ⟨d, hd⟩
        have happ : applyTransitionEntry ⟨q.val, [([], head, right)]⟩ e =
            some ⟨e.dst_state, [tapeStep ([], head, right) w d]⟩ := by
          simp [applyTransitionEntry, hw, hd]
        rw [hfind, Option.bind_some, happ] at hrun
        let q' : Fin M.states := ⟨e.dst_state, hdst_lt⟩
        have hq'_eq : (if h : e.dst_state < M.states then ⟨e.dst_state, h⟩ else q) = q' :=
          dif_pos hdst_lt
        -- Step write phase: from `.sim q` to `.doMove q' d`
        have hwrite_phase : ∃ (T1 : Tape (SimSym (max M.sig 4))) (k1 : ℕ),
            k1 ≤ 4 ∧
            Reaches (simDelta M hvalid) ⟨.sim q, T⟩ ⟨.doMove q' d, T1⟩ k1 ∧
            TapeMatch (max M.sig 4) T1 head (writeCurrentTapeSymbol ([], head, right) w).2.2 ∧
            (writeCurrentTapeSymbol ([], head, right) w).2.2.length ≤ right.length + 1 := by
          cases w with
          | none =>
            have hs : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
                some ⟨.doMove q' d, T.write T.head⟩ := by
              apply step_write
              unfold simDelta
              simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hfind, hw, hd,
                List.headD_cons, hq'_eq]
            have hwr : T.write T.head = T := by cases T; rfl
            rw [hwr] at hs
            exact ⟨T, 1, by omega, reaches_step _ hs, hT, by simp [writeCurrentTapeSymbol]⟩
          | some v =>
            have hv_lt_sig : v < M.sig := by
              have hbdd := he_val.2.2.2.2.2.2
              simp [flatTMOptionSymbolsBounded, hw] at hbdd
              exact hbdd
            have hv_lt : v < max M.sig 4 := lt_of_lt_of_le hv_lt_sig (le_max_left _ _)
            let vf : Fin (max M.sig 4) := ⟨v, hv_lt⟩
            have hvf_eq : (if h : v < max M.sig 4 then ⟨v, h⟩ else ⟨0, by omega⟩) = vf :=
              dif_pos hv_lt
            rcases lt_trichotomy head right.length with hlt | heq | hgt
            · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT hlt
              have hfind' := hfind
              rw [hhd] at hfind'
              have hs : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
                  some ⟨.doMove q' d, T.write (.cell vf)⟩ := by
                apply step_write
                unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              refine ⟨T.write (.cell vf), 1, by omega, reaches_step _ hs, ?_, ?_⟩
              · simpa [writeCurrentTapeSymbol, hlt, vf] using tapeMatch_write_in_range hT hlt vf
              · simp [writeCurrentTapeSymbol, hlt, List.length_take, List.length_drop]; omega
            · have hhd := tapeMatch_head_eq hT heq
              have hfind' := hfind
              rw [hhd] at hfind'
              have hs1 : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
                  some ⟨.frontMoveR q' d, T.write (.cell vf)⟩ := by
                apply step_write
                unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              have hs2 : TM0.step (simDelta M hvalid) ⟨.frontMoveR q' d, T.write (.cell vf)⟩ =
                  some ⟨.frontWriteF q' d, (T.write (.cell vf)).move .right⟩ :=
                step_move _ _ _ _ _ rfl
              have hs3 : TM0.step (simDelta M hvalid) ⟨.frontWriteF q' d, (T.write (.cell vf)).move .right⟩ =
                  some ⟨.frontMoveL q' d, ((T.write (.cell vf)).move .right).write .frontier⟩ :=
                step_write _ _ _ _ _ rfl
              have hs4 : TM0.step (simDelta M hvalid) ⟨.frontMoveL q' d, ((T.write (.cell vf)).move .right).write .frontier⟩ =
                  some ⟨.doMove q' d, (((T.write (.cell vf)).move .right).write .frontier).move .left⟩ :=
                step_move _ _ _ _ _ rfl
              have hr : Reaches (simDelta M hvalid) ⟨.sim q, T⟩
                  ⟨.doMove q' d, (((T.write (.cell vf)).move .right).write .frontier).move .left⟩ 4 :=
                reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2))
                  (reaches_trans _ (reaches_step _ hs3) (reaches_step _ hs4))
              subst heq
              refine ⟨_, 4, le_rfl, hr, ?_, ?_⟩
              · simpa [writeCurrentTapeSymbol, vf] using tapeMatch_write_frontier hT vf
              · simp [writeCurrentTapeSymbol]
            · have hhd := tapeMatch_head_gt hT hgt
              have hfind' := hfind
              rw [hhd] at hfind'
              have hs : TM0.step (simDelta M hvalid) ⟨.sim q, T⟩ =
                  some ⟨.doMove q' d, T.write T.head⟩ := by
                apply step_write
                unfold simDelta
                simp only [hqhaltF, Bool.false_eq_true, ↓reduceIte, hhd, hfind', hw, hd,
                  List.headD_cons, hq'_eq, hvf_eq]
              have hwr : T.write T.head = T := by cases T; rfl
              rw [hwr] at hs
              have hnotlt : ¬ (head < right.length) := by omega
              have hnoteq : ¬ (head = right.length) := by omega
              refine ⟨T, 1, by omega, reaches_step _ hs, ?_, ?_⟩
              · simpa [writeCurrentTapeSymbol, hnotlt, hnoteq] using hT
              · simp [writeCurrentTapeSymbol, hnotlt, hnoteq]
        obtain ⟨T1, k1, hk1, hr1, hT1, hlen1⟩ := hwrite_phase
        set right1 := (writeCurrentTapeSymbol ([], head, right) w).2.2 with hright1
        have hwr_eq : writeCurrentTapeSymbol ([], head, right) w = ([], head, right1) := by
          cases w <;> simp [writeCurrentTapeSymbol, hright1] <;> split_ifs <;> rfl
        have hstep_eq : tapeStep ([], head, right) w d =
            ([], (moveTapeHead ([], head, right1) d).2.1, right1) := by
          unfold tapeStep; rw [hwr_eq]; cases d <;> rfl
        obtain ⟨T2, k2, hk2, hr2, hT2⟩ := doMove_sim M hvalid q' d head right1 T1 hT1
        have hhead_le : (moveTapeHead ([], head, right1) d).2.1 ≤ head + 1 := by
          cases d <;> simp [moveTapeHead] <;> omega
        rw [hstep_eq] at hrun
        obtain ⟨head', right', T', k3, hcfg_t, hhd', hrlen', hk3, hr3, hT'⟩ :=
          ih q' (moveTapeHead ([], head, right1) d).2.1 right1 T2 cfg hT2 hrun hhalt
        refine ⟨head', right', T', k1 + k2 + k3, hcfg_t, by omega, by omega, by omega,
          reaches_trans _ (reaches_trans _ hr1 hr2) hr3, hT'⟩

/-! ## Phase 3: Output extraction (`outRewind` → `halt` showing `outputString cfg`) -/

private lemma out_rewind_loop (M : FlatTM) (hvalid : validFlatTM M)
    (right : List ℕ) :
    ∀ (head : ℕ) (T : Tape (SimSym (max M.sig 4))),
      TapeMatch (max M.sig 4) T head right →
      ∃ T', Reaches (simDelta M hvalid) ⟨.outRewind, T⟩ ⟨.outAt0, T'⟩ (head + 2) ∧
        TapeMatch (max M.sig 4) T' 0 right := by
  intro head
  induction head with
  | zero =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      cases right with
      | nil => rw [tapeMatch_head_eq hT rfl]; intro h; cases h
      | cons r rs =>
        obtain ⟨_, heq⟩ := tapeMatch_head_lt hT (by simp)
        rw [heq]; intro h; cases h
    have hs1 : TM0.step (simDelta M hvalid) ⟨.outRewind, T⟩ = some ⟨.outRewind, T.move .left⟩ := by
      apply step_move; unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    have hwall : (T.move .left).head = SimSym.leftWall := by
      rw [← nth_zero, nth_move_left]; simpa using hT.2.1
    have hs2 : TM0.step (simDelta M hvalid) ⟨.outRewind, T.move .left⟩ =
        some ⟨.outAt0, (T.move .left).move .right⟩ := by
      apply step_move; simp [simDelta, hwall]
    have h12 : Reaches (simDelta M hvalid) ⟨.outRewind, T⟩
        ⟨.outAt0, (T.move .left).move .right⟩ (0 + 2) := by
      show Reaches (simDelta M hvalid) ⟨.outRewind, T⟩
        ⟨.outAt0, (T.move .left).move .right⟩ (1 + 1)
      exact reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)
    refine ⟨(T.move .left).move .right, h12, ?_⟩
    have hsame : ∀ z : ℤ, ((T.move .left).move .right).nth z = T.nth z := by
      intro z; rw [nth_move_right, nth_move_left]; congr 1; omega
    obtain ⟨h1, h2, h3, h4, h5⟩ := hT
    exact ⟨fun k hk => by rw [hsame]; exact h1 k hk, by rw [hsame]; exact h2,
      fun i hi => by obtain ⟨hv, heq⟩ := h3 i hi; exact ⟨hv, by rw [hsame]; exact heq⟩,
      by rw [hsame]; exact h4, fun i hi => by rw [hsame]; exact h5 i hi⟩
  | succ k ih =>
    intro T hT
    have hnotW : T.head ≠ SimSym.leftWall := by
      rcases lt_trichotomy (k + 1) right.length with hlt | heq | hgt
      · obtain ⟨_, hhd⟩ := tapeMatch_head_lt hT hlt; rw [hhd]; intro h; cases h
      · rw [tapeMatch_head_eq hT heq]; intro h; cases h
      · rw [tapeMatch_head_gt hT hgt]; intro h; cases h
    have hs1 : TM0.step (simDelta M hvalid) ⟨.outRewind, T⟩ = some ⟨.outRewind, T.move .left⟩ := by
      apply step_move; unfold simDelta
      cases hhd : T.head with
      | leftWall => exact absurd hhd hnotW
      | _ => rfl
    obtain ⟨T', hreach, hT'⟩ := ih (T.move .left) (tapeMatch_move_left hT)
    refine ⟨T', ?_, hT'⟩
    have htot := reaches_trans _ (reaches_step _ hs1) hreach
    have hcnt : 1 + (k + 2) = k + 1 + 2 := by omega
    rwa [hcnt] at htot

private def OutScanInv (N : ℕ) (T : Tape (SimSym N)) (pos : ℕ) (outAcc : List Bool) (rem : List ℕ) : Prop :=
  outAcc.length = pos ∧
  (∀ b : Bool, T.nth (-1 - pos) ≠ SimSym.outBit b) ∧
  (∀ (i : ℕ) (hi : i < outAcc.length), T.nth ((i : ℤ) - pos) = SimSym.outBit outAcc[i]) ∧
  (∀ (j : ℕ) (hj : j < rem.length), ∃ hv : rem[j] < N, T.nth (j : ℤ) = SimSym.cell ⟨rem[j], hv⟩) ∧
  T.nth (rem.length : ℤ) = SimSym.frontier

private lemma out_back_loop (M : FlatTM) (hvalid : validFlatTM M) (outList : List Bool) :
    ∀ (k : ℕ) (hk : k ≤ outList.length) (T : Tape (SimSym (max M.sig 4))),
      (∀ b : Bool, T.nth (-(k : ℤ)) ≠ SimSym.outBit b) →
      (∀ (i : ℕ) (hi : i < outList.length),
        T.nth ((i : ℤ) + 1 - k) = SimSym.outBit outList[i]) →
      (∀ b : Bool, T.nth ((outList.length : ℤ) + 1 - k) ≠ SimSym.outBit b) →
      ∃ T', Reaches (simDelta M hvalid) ⟨.outBack, T⟩ ⟨.halt, T'⟩ (k + 1) ∧
        (simMachine M hvalid).Shows ⟨SimState.halt, T'⟩ outList := by
  intro k
  induction k with
  | zero =>
    intro _ T hstop hout hend
    have hhd : ∀ b : Bool, T.head ≠ SimSym.outBit b := by
      intro b; rw [← nth_zero]; simpa using hstop b
    have hs : TM0.step (simDelta M hvalid) ⟨.outBack, T⟩ =
        some ⟨.halt, T.move .right⟩ := by
      apply step_move
      unfold simDelta
      cases h : T.head with
      | outBit b => exact absurd h (hhd b)
      | _ => rfl
    refine ⟨T.move .right, reaches_step _ hs, ?_⟩
    refine ⟨fun i hi => ?_, fun b => ?_⟩
    · show (T.move .right).right₀.nth i = SimSym.outBit outList[i]
      rw [right₀_nth_eq_nth, nth_move_right]
      simpa using hout i hi
    · show (T.move .right).right₀.nth outList.length ≠ SimSym.outBit b
      rw [right₀_nth_eq_nth, nth_move_right]
      simpa using hend b
  | succ m ih =>
    intro hk T hstop hout hend
    have hhd : T.head = SimSym.outBit (outList[m]'(by omega)) := by
      rw [← nth_zero]
      have := hout m (by omega)
      simpa [show ((m : ℤ) + 1 - (m + 1 : ℕ)) = 0 by omega] using this
    have hs : TM0.step (simDelta M hvalid) ⟨.outBack, T⟩ =
        some ⟨.outBack, T.move .left⟩ := by
      apply step_move
      simp [simDelta, hhd]
    obtain ⟨T', hr, hshows⟩ := ih (by omega) (T.move .left)
      (fun b => by rw [nth_move_left, show -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) by omega]; exact hstop b)
      (fun i hi => by
        rw [nth_move_left, show (i : ℤ) + 1 - m - 1 = (i : ℤ) + 1 - (m + 1 : ℕ) by omega]
        exact hout i hi)
      (fun b => by
        rw [nth_move_left, show (outList.length : ℤ) + 1 - m - 1 = (outList.length : ℤ) + 1 - (m + 1 : ℕ) by omega]
        exact hend b)
    refine ⟨T', ?_, hshows⟩
    have htot := reaches_trans _ (reaches_step _ hs) hr
    simpa [Nat.add_assoc, Nat.add_comm] using htot

private def takeOut (l : List ℕ) : List Bool :=
  ((l.takeWhile (· != 3)).takeWhile (· != 0)).map (· == 2)

private lemma takeOut_nil : takeOut [] = [] := rfl

private lemma takeOut_cons_stop0 (rs : List ℕ) : takeOut (0 :: rs) = [] := by
  simp [takeOut, List.takeWhile]

private lemma takeOut_cons_stop3 (rs : List ℕ) : takeOut (3 :: rs) = [] := by
  simp [takeOut, List.takeWhile]

private lemma takeOut_cons_keep (r : ℕ) (rs : List ℕ) (h0 : r ≠ 0) (h3 : r ≠ 3) :
    takeOut (r :: rs) = (r == 2) :: takeOut rs := by
  have hb3 : (r != 3) = true := by simp [h3]
  have hb0 : (r != 0) = true := by simp [h0]
  simp [takeOut, List.takeWhile, hb3, hb0]

private lemma out_scan_loop (M : FlatTM) (hvalid : validFlatTM M) :
    ∀ (rem : List ℕ) (outAcc : List Bool) (T : Tape (SimSym (max M.sig 4))),
      OutScanInv (max M.sig 4) T outAcc.length outAcc rem →
      ∃ (T' : Tape (SimSym (max M.sig 4))) (k : ℕ),
        k ≤ outAcc.length + 3 * rem.length + 2 ∧
        Reaches (simDelta M hvalid) ⟨.outScan, T⟩ ⟨.halt, T'⟩ k ∧
        (simMachine M hvalid).Shows ⟨SimState.halt, T'⟩ (outAcc ++ takeOut rem) := by
  intro rem
  induction rem with
  | nil =>
    intro outAcc T hInv
    obtain ⟨_, hstop, hout, _, hfront⟩ := hInv
    have hhd : T.head = SimSym.frontier := by rw [← nth_zero]; simpa using hfront
    have hs : TM0.step (simDelta M hvalid) ⟨.outScan, T⟩ =
        some ⟨.outBack, T.move .left⟩ := by
      apply step_move; simp [simDelta, hhd]
    obtain ⟨T', hr, hshows⟩ := out_back_loop M hvalid outAcc outAcc.length le_rfl (T.move .left)
      (fun b => by
        rw [nth_move_left, show -(outAcc.length : ℤ) - 1 = -1 - outAcc.length by omega]
        exact hstop b)
      (fun i hi => by
        rw [nth_move_left, show (i : ℤ) + 1 - outAcc.length - 1 = (i : ℤ) - outAcc.length by omega]
        exact hout i hi)
      (fun b => by
        rw [nth_move_left, show (outAcc.length : ℤ) + 1 - outAcc.length - 1 = 0 by omega, nth_zero, hhd]
        intro h; cases h)
    refine ⟨T', 1 + (outAcc.length + 1), by omega,
      reaches_trans _ (reaches_step _ hs) hr, by simpa [takeOut_nil] using hshows⟩
  | cons r rs ih =>
    intro outAcc T hInv
    obtain ⟨_, hstop, hout, hrem, hfront⟩ := hInv
    obtain ⟨hrlt, hhd⟩ := hrem 0 (by simp)
    have hhd0 : T.head = SimSym.cell ⟨r, hrlt⟩ := by rw [← nth_zero]; simpa using hhd
    by_cases hkeep : r ≠ 0 ∧ r ≠ 3
    · have hs1 : TM0.step (simDelta M hvalid) ⟨.outScan, T⟩ =
          some ⟨.outScanMove, T.write (.outBit (r == 2))⟩ := by
        apply step_write
        simp [simDelta, hhd0, hkeep.1, hkeep.2]
      have hs2 : TM0.step (simDelta M hvalid) ⟨.outScanMove, T.write (.outBit (r == 2))⟩ =
          some ⟨.outScan, (T.write (.outBit (r == 2))).move .right⟩ :=
        step_move _ _ _ _ _ rfl
      have hInv' : OutScanInv (max M.sig 4) ((T.write (.outBit (r == 2))).move .right)
          (outAcc ++ [r == 2]).length (outAcc ++ [r == 2]) rs := by
        have hlen : (outAcc ++ [r == 2]).length = outAcc.length + 1 := by simp
        refine ⟨rfl, fun b => ?_, fun i hi => ?_, fun j hj => ?_, ?_⟩
        · rw [hlen, nth_move_right, nth_write, if_neg (by omega),
            show (-1 : ℤ) - (outAcc.length + 1 : ℕ) + 1 = -1 - outAcc.length by omega]
          exact hstop b
        · rw [hlen] at hi ⊢
          rw [nth_move_right, show (i : ℤ) - (outAcc.length + 1 : ℕ) + 1 = (i : ℤ) - outAcc.length by omega]
          by_cases hilt : i < outAcc.length
          · rw [nth_write, if_neg (by omega), List.getElem_append_left hilt]
            exact hout i hilt
          · have hieq : i = outAcc.length := by omega
            subst hieq
            rw [nth_write, if_pos (by omega)]
            simp
        · obtain ⟨hv, heq⟩ := hrem (j + 1) (by simp; omega)
          refine ⟨hv, ?_⟩
          rw [nth_move_right, nth_write, if_neg (by omega)]
          simpa using heq
        · rw [nth_move_right, nth_write, if_neg (by omega)]
          simpa [Nat.add_comm] using hfront
      obtain ⟨T', k, hk, hr, hshows⟩ := ih (outAcc ++ [r == 2]) _ hInv'
      refine ⟨T', 1 + 1 + k, ?_,
        reaches_trans _ (reaches_trans _ (reaches_step _ hs1) (reaches_step _ hs2)) hr, ?_⟩
      · simp only [List.length_append, List.length_singleton] at hk
        simp only [List.length_cons]; omega
      rw [takeOut_cons_keep r rs hkeep.1 hkeep.2]
      simpa [List.append_assoc] using hshows
    · have hstop_r : takeOut (r :: rs) = [] := by
        by_cases h0 : r = 0
        · subst h0; exact takeOut_cons_stop0 rs
        · have h3 : r = 3 := by omega
          subst h3; exact takeOut_cons_stop3 rs
      have hs : TM0.step (simDelta M hvalid) ⟨.outScan, T⟩ =
          some ⟨.outBack, T.move .left⟩ := by
        apply step_move
        simp [simDelta, hhd0, hkeep]
      obtain ⟨T', hr, hshows⟩ := out_back_loop M hvalid outAcc outAcc.length le_rfl (T.move .left)
        (fun b => by
          rw [nth_move_left, show -(outAcc.length : ℤ) - 1 = -1 - outAcc.length by omega]
          exact hstop b)
        (fun i hi => by
          rw [nth_move_left, show (i : ℤ) + 1 - outAcc.length - 1 = (i : ℤ) - outAcc.length by omega]
          exact hout i hi)
        (fun b => by
          rw [nth_move_left, show (outAcc.length : ℤ) + 1 - outAcc.length - 1 = 0 by omega, nth_zero, hhd0]
          intro h; cases h)
      refine ⟨T', 1 + (outAcc.length + 1), by simp; omega,
        reaches_trans _ (reaches_step _ hs) hr, by simpa [hstop_r] using hshows⟩

private lemma phase3_output (M : FlatTM) (hvalid : validFlatTM M)
    (head : ℕ) (right : List ℕ) (T : Tape (SimSym (max M.sig 4)))
    (hT : TapeMatch (max M.sig 4) T head right) :
    ∃ (T' : Tape (SimSym (max M.sig 4))) (k : ℕ),
      k ≤ head + 3 * right.length + 6 ∧
      Reaches (simDelta M hvalid) ⟨.outRewind, T⟩ ⟨.halt, T'⟩ k ∧
      (simMachine M hvalid).Shows ⟨SimState.halt, T'⟩ (takeOut right.tail) := by
  obtain ⟨T0, hrRew, hT0⟩ := out_rewind_loop M hvalid right head T hT
  cases right with
  | nil =>
    have hhd : T0.head = SimSym.frontier := tapeMatch_head_eq hT0 rfl
    have hs : TM0.step (simDelta M hvalid) ⟨.outAt0, T0⟩ = some ⟨.halt, T0.write T0.head⟩ := by
      apply step_write; simp [simDelta, hhd]
    have hwr : T0.write T0.head = T0 := by cases T0; rfl
    rw [hwr] at hs
    refine ⟨T0, (head + 2) + 1, by omega, reaches_trans _ hrRew (reaches_step _ hs), ?_⟩
    refine ⟨fun i hi => by simp [takeOut_nil] at hi, fun b => ?_⟩
    show T0.right₀.nth 0 ≠ SimSym.outBit b
    rw [right₀_nth_eq_nth]
    show T0.nth 0 ≠ SimSym.outBit b
    rw [nth_zero, hhd]; intro h; cases h
  | cons r0 rest =>
    obtain ⟨hr0lt, hhd0⟩ := tapeMatch_head_lt hT0 (by simp)
    have hs : TM0.step (simDelta M hvalid) ⟨.outAt0, T0⟩ =
        some ⟨.outScan, T0.move .right⟩ := by
      apply step_move; simp [simDelta, hhd0]
    have hInv0 : OutScanInv (max M.sig 4) (T0.move .right) 0 [] rest := by
      obtain ⟨_, _, h3, h4, _⟩ := hT0
      refine ⟨rfl, fun b => ?_, fun i hi => by simp at hi, fun j hj => ?_, ?_⟩
      · rw [nth_move_right, show (-1 : ℤ) - (0 : ℕ) + 1 = 0 by omega, nth_zero, hhd0]; intro h; cases h
      · obtain ⟨hv, heq⟩ := h3 (j + 1) (by simp; omega)
        refine ⟨hv, ?_⟩
        rw [nth_move_right]
        simpa using heq
      · rw [nth_move_right]
        have hlen : ((r0 :: rest).length : ℤ) - (0 : ℕ) = (rest.length : ℤ) + 1 := by simp
        rwa [hlen] at h4
    obtain ⟨T', k, hk, hrScan, hshows⟩ := out_scan_loop M hvalid rest [] (T0.move .right) hInv0
    refine ⟨T', (head + 2) + 1 + k, by simp at hk ⊢; omega,
      reaches_trans _ (reaches_trans _ hrRew (reaches_step _ hs)) hrScan,
      by simpa using hshows⟩

/-! ## Polynomial upper bound for `inOPoly t` -/

private lemma inOPoly_le_poly {t : ℕ → ℕ} (ht : inOPoly t) :
    ∃ (C k : ℕ), ∀ n : ℕ, t n ≤ C * n ^ k + C := by
  rcases ht with ⟨k, c, n0, hcn⟩
  let B := maxPrefix t n0
  refine ⟨c + B, k, fun n => ?_⟩
  by_cases hn : n0 ≤ n
  · have h1 := hcn n hn
    have h2 : c * n ^ k ≤ (c + B) * n ^ k := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 (le_trans h2 (Nat.le_add_right _ _))
  · have h1 : t n ≤ B := le_maxPrefix t (by omega)
    omega

end PvsNP.Units.m1_flat_to_st

theorem PvsNP.Units.m1_flat_to_st :
    ∀ (f : List Bool → List Bool) (t : ℕ → ℕ) (M : FlatTM),
      inOPoly t → validFlatTM M → M.tapes = 1 → CookLevin.computesInTime M f t →
        PvsNP.SingleTape.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f := by
  intro f t M ht hvalid htapes hcomp
  obtain ⟨C, k, hCk⟩ := PvsNP.Units.m1_flat_to_st.inOPoly_le_poly ht
  let p : Polynomial ℕ :=
    Polynomial.C (10 * C + 40) + Polynomial.C 6 * Polynomial.X +
      Polynomial.C (10 * C) * Polynomial.X ^ k
  refine ⟨PvsNP.Units.m1_flat_to_st.simMachine M hvalid, p, fun x => ?_⟩
  obtain ⟨cfg, hrun, hhalt, hout⟩ := hcomp x
  obtain ⟨T1, hr1, hTM1⟩ := PvsNP.Units.m1_flat_to_st.phase1_init M hvalid x
  obtain ⟨head', right', T2, k2, hcfg_t, hhd', hrlen', hk2, hr2, hTM2⟩ :=
    PvsNP.Units.m1_flat_to_st.sim_runFlatTM M hvalid htapes (t x.length)
      ⟨M.start, hvalid.1⟩ 0 (CookLevin.stringTape x) T1 cfg hTM1 hrun hhalt
  obtain ⟨T3, k3, hk3, hr3, hshows⟩ :=
    PvsNP.Units.m1_flat_to_st.phase3_output M hvalid head' right' T2 hTM2
  have hout_eq : PvsNP.Units.m1_flat_to_st.takeOut right'.tail = f x := by
    rw [← hout]
    unfold CookLevin.outputString
    rw [hcfg_t]
    rfl
  rw [hout_eq] at hshows
  have hrTot := PvsNP.Units.m1_flat_to_st.reaches_trans _
    (PvsNP.Units.m1_flat_to_st.reaches_trans _ hr1 hr2) hr3
  have hstrLen : (CookLevin.stringTape x).length = x.length + 3 := by
    simp [CookLevin.stringTape, CookLevin.symbolsOf]
  have ht_le : t x.length ≤ C * x.length ^ k + C := hCk x.length
  have hpeval : p.eval x.length = 10 * C + 40 + 6 * x.length + 10 * C * x.length ^ k := by
    simp [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
  have h10 : 10 * t x.length ≤ 10 * C * x.length ^ k + 10 * C := by
    calc 10 * t x.length ≤ 10 * (C * x.length ^ k + C) := Nat.mul_le_mul_left 10 ht_le
      _ = 10 * C * x.length ^ k + 10 * C := by ring
  have hsteps_le : (3 * x.length + 15) + k2 + k3 ≤ p.eval (PvsNP.encodeString x).length := by
    change (3 * x.length + 15) + k2 + k3 ≤ p.eval x.length
    rw [hpeval]
    have h3r : 3 * right'.length ≤ 3 * (x.length + 3) + 3 * t x.length := by
      have : right'.length ≤ (x.length + 3) + t x.length := by omega
      omega
    omega
  refine ⟨⟨PvsNP.Units.m1_flat_to_st.SimState.halt, T3⟩,
    ⟨⟨⟨(3 * x.length + 15) + k2 + k3, hrTot⟩, hsteps_le⟩⟩, rfl, hshows⟩



