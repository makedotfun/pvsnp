import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_sat_to_3occ_sat_aux

/-- Each literal gets its own column. The original variable chooses the row. -/
def copies (width offset : Nat) (C : clause) : clause :=
  match C with
  | [] => []
  | (s, v) :: tail => (s, v * width + offset) :: copies width (offset + 1) tail

def copyClauses (width : Nat) : Nat → cnf → cnf
  | _, [] => []
  | offset, C :: N =>
    copies width offset C :: copyClauses width (offset + C.length) N

def implication (u v : var) : clause := [(false, u), (true, v)]

def row (width v : Nat) : cnf :=
  (List.range width).map fun i =>
    implication (v * width + i) (v * width + ((i + 1) % width))

def expand (w H : Nat) (N : cnf) : cnf :=
  copyClauses w 0 N ++ (List.range H).flatMap (row w)

theorem implication_true_iff (a : assgn) (u v : var) :
    evalClause a (implication u v) = true ↔ (u ∈ a → v ∈ a) := by
  by_cases hu : u ∈ a <;> by_cases hv : v ∈ a <;>
    simp [implication, evalClause, evalLiteral, evalVar, hu, hv]

/-- Truth at one copy propagates around the whole row; in particular it reaches any
chosen original occurrence, even when that occurrence precedes the first true one. -/
theorem cycle_constant (p : Nat → Prop) (w : Nat) (hw : 0 < w)
    (step : ∀ i < w, p i → p ((i + 1) % w)) (i j : Nat)
    (hi : i < w) (hj : j < w) : p i → p j := by
  intro start
  have walk (k : Nat) : p ((i + k) % w) := by
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt hi] using start
    | succ k ih =>
      have h := step ((i + k) % w) (Nat.mod_lt _ hw) ih
      change p (((i + k) + 1) % w)
      rwa [Nat.mod_add_mod] at h
  have reach := walk (w - i + j)
  have e : i + (w - i + j) = w + j := by omega
  simpa [e, Nat.add_mod, Nat.mod_eq_of_lt hj] using reach

theorem row_constant (a : assgn) (w v : Nat) (hw : 0 < w)
    (h : evalCnf a (row w v) = true) (i j : Nat) (hi : i < w) (hj : j < w) :
    v * w + i ∈ a ↔ v * w + j ∈ a := by
  have step (k : Nat) (hk : k < w) :
      v * w + k ∈ a → v * w + (k + 1) % w ∈ a := by
    apply (implication_true_iff ..).mp
    exact (evalCnf_clause_iff ..).mp h _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  exact ⟨cycle_constant _ w hw step i j hi hj, cycle_constant _ w hw step j i hj hi⟩

/-- Within the input's rectangle, every renamed literal reads the original truth value
if the two assignments agree on the row and column of each original occurrence. -/
theorem copies_eval (w H : Nat) (a b : assgn) (C : clause) (offset : Nat)
    (hcols : offset + C.length ≤ w) (hrows : ∀ l ∈ C, l.2 < H)
    (agree : ∀ v < H, ∀ i < w, (v * w + i ∈ b ↔ v ∈ a)) :
    evalClause b (copies w offset C) = evalClause a C := by
  induction C generalizing offset with
  | nil => rfl
  | cons l C ih =>
    obtain ⟨s, v⟩ := l
    have col : offset < w := by
      simp only [List.length_cons] at hcols
      omega
    have eqv := agree v (hrows (s, v) (by simp)) offset col
    have eqLit : evalLiteral b (s, v * w + offset) = evalLiteral a (s, v) := by
      simp [evalLiteral, evalVar, eqv] <;> rfl
    have tailBound : offset + 1 + C.length ≤ w := by
      simp only [List.length_cons] at hcols
      omega
    change (evalLiteral b _ || evalClause b (copies w (offset + 1) C)) =
      (evalLiteral a _ || evalClause a C)
    rw [eqLit, ih (offset + 1) tailBound (fun l hl => hrows l (by simp [hl]))]

theorem copyClauses_eval (w H : Nat) (a b : assgn) (N : cnf) (offset : Nat)
    (hcols : offset + N.flatten.length ≤ w) (hrows : ∀ l ∈ N.flatten, l.2 < H)
    (agree : ∀ v < H, ∀ i < w, (v * w + i ∈ b ↔ v ∈ a)) :
    evalCnf b (copyClauses w offset N) = evalCnf a N := by
  induction N generalizing offset with
  | nil => rfl
  | cons C N ih =>
    simp only [List.flatten_cons, List.length_append] at hcols
    have first := copies_eval w H a b C offset (by omega)
      (fun l hl => hrows l (by simp [hl])) agree
    have tail' := ih (offset + C.length) (by omega) (fun l hl => hrows l (by simp [hl]))
    change (evalClause b _ && evalCnf b _) = (evalClause a _ && evalCnf a _)
    rw [first, tail']

theorem expand_sat (N : cnf) (w H : Nat) (hw : 0 < w)
    (bound : 0 + N.flatten.length ≤ w) (vars : ∀ l ∈ N.flatten, l.2 < H) :
    SAT (expand w H N) ↔ SAT N := by
  change SAT (copyClauses w 0 N ++ (List.range H).flatMap (row w)) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hc, hr⟩ := (evalCnf_app_iff ..).mp hb
    let a := (List.range H).filter fun v => decide (v * w ∈ b)
    have agree (v : Nat) (hv : v < H) (i : Nat) (hi : i < w) :
        v * w + i ∈ b ↔ v ∈ a := by
      have good : evalCnf b (row w v) = true := by
        apply (evalCnf_clause_iff ..).mpr
        intro C hC
        apply (evalCnf_clause_iff ..).mp hr
        exact List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, hC⟩
      simpa [a, hv] using row_constant b w v hw good i 0 hi hw
    refine ⟨a, ?_⟩
    change evalCnf a N = true
    rwa [← copyClauses_eval w H a b N 0 bound vars agree]
  · rintro ⟨a, ha⟩
    let b := (List.range (H * w)).filter fun n => decide (n / w ∈ a)
    have agree (v : Nat) (hv : v < H) (i : Nat) (hi : i < w) :
        v * w + i ∈ b ↔ v ∈ a := by
      have room : v * w + i < H * w := calc
        _ < v * w + w := Nat.add_lt_add_left hi _
        _ = (v + 1) * w := (Nat.succ_mul _ _).symm
        _ ≤ H * w := Nat.mul_le_mul_right _ hv
      have divRow : (v * w + i) / w = v := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hi, Nat.zero_add]
      simp [b, room, divRow]
    refine ⟨b, (evalCnf_app_iff ..).mpr ⟨?_, ?_⟩⟩
    · rw [copyClauses_eval w H a b N 0 bound vars agree]
      exact ha
    · apply (evalCnf_clause_iff ..).mpr
      intro C hC
      obtain ⟨v, hv, hrow⟩ := List.mem_flatMap.mp hC
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
      apply (implication_true_iff ..).mpr
      intro h
      exact (agree v (List.mem_range.mp hv) _ (Nat.mod_lt _ hw)).mpr
        ((agree v (List.mem_range.mp hv) i (List.mem_range.mp hi)).mp h)

def hits (k : Nat) (C : List literal) := C.countP (fun l => l.2 == k)

theorem cell_col (v w i : Nat) (hi : i < w) : (v * w + i) % w = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem cell_row (v w i : Nat) (hi : i < w) : (v * w + i) / w = v := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

def occupied (k offset n : Nat) : Nat := if offset ≤ k ∧ k < offset + n then 1 else 0

theorem occupied_add (k offset a b : Nat) :
    occupied k offset (a + b) = occupied k offset a + occupied k (offset + a) b := by
  simp only [occupied]
  split <;> split <;> split <;> omega

theorem hits_copies (k w : Nat) (C : clause) (o : Nat) (hw : o + C.length ≤ w) :
    hits k (copies w o C) ≤ occupied (k % w) o C.length := by
  induction C generalizing o with
  | nil => simp [copies, hits, occupied]
  | cons l C ih =>
    obtain ⟨s,v⟩ := l
    simp only [List.length_cons] at hw ⊢
    rw [Nat.add_comm C.length 1, occupied_add]
    have htail := ih (o + 1) (by omega)
    have cell := cell_col v w o (by omega)
    by_cases eq : v * w + o = k
    · rw [eq] at cell
      simpa [copies, hits, eq, cell, occupied, Nat.add_comm] using htail
    · simp only [copies, hits, List.countP_cons, beq_iff_eq, eq, ite_false, Nat.add_zero]
      exact Nat.le_trans htail (Nat.le_add_left ..)

theorem hits_copyClauses (k w : Nat) (N : cnf) (o : Nat) (hw : o + N.flatten.length ≤ w) :
    hits k (copyClauses w o N).flatten ≤ occupied (k % w) o N.flatten.length := by
  induction N generalizing o with
  | nil => simp [copyClauses, hits, occupied]
  | cons C N ih =>
    simp only [List.flatten_cons, List.length_append] at hw ⊢
    rw [occupied_add]
    change hits k (copies w o C ++ (copyClauses w (o + C.length) N).flatten) ≤ _
    rw [show ∀ a b, hits k (a ++ b) = hits k a + hits k b from fun a b => List.countP_append]
    exact Nat.add_le_add (hits_copies k w C o (by omega)) (ih (o + C.length) (by omega))

theorem prev_of_step (w i : Nat) (hi : i < w) :
    i = (if (i + 1) % w = 0 then w - 1 else (i + 1) % w - 1) := by
  by_cases last : i + 1 = w
  · rw [last, Nat.mod_self]
    simp only [ite_true]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i + 1 < w)]
    simp

theorem edges_count (k : Nat) (src dst : Nat → Nat) (is : List Nat) :
    hits k (is.map (fun i => implication (src i) (dst i))).flatten =
      is.countP (fun i => src i == k) + is.countP (fun i => dst i == k) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.flatten_cons, hits, List.countP_append] at ih ⊢
    rw [ih]
    simp only [implication, List.countP_cons, List.countP_nil, Nat.zero_add]
    omega

theorem unique_hits (k j w : Nat) (f : Nat → Nat)
    (h : ∀ i < w, f i = k → i = j) :
    (List.range w).countP (fun i => f i == k) ≤ 1 := by
  have bound : (List.range w).countP (fun i => f i == k) ≤ (List.range w).count j := by
    apply List.countP_mono_left
    intro i hi heq
    exact beq_iff_eq.mpr (h i (List.mem_range.mp hi) (beq_iff_eq.mp heq))
  exact Nat.le_trans bound (List.nodup_iff_count.mp List.nodup_range j)

theorem count_row (k w v : Nat) (hw : 0 < w) :
    hits k (row w v).flatten ≤ (if v = k / w then 2 else 0) := by
  unfold row
  rw [edges_count]
  split
  · apply Nat.add_le_add (b := 1) (d := 1)
    · apply unique_hits k (k % w)
      intro i hi eq
      exact eq ▸ (cell_col v w i hi).symm
    · apply unique_hits k (if k % w = 0 then w - 1 else k % w - 1)
      intro i hi eq
      have en := cell_col v w ((i + 1) % w) (Nat.mod_lt _ hw)
      rw [eq] at en
      rw [en]
      exact prev_of_step w i hi
  · rename_i hv
    have miss (i : Nat) (hi : i < w) : v * w + i ≠ k := by
      intro e
      exact hv (e ▸ (cell_row v w i hi).symm)
    have lhs : (List.range w).countP (fun i => v * w + i == k) = 0 := by
      apply List.countP_eq_zero.mpr
      intro i hi
      simpa using miss i (List.mem_range.mp hi)
    have rhs : (List.range w).countP (fun i => v * w + (i+1)%w == k) = 0 := by
      apply List.countP_eq_zero.mpr
      intro i _
      simpa using miss _ (Nat.mod_lt _ hw)
    simp only [lhs, rhs, Nat.add_zero, Nat.le_refl]

theorem count_rows (k w : Nat) (hw : 0 < w) (vs : List Nat) :
    hits k (vs.flatMap (row w)).flatten ≤ 2 * vs.count (k / w) := by
  induction vs with
  | nil => simp [hits]
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.flatten_append, hits, List.countP_append] at ih ⊢
    have h := count_row k w v hw
    unfold hits at h
    by_cases e : v = k / w
    · subst v
      simp only [ite_true, List.count_cons_self] at h ⊢
      omega
    · simp only [e, ite_false] at h
      rw [List.count_cons_of_ne e]
      omega

theorem expand_occ (N : cnf) (w H : Nat) (hw : 0 < w)
    (bound : 0 + N.flatten.length ≤ w) (k : var) :
    (expand w H N).flatten.countP (fun l => l.2 == k) ≤ 3 := by
  have h := hits_copyClauses k w N 0 bound
  have one : hits k (copyClauses w 0 N).flatten ≤ 1 := by
    apply Nat.le_trans h
    unfold occupied
    split <;> decide
  have two := count_rows k w hw (List.range H)
  have r := List.nodup_iff_count.mp (@List.nodup_range H) (k/w)
  unfold hits at one two
  unfold expand
  rw [List.flatten_append, List.countP_append]
  change _ + _ ≤ 3
  omega

open EvalCnfCmd (encodeCnf encodeClause encodeLit)
open CnfSerialize (clauseBody)

def gridWidth (N : cnf) := (encodeCnf N).length + 1

theorem width_fits (N : cnf) : 0 + N.flatten.length ≤ gridWidth N := by
  have h : N.flatten.length ≤ (encodeCnf N).length := by
    induction N with
    | nil => exact Nat.le_refl 0
    | cons C N ih =>
      simp only [List.flatten_cons, List.length_append, CnfSerialize.encodeCnf_cons]
      exact Nat.add_le_add (Nat.le_of_lt (CnfSerialize.length_lt_encodeClause C)) ih
  unfold gridWidth
  omega

theorem height_fits (N : cnf) (l : literal) (hl : l ∈ N.flatten) : l.2 < gridWidth N := by
  obtain ⟨C,hC,hl⟩ := List.mem_flatten.mp hl
  have h : l.2 ∈ SAT_inNP.varsOfCnf N :=
    List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨C,hC,rfl⟩,
      List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨l,hl,rfl⟩, by simp [SAT_inNP.varsOfLiteral]⟩⟩
  exact Nat.lt_succ_of_le ((Nat.le_of_lt (EvalCnfSplit.varsOfCnf_lt_size h)).trans
    (CnfSerialize.size_le_encodeCnf_length N))

def reduceString (x : List Bool) : List Bool :=
  let N := SATStr.cnfOf x
  SATToSATStr.satToStr (expand (gridWidth N) (gridWidth N) N)

theorem reduceString_correct (x : List Bool) :
    SATStr x ↔ (∀ v : var,
      ((SATStr.cnfOf (reduceString x)).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
      SAT (SATStr.cnfOf (reduceString x)) := by
  let N := SATStr.cnfOf x
  have parse : SATStr.cnfOf (reduceString x) = expand (gridWidth N) (gridWidth N) N := by
    unfold SATStr.cnfOf reduceString
    rw [SATToSATStr.strBits_satToStr, CnfWellFormed.parseTotal_encodeCnf] <;> rfl
  rw [parse]
  have hw : 0 < gridWidth N := Nat.succ_pos _
  have sat := expand_sat N _ _ hw (width_fits N) (height_fits N)
  exact ⟨fun h => ⟨expand_occ N _ _ hw (width_fits N), sat.mpr h⟩, fun h => sat.mp h.2⟩

open CookLevin.Lang

/- The first scan obtains the row width and height in unary. A second scan writes
the renamed clauses. Finally a pair of bounded loops writes each row's cycle. -/
abbrev widthReg : Var := 1
abbrev heightReg : Var := 2
abbrev stream : Var := 3
abbrev readingLit : Var := 4
abbrev readingVar : Var := 5
abbrev column : Var := 7
abbrev output : Var := 8
abbrev headBit : Var := 9
abbrev outerIndex : Var := 10
abbrev innerIndex : Var := 11
abbrev flag : Var := 13
abbrev oneReg : Var := 14
abbrev rowStart : Var := 15
abbrev nextColumn : Var := 16
abbrev pending : Var := 17
abbrev maxTail : Var := 18
abbrev beyondMax : Var := 19

def yes (r : Var) : Cmd := .op (.copy r oneReg)
def no (r : Var) : Cmd := .op (.clear r)
def startScan : Cmd :=
  .op (.copy stream 0) ;; no readingLit ;; no readingVar ;; no pending

/-- The command arguments handle a clause end, a literal start, its sign, a unary
one, and the literal terminator, respectively. -/
def scan (clauseEnd litStart sign unaryOne litEnd : Cmd) : Cmd :=
  Cmd.forBnd outerIndex 0 (
    .op (.head headBit stream) ;; .op (.tail stream stream) ;;
    .ifBit readingLit
      (.ifBit readingVar
        (.ifBit headBit unaryOne (litEnd ;; no readingLit))
        (sign ;; yes readingVar))
      (.ifBit headBit (litStart ;; yes readingLit ;; no readingVar ;; yes pending)
        (clauseEnd ;; no pending)))

def prepare : Cmd :=
  SATStr.satStrBuild ;; .op (.copy 0 EvalCnfCmd.CNF_STREAM) ;;
  no oneReg ;; .op (.appendOne oneReg) ;;
  no widthReg ;; .forBnd outerIndex 0 (.op (.appendOne widthReg)) ;;
  .op (.appendOne widthReg) ;; .op (.copy heightReg widthReg)

def emitCopies : Cmd :=
  startScan ;; no column ;; no output ;;
  scan (.op (.appendZero output)) (.op (.appendOne output))
    (.ifBit headBit (.op (.appendOne output)) (.op (.appendZero output)))
    (.op (.concat output output widthReg))
    (.op (.concat output output column) ;; .op (.appendZero output) ;;
      .op (.appendOne column))

def emitRow : Cmd :=
  .forBnd innerIndex widthReg (
    .op (.appendOne output) ;; .op (.appendZero output) ;;
    .op (.concat output output rowStart) ;; .op (.concat output output innerIndex) ;;
    .op (.appendZero output) ;;
    .op (.appendOne output) ;; .op (.appendOne output) ;;
    .op (.concat output output rowStart) ;;
    .op (.copy nextColumn innerIndex) ;; .op (.appendOne nextColumn) ;;
    .op (.eqBit flag nextColumn widthReg) ;;
    .ifBit flag (no nextColumn) (.op (.concat output output nextColumn)) ;;
    .op (.appendZero output) ;; .op (.appendZero output))

def emitCycles : Cmd :=
  no rowStart ;;
  .forBnd outerIndex heightReg (emitRow ;; .op (.concat rowStart rowStart widthReg))

/-- The canonical parser sends malformed inputs to the one empty clause. -/
def program : Cmd :=
  prepare ;; emitCopies ;; emitCycles ;; .op (.copy 0 output)

/-- A bound on cost and on the length of every output register. The register bound
lets the next phase use the previous phase's output as its polynomial-size input. -/
def bounded (c : Cmd) : Prop :=
  ∃ p : Nat → Nat, inOPoly p ∧ monotonic p ∧
    ∀ (s : State) (n : Nat), (∀ r, (s.get r).length ≤ n) →
      c.cost s ≤ p n ∧ ∀ r, ((c.eval s).get r).length ≤ p n

theorem bounded_checked (c : Cmd) (ok : (c.chk (2^25 - 1)).1 = true) : bounded c := by
  obtain ⟨K,D,h⟩ := (Cmd.chk_sound c (2^25 - 1)).2 ok
  let p := fun n : Nat => K * (n+1)^D * (n+1) + n
  have power : inOPoly (fun n : Nat => (n+1)^D) := by
    refine ⟨D, 2^D, 1, ?_⟩
    intro n hn
    calc (n+1)^D ≤ (2*n)^D := Nat.pow_le_pow_left (by omega) _
         _ = _ := Nat.mul_pow ..
  refine ⟨p, inOPoly_add (inOPoly_mul (inOPoly_mul (inOPoly_const K) power)
    (inOPoly_add inOPoly_id (inOPoly_const 1))) inOPoly_id, ?_, ?_⟩
  · intro a b ab
    have plus : a+1 ≤ b+1 := by omega
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left K (Nat.pow_le_pow_left plus D)) plus) ab
  · intro s n hs
    obtain ⟨cost,regs,_⟩ := h s n n (fun r _ => hs r) hs
    exact ⟨Nat.le_trans cost (Nat.le_add_right ..), fun r => by
      have small := regs r
      have big := Nat.le_mul_of_pos_right (K * (n+1)^D) (by omega : 0 < n+1)
      dsimp [p]
      omega⟩

theorem bounded_seq {a b : Cmd} (ha : bounded a) (hb : bounded b) : bounded (a ;; b) := by
  obtain ⟨p,hp,mp,A⟩ := ha
  obtain ⟨q,hq,mq,B⟩ := hb
  refine ⟨fun n => 1 + p n + q (p n),
    inOPoly_add (inOPoly_add (inOPoly_const 1) hp) (inOPoly_comp hp hq), ?_, ?_⟩
  · intro i j hij
    exact Nat.add_le_add (Nat.add_le_add_left (mp _ _ hij) 1) (mq _ _ (mp _ _ hij))
  · intro s n hs
    obtain ⟨ca,ra⟩ := A s n hs
    obtain ⟨cb,rb⟩ := B (a.eval s) (p n) ra
    dsimp only
    rw [Cmd.cost_seq, Cmd.eval_seq]
    exact ⟨by omega, fun r => Nat.le_trans (rb r) (Nat.le_add_left ..)⟩

theorem bounded_branch (t : Var) {a b : Cmd} (ha : bounded a) (hb : bounded b) :
    bounded (.ifBit t a b) := by
  obtain ⟨p,hp,mp,A⟩ := ha
  obtain ⟨q,hq,mq,B⟩ := hb
  refine ⟨fun n => 1 + p n + q n, inOPoly_add (inOPoly_add (inOPoly_const 1) hp) hq, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_le_add (Nat.add_le_add_left (mp _ _ hij) 1) (mq _ _ hij)
  · intro s n hs
    obtain ⟨ca,ra⟩ := A s n hs
    obtain ⟨cb,rb⟩ := B s n hs
    dsimp only
    by_cases e : s.get t = [1]
    · rw [Cmd.cost_ifBit_true _ _ _ _ e, Cmd.eval_ifBit_true _ _ _ _ e]
      exact ⟨by omega, fun r => by have := ra r; omega⟩
    · rw [Cmd.cost_ifBit_false _ _ _ _ e, Cmd.eval_ifBit_false _ _ _ _ e]
      exact ⟨by omega, fun r => by have := rb r; omega⟩

theorem program_bounded : bounded program := by
  unfold program
  exact bounded_seq (bounded_checked _ (by decide)) (bounded_seq (bounded_checked _ (by decide))
    (bounded_seq (bounded_checked _ (by decide)) (bounded_checked _ (by decide))))

theorem program_registers : program.UsesBelow 25 := by
  have old : SATStr.satStrBuild.UsesBelow 25 := SATStr.satStrMfc_usesBelow.1
  simp only [program, prepare, Cmd.UsesBelow, old, true_and]
  simp [yes, no, startScan, emitCopies, scan, emitRow, emitCycles, Cmd.UsesBelow, Op.UsesBelow,
    widthReg, heightReg, stream, readingLit, readingVar, column, output, headBit, outerIndex,
    innerIndex, flag, oneReg, rowStart, nextColumn, pending, EvalCnfCmd.CNF_STREAM]

def runString (x : List Bool) := boolsOf ((program.eval (certState x)).get 0)

def machineWithBound (p : Nat → Nat) (poly : inOPoly p) (mono : monotonic p)
    (control : ∀ (s : State) (n : Nat), (∀ r, (s.get r).length ≤ n) →
      program.cost s ≤ p n ∧ ∀ r, ((program.eval s).get r).length ≤ p n) :
    PolyTimeComputableLang runString := by
  let budget := fun n : Nat => 2 * p n
  have bounds (x : List Bool) :=
    control (certState x) (encodable.size x) (fun r => calc
      ((certState x).get r).length ≤ (certState x).size := State.get_length_le_size _ _
      _ = x.length := State.size_certState _
      _ ≤ _ := CookLevin.length_le_size _)
  refine {
    c := program, encodeIn := certState, decodeOut := fun s => boolsOf (s.get 0),
    cost_bound := budget, cost_bound_poly := inOPoly_mul (inOPoly_const 2) poly,
    cost_bound_mono := fun a b h => Nat.mul_le_mul_left _ (mono a b h),
    encBound := id, encBound_poly := inOPoly_id, encBound_mono := fun _ _ h => h,
    encodeIn_size := fun x => by rw [State.size_certState]; exact CookLevin.length_le_size _,
    computes := fun _ => rfl, cost_le := ?_, output_size_le := ?_,
    enc_bit := ?_, regBound := 25, usesBelow := program_registers, width_le := ?_,
    decode_agree := ?_ }
  · intro x
    exact Nat.le_trans (bounds x).1 (by dsimp [budget]; omega)
  · intro x
    have h := (bounds x).2 0
    have len : (runString x).length = ((program.eval (certState x)).get 0).length := by
      simp [runString, boolsOf]
    have hout : (runString x).length ≤ p (encodable.size x) := len.trans_le h
    exact (CookLevin.size_le_two_mul_length _).trans (Nat.mul_le_mul_left 2 hout)
  · intro x reg hr i hi
    simp only [certState, List.mem_singleton] at hr
    subst reg
    exact strBits_bit x i hi
  · intro x
    simp [certState]
  · intro x n
    have eqs : AgreeBelow 25 (certState x ++ List.replicate n []) (certState x) :=
      fun r _ => State.get_append_replicate_nil _ _ _
    rw [Cmd.eval_agree program 25 program_registers eqs 0 (by decide)]

noncomputable def machineProgram : PolyTimeComputableLang runString :=
  machineWithBound program_bounded.choose program_bounded.choose_spec.1
    program_bounded.choose_spec.2.1 program_bounded.choose_spec.2.2

abbrev U (n : Nat) : List Nat := List.replicate n 1

theorem eval_branch (s : State) (t : Var) (a b : Cmd) :
    (Cmd.ifBit t a b).eval s = (if s.get t = [1] then a.eval s else b.eval s) := by
  split
  · exact Cmd.eval_ifBit_true t a b s ‹_›
  · exact Cmd.eval_ifBit_false t a b s ‹_›

theorem reg_read (s : State) (v r : Var) (xs : List Nat) :
    (s.set v xs).get r = if r = v then xs else s.get r := by
  split
  · subst r; exact State.get_set_eq ..
  · exact State.get_set_ne s v xs r ‹_›

theorem U_add (m n : Nat) : U (m+n) = U m ++ U n := List.replicate_add ..

theorem U_succ (n : Nat) : U (n+1) = U n ++ [1] := U_add n 1

theorem parse_canonical (x : List Bool) :
    (SATStr.satStrBuild.eval (certState x)).get EvalCnfCmd.CNF_STREAM = encodeCnf (SATStr.cnfOf x) := by
  have A : AgreeBelow 25 (certState x) (SATStr.strEIn (x,[])) :=
    fun r _ => (State.get_append_replicate_nil (certState x) 1 r).symm
  have uses : SATStr.satStrBuild.UsesBelow 25 := SATStr.satStrMfc_usesBelow.1
  have eqs := Cmd.eval_agree SATStr.satStrBuild 25 uses A EvalCnfCmd.CNF_STREAM (by decide)
  exact eqs.trans (SATStr.satStrBuild_get x []).2.2.1

def initData : Cmd := .op (.copy 0 EvalCnfCmd.CNF_STREAM) ;; no oneReg ;;
  .op (.appendOne oneReg) ;; no widthReg

theorem initData_correct (z : State) :
    (initData.eval z).get 0 = z.get EvalCnfCmd.CNF_STREAM ∧
    (initData.eval z).get oneReg = [1] ∧ (initData.eval z).get widthReg = [] := by
  simp [initData, no, Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, oneReg, widthReg]

def widthLoop : Cmd := .forBnd outerIndex 0 (.op (.appendOne widthReg))

theorem widthLoop_correct (a : State) (hw : a.get widthReg = []) :
    (widthLoop.eval a).get widthReg = U (a.get 0).length := by
  unfold widthLoop
  rw [Cmd.eval_forBnd]
  apply Cmd.foldlState_range_induct _ _ _ _ (fun i st => st.get widthReg = U i) hw
  intro i st hi hs
  change ((st.set outerIndex (U i)).set widthReg
    (((st.set outerIndex (U i)).get widthReg) ++ [1])).get widthReg = U (i+1)
  rw [State.get_set_eq, State.get_set_ne _ _ _ _ (by decide), hs, U_succ]

def finishSize : Cmd := .op (.appendOne widthReg) ;; .op (.copy heightReg widthReg)

theorem finishSize_correct (b : State) (N : cnf)
    (h0 : b.get 0 = encodeCnf N) (h1 : b.get oneReg = [1])
    (hw : b.get widthReg = U (encodeCnf N).length) :
    (finishSize.eval b).get 0 = encodeCnf N ∧ (finishSize.eval b).get oneReg = [1] ∧
    (finishSize.eval b).get widthReg = U (gridWidth N) ∧ (finishSize.eval b).get heightReg = U (gridWidth N) := by
  simp [finishSize, Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, oneReg, heightReg, widthReg,
    h0, h1, hw, gridWidth, U_succ]

theorem seq_assoc_eval (a b c : Cmd) (s : State) :
    (a ;; (b ;; c)).eval s = ((a ;; b) ;; c).eval s := rfl

theorem prepare_eval (s : State) : prepare.eval s =
    finishSize.eval (widthLoop.eval (initData.eval (SATStr.satStrBuild.eval s))) := by
  simp only [prepare, finishSize, widthLoop, initData, Cmd.eval_seq]

theorem prepare_correct (x : List Bool) :
    let N := SATStr.cnfOf x
    let s := prepare.eval (certState x)
    s.get 0 = encodeCnf N ∧ s.get oneReg = [1] ∧
    s.get widthReg = U (gridWidth N) ∧ s.get heightReg = U (gridWidth N) := by
  let z := SATStr.satStrBuild.eval (certState x)
  let a := initData.eval z
  let b := widthLoop.eval a
  have ha := initData_correct z
  have A0 : a.get 0 = encodeCnf (SATStr.cnfOf x) := ha.1.trans (parse_canonical x)
  have W := widthLoop_correct a ha.2.2
  rw [A0] at W
  have B0 := Cmd.eval_get_of_not_writes widthLoop a 0 (by decide)
  have B1 := Cmd.eval_get_of_not_writes widthLoop a oneReg (by decide)
  dsimp only
  rw [prepare_eval]
  exact finishSize_correct b _ (B0.trans A0) (B1.trans ha.2.1) W

def edge : Cmd :=
  .op (.appendOne output) ;; .op (.appendZero output) ;;
    .op (.concat output output rowStart) ;; .op (.concat output output innerIndex) ;;
    .op (.appendZero output) ;;
    .op (.appendOne output) ;; .op (.appendOne output) ;;
    .op (.concat output output rowStart) ;;
    .op (.copy nextColumn innerIndex) ;; .op (.appendOne nextColumn) ;;
    .op (.eqBit flag nextColumn widthReg) ;;
    .ifBit flag (no nextColumn) (.op (.concat output output nextColumn)) ;;
    .op (.appendZero output) ;; .op (.appendZero output)


theorem edge_correct (s : State) (w base i : Nat) (h : i < w)
    (hw : s.get widthReg = U w) (hb : s.get rowStart = U base)
    (hi : s.get innerIndex = U i) :
    (edge.eval s).get output = s.get output ++
      encodeClause (implication (base+i) (base+(i+1)%w)) := by
  have noWrap : i+1 ≠ w → i+1 < w := by omega
  by_cases last : i+1 = w
  · have eq : U i ++ [1] = U w := by rw [← U_succ, last]
    simp (disch := decide) [-List.replicate_append_replicate, edge, eval_branch, Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, widthReg,
      rowStart, innerIndex, nextColumn, output, flag, no, widthReg, innerIndex, rowStart,
      eq, hw, hb, hi, last, Nat.mod_self, implication, encodeClause, encodeLit, U_add,
      List.append_assoc]
  · have neq : U i ++ [1] ≠ U w := by
      intro e
      have hlen := congrArg List.length e
      simp [U] at hlen
      omega
    have small := Nat.mod_eq_of_lt (noWrap last)
    simp (disch := decide) [-List.replicate_append_replicate, edge, eval_branch, Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, widthReg,
      rowStart, innerIndex, nextColumn, output, flag, no, hw, hb, hi, neq, small,
      implication, encodeClause, encodeLit, U_add, U_succ, List.append_assoc]


theorem enc_append (A B : cnf) : encodeCnf (A ++ B) = encodeCnf A ++ encodeCnf B := by
  induction A with
  | nil => rfl
  | cons C A ih =>
    simp only [List.cons_append, CnfSerialize.encodeCnf_cons, ih, List.append_assoc]

def firstEdges (w base n : Nat) : cnf :=
  (List.range n).map fun i => implication (base+i) (base+(i+1)%w)

theorem emitRow_correct (s : State) (w base : Nat)
    (hw : s.get widthReg = U w) (hb : s.get rowStart = U base) :
    (emitRow.eval s).get output = s.get output ++ encodeCnf (firstEdges w base w) := by
  change ((Cmd.forBnd innerIndex widthReg edge).eval s).get output = _
  rw [Cmd.eval_forBnd, hw, List.length_replicate]
  let inv := fun (i : Nat) (z : State) =>
    z.get output = s.get output ++ encodeCnf (firstEdges w base i) ∧
      z.get widthReg = U w ∧ z.get rowStart = U base
  have h := Cmd.foldlState_range_induct edge innerIndex w s inv
    (by exact ⟨by simp [firstEdges, encodeCnf], hw, hb⟩) (by
      rintro i z hi ⟨ho,hw',hb'⟩
      let a := z.set innerIndex (U i)
      have aw : a.get widthReg = U w := (State.get_set_ne _ _ _ _ (by decide)).trans hw'
      have ab : a.get rowStart = U base := (State.get_set_ne _ _ _ _ (by decide)).trans hb'
      have ao : a.get output = z.get output := State.get_set_ne _ _ _ _ (by decide)
      refine ⟨?_, (Cmd.eval_get_of_not_writes edge a widthReg (by decide)).trans aw,
        (Cmd.eval_get_of_not_writes edge a rowStart (by decide)).trans ab⟩
      have he := edge_correct a w base i hi aw ab (State.get_set_eq ..)
      rw [ao, ho] at he
      simpa only [firstEdges, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        enc_append, CnfSerialize.encodeCnf_cons, show encodeCnf [] = [] from rfl,
        List.append_nil, List.append_assoc] using he)
  exact h.1

theorem emitCycles_correct (s : State) (w H : Nat) (hw : s.get widthReg = U w)
    (hh : s.get heightReg = U H) :
    (emitCycles.eval s).get output =
      s.get output ++ encodeCnf ((List.range H).flatMap (row w)) := by
  let z := (no rowStart).eval s
  let body := emitRow ;; Cmd.op (.concat rowStart rowStart widthReg)
  change ((Cmd.forBnd outerIndex heightReg body).eval z).get output = _
  have zh : z.get heightReg = U H := (State.get_set_ne _ _ _ _ (by decide)).trans hh
  rw [Cmd.eval_forBnd, zh, List.length_replicate]
  let inv := fun (i : Nat) (st : State) =>
    st.get output = s.get output ++ encodeCnf ((List.range i).flatMap (row w)) ∧
    st.get widthReg = U w ∧ st.get rowStart = U (i*w)
  have h := Cmd.foldlState_range_induct body outerIndex H z inv (by
    dsimp [inv,z,no,Cmd.eval_op,Op.eval]
    simp [reg_read, rowStart, output, widthReg, hw, encodeCnf, U]) (by
    rintro i st hi ⟨ho, hw', hb⟩
    let a := st.set outerIndex (U i)
    let b := emitRow.eval a
    have aw : a.get widthReg = U w := (State.get_set_ne _ _ _ _ (by decide)).trans hw'
    have ab : a.get rowStart = U (i*w) := (State.get_set_ne _ _ _ _ (by decide)).trans hb
    have ao : a.get output = st.get output := State.get_set_ne _ _ _ _ (by decide)
    have bw : b.get widthReg = U w := (Cmd.eval_get_of_not_writes emitRow a widthReg (by decide)).trans aw
    have bb : b.get rowStart = U (i*w) := (Cmd.eval_get_of_not_writes emitRow a rowStart (by decide)).trans ab
    have out := emitRow_correct a w (i*w) aw ab
    change b.get output = _ at out
    rw [ao,ho] at out
    change inv (i+1) (b.set rowStart (b.get rowStart ++ b.get widthReg))
    refine ⟨?_, (State.get_set_ne _ _ _ _ (by decide)).trans bw, ?_⟩
    · rw [State.get_set_ne _ _ _ _ (by decide), out]
      simp [List.range_succ, List.flatMap_append, enc_append, firstEdges, row, List.append_assoc]
    · rw [State.get_set_eq, bb, bw, Nat.succ_mul, U_add])
  exact h.1

def copyStep : Cmd :=
  .op (.head headBit stream) ;; .op (.tail stream stream) ;;
  .ifBit readingLit
    (.ifBit readingVar
      (.ifBit headBit (.op (.concat output output widthReg))
        ((.op (.concat output output column) ;; .op (.appendZero output) ;;
          .op (.appendOne column)) ;; no readingLit))
      ((.ifBit headBit (.op (.appendOne output)) (.op (.appendZero output))) ;; yes readingVar))
    (.ifBit headBit ((.op (.appendOne output)) ;; yes readingLit ;; no readingVar ;; yes pending)
      ((.op (.appendZero output)) ;; no pending))

def portion (k n : Nat) (s : State) : State :=
  Cmd.foldlState copyStep outerIndex (List.range' k n) s

theorem portion_add (n m k : Nat) (s : State) :
    portion k (n+m) s = portion (k+n) m (portion k n s) := by
  simp only [portion, ← List.range'_append_1 (s := k) (m := n) (n := m),
    Cmd.foldlState, List.foldl_append]

theorem portion_zero (k : Nat) (s : State) : portion k 0 s = s := rfl

theorem portion_next (n k : Nat) (s : State) :
    portion k (n+1) s = portion (k+1) n (copyStep.eval (s.set outerIndex (U k))) := by
  simp only [portion, List.range'_succ, Cmd.foldlState, List.foldl_cons]

/-- Register values at a point in the second scan. -/
structure ScanAt (s : State) (tail out : List Nat) (w off : Nat) (lit unary : Bool) : Prop where
  cursor : s.get stream = tail
  result : s.get output = out
  width : s.get widthReg = U w
  columnValue : s.get column = U off
  one : s.get oneReg = [1]
  phase : s.get readingLit = SATStr.flagOf lit
  variablePhase : lit = true → s.get readingVar = SATStr.flagOf unary

theorem openLit (s : State) (k w off : Nat) (tail out : List Nat) 
    (inv : ScanAt s (1 :: tail) out w off false false) :
    ScanAt (copyStep.eval (s.set outerIndex (U k))) tail (out ++ [1]) w (off) true false := by
  obtain ⟨hc, ho, hw, hcol, h1, hphase, hv⟩ := inv
  constructor <;>
    simp (disch := decide) [-List.replicate_append_replicate, copyStep, no, yes, eval_branch,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, outerIndex, readingVar, readingLit,
      output, widthReg, column, oneReg, stream, pending, headBit, hc, ho, hw, hcol,
      h1, hphase, hv, SATStr.flagOf, U_succ] at *

theorem signLit (s : State) (k w off : Nat) (tail out : List Nat) (pol : Bool)
    (inv : ScanAt s ((if pol then 1 else 0) :: tail) out w off true false) :
    ScanAt (copyStep.eval (s.set outerIndex (U k))) tail (out ++ [if pol then 1 else 0]) w (off) true true := by
  obtain ⟨hc, ho, hw, hcol, h1, hphase, hv⟩ := inv
  specialize hv rfl
  cases pol <;> constructor <;>
    simp (disch := decide) [-List.replicate_append_replicate, copyStep, no, yes, eval_branch,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, outerIndex, readingVar, readingLit,
      output, widthReg, column, oneReg, stream, pending, headBit, hc, ho, hw, hcol,
      h1, hphase, hv, SATStr.flagOf, U_succ] at *

theorem unaryCell (s : State) (k w off : Nat) (tail out : List Nat) 
    (inv : ScanAt s (1 :: tail) out w off true true) :
    ScanAt (copyStep.eval (s.set outerIndex (U k))) tail (out ++ U w) w (off) true true := by
  obtain ⟨hc, ho, hw, hcol, h1, hphase, hv⟩ := inv
  specialize hv rfl
  constructor <;>
    simp (disch := decide) [-List.replicate_append_replicate, copyStep, no, yes, eval_branch,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, outerIndex, readingVar, readingLit,
      output, widthReg, column, oneReg, stream, pending, headBit, hc, ho, hw, hcol,
      h1, hphase, hv, SATStr.flagOf, U_succ] at *

theorem endLit (s : State) (k w off : Nat) (tail out : List Nat) 
    (inv : ScanAt s (0 :: tail) out w off true true) :
    ScanAt (copyStep.eval (s.set outerIndex (U k))) tail ((out ++ U off) ++ [0]) w (off+1) false false := by
  obtain ⟨hc, ho, hw, hcol, h1, hphase, hv⟩ := inv
  specialize hv rfl
  constructor <;>
    simp (disch := decide) [-List.replicate_append_replicate, copyStep, no, yes, eval_branch,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, outerIndex, readingVar, readingLit,
      output, widthReg, column, oneReg, stream, pending, headBit, hc, ho, hw, hcol,
      h1, hphase, hv, SATStr.flagOf, U_succ] at *

theorem endClause (s : State) (k w off : Nat) (tail out : List Nat) 
    (inv : ScanAt s (0 :: tail) out w off false false) :
    ScanAt (copyStep.eval (s.set outerIndex (U k))) tail (out ++ [0]) w (off) false false := by
  obtain ⟨hc, ho, hw, hcol, h1, hphase, hv⟩ := inv
  constructor <;>
    simp (disch := decide) [-List.replicate_append_replicate, copyStep, no, yes, eval_branch,
      Cmd.eval_seq, Cmd.eval_op, Op.eval, reg_read, outerIndex, readingVar, readingLit,
      output, widthReg, column, oneReg, stream, pending, headBit, hc, ho, hw, hcol,
      h1, hphase, hv, SATStr.flagOf, U_succ] at *

theorem unaryPart (v k w off : Nat) (tail out : List Nat) (s : State)
    (inv : ScanAt s (U v ++ tail) out w off true true) :
    ScanAt (portion k v s) tail (out ++ U (v*w)) w off true true := by
  induction v generalizing k out s with
  | zero => simpa [U, portion_zero] using inv
  | succ v ih =>
    rw [portion_next]
    have h := unaryCell s k w off (U v ++ tail) out (by
      simpa [U, List.replicate_succ] using inv)
    have concl := ih (k+1) (out ++ U w) _ h
    rwa [Nat.succ_mul, Nat.add_comm (v*w) w, U_add, ← List.append_assoc]

theorem literalPart (l : literal) (k w off : Nat) (tail out : List Nat) (s : State)
    (inv : ScanAt s (encodeLit l ++ tail) out w off false false) :
    ScanAt (portion k (encodeLit l).length s) tail
      (out ++ encodeLit (l.1, l.2*w+off)) w (off+1) false false := by
  obtain ⟨pol,v⟩ := l
  let bit : Nat := if pol then 1 else 0
  let rest := U v ++ 0 :: tail
  have a := openLit s k w off (bit :: rest) out (by
    simpa [encodeLit, bit, rest, U, List.append_assoc] using inv)
  have b := signLit _ (k+1) w off rest (out ++ [1]) pol a
  have c := unaryPart v (k+2) w off (0 :: tail) _ _ b
  have d := endLit _ (k+2+v) w off tail _ c
  have len : (encodeLit (pol,v)).length = 1+(1+(v+1)) := by simp [encodeLit]; omega
  rw [len, Nat.add_comm 1 (1+(v+1)), portion_next, Nat.add_comm 1 (v+1), portion_next,
    portion_add v 1]
  simpa only [portion, List.range'_succ, List.range'_zero, Cmd.foldlState, List.foldl_cons,
    List.foldl_nil, encodeLit, U_add, List.append_assoc, List.cons_append, List.nil_append,
    List.replicate_add, Nat.add_assoc, U, List.replicate_succ, List.replicate_zero, Nat.reduceAdd] using d

theorem clausePart (C : clause) (k w off : Nat) (tail out : List Nat) (s : State)
    (inv : ScanAt s (clauseBody C ++ tail) out w off false false) :
    ScanAt (portion k (clauseBody C).length s) tail
      (out ++ clauseBody (copies w off C)) w (off+C.length) false false := by
  induction C generalizing k off out s with
  | nil => simpa [clauseBody, copies, portion_zero] using inv
  | cons l C ih =>
    obtain ⟨pol,v⟩ := l
    rw [CnfSerialize.clauseBody_cons, List.length_append, portion_add]
    have a := literalPart (pol,v) k w off (clauseBody C ++ tail) out s
      (by simpa only [CnfSerialize.clauseBody_cons, List.append_assoc] using inv)
    have b := ih (k+(encodeLit (pol,v)).length) (off+1) _ _ a
    simpa only [copies, CnfSerialize.clauseBody_cons, List.length_cons, List.append_assoc,
      Nat.add_assoc, Nat.add_comm 1 C.length] using b

theorem formulaPart (N : cnf) (k w off : Nat) (tail out : List Nat) (s : State)
    (inv : ScanAt s (encodeCnf N ++ tail) out w off false false) :
    ScanAt (portion k (encodeCnf N).length s) tail
      (out ++ encodeCnf (copyClauses w off N)) w (off+N.flatten.length) false false := by
  induction N generalizing k off out s with
  | nil => simpa [encodeCnf, copyClauses, portion_zero] using inv
  | cons C N ih =>
    have a := clausePart C k w off (0 :: (encodeCnf N ++ tail)) out s (by
      simpa only [CnfSerialize.encodeCnf_cons, CnfSerialize.encodeClause_eq, List.append_assoc,
        List.cons_append, List.nil_append] using inv)
    have b := endClause _ (k+(clauseBody C).length) w (off+C.length) _ _ a
    have c := ih (k+((clauseBody C).length+1)) (off+C.length) _ _ b
    rw [CnfSerialize.encodeCnf_cons, CnfSerialize.encodeClause_eq, List.length_append,
      List.length_append, portion_add, portion_add]
    simpa only [portion, List.range'_succ, List.range'_zero, Cmd.foldlState,
      List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil, copyClauses,
      CnfSerialize.encodeCnf_cons, CnfSerialize.encodeClause_eq, List.flatten_cons,
      List.length_append, List.append_assoc, Nat.add_assoc] using c

def copyInit : Cmd := startScan ;; no column ;; no output

theorem copyInit_correct (s : State) (N : cnf) (w : Nat)
    (h : s.get 0 = encodeCnf N) (hw : s.get widthReg = U w) (hone : s.get oneReg = [1]) :
    ScanAt (copyInit.eval s) (encodeCnf N ++ []) [] w 0 false false := by
  constructor <;> simp [copyInit, startScan, no, Cmd.eval_seq, Cmd.eval_op, Op.eval,
    reg_read, oneReg, widthReg, column, stream, output, pending, readingLit, readingVar,
    h, hw, hone, SATStr.flagOf]

theorem emitCopies_eval (s : State) :
    emitCopies.eval s = (Cmd.forBnd outerIndex 0 copyStep).eval (copyInit.eval s) := by
  simp only [emitCopies, copyInit, scan, copyStep, Cmd.eval_seq]

theorem emitCopies_correct (s : State) (N : cnf) (w : Nat)
    (h : s.get 0 = encodeCnf N) (hw : s.get widthReg = U w) (hone : s.get oneReg = [1]) :
    (emitCopies.eval s).get output = encodeCnf (copyClauses w 0 N) := by
  have h0 := copyInit_correct s N w h hw hone
  have a := (formulaPart N 0 w 0 [] [] (copyInit.eval s) h0).result
  have eq0 : (copyInit.eval s).get 0 = encodeCnf N :=
    (Cmd.eval_get_of_not_writes copyInit s 0 (by decide)).trans h
  rw [emitCopies_eval, Cmd.eval_forBnd, eq0, List.range_eq_range']
  exact a

theorem runString_correct (x : List Bool) : runString x = reduceString x := by
  let N := SATStr.cnfOf x
  let w := gridWidth N
  let p := prepare.eval (certState x)
  let c := emitCopies.eval p
  obtain ⟨input,one,width,height⟩ := prepare_correct x
  have hw : c.get widthReg = U w :=
    (Cmd.eval_get_of_not_writes emitCopies p widthReg (by decide)).trans width
  have hh : c.get heightReg = U w :=
    (Cmd.eval_get_of_not_writes emitCopies p heightReg (by decide)).trans height
  have out : c.get output = encodeCnf (copyClauses w 0 N) :=
    emitCopies_correct p N w input width one
  have final := emitCycles_correct c w w hw hh
  rw [out, ← enc_append] at final
  unfold runString program
  simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
  change boolsOf ((emitCycles.eval c).get output) = _
  rw [final]
  rfl

end PvsNP.Units.m3_sat_to_3occ_sat_aux


open PvsNP.Units.m3_sat_to_3occ_sat_aux in
theorem PvsNP.Units.m3_sat_to_3occ_sat : CookLevin.reducesPoly SATStr
    (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
      SAT (SATStr.cnfOf x)) := by
  obtain ⟨t, M, ht, valid, tapes, comp⟩ :=
    machineProgram.toMachine (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨runString, t, M, ht, valid, tapes, comp, fun x => ?_⟩
  rw [runString_correct]
  exact reduceString_correct x
