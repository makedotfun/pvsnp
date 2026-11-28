import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tl_lang_len_two_squares_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

/-- One step of the two-square search on the state `pairB a (pairB b (pairB fnd x))`:
test whether `a ^ 2 + b ^ 2 = x.length` for the current pair, then advance
lexicographically (`b` wraps at the input length, incrementing `a`). -/
def tsStep (s : List Bool) : List Bool :=
  let a := (unpairB s).1
  let b := (unpairB (unpairB s).2).1
  let fnd := (unpairB (unpairB (unpairB s).2).2).1
  let x := (unpairB (unpairB (unpairB s).2).2).2
  let sum := mulU a a ++ mulU b b
  let found := sel (leFlag sum x) [] (sel (leFlag x sum) [] [true])
  let wrap := sel (leFlag b x) [] (sel (leFlag x b) [] [true])
  let fnd' := sel fnd found [true]
  let a' := sel wrap a (true :: a)
  let b' := sel wrap (true :: b) []
  pairB a' (pairB b' (pairB fnd' x))

theorem cpt_tsStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) tsStep := by
  have ha : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have h22 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hfnd : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 h22
  have hx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 h22
  have hasq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (unpairB s).1 (unpairB s).1) := cpt_mulU2 ha ha
  have hbsq : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1) :=
    cpt_mulU2 hb hb
  have hsum : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => mulU (unpairB s).1 (unpairB s).1 ++
        mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1) :=
    cpt_comp (cpt_pair hasq hbsq) cpt_append
  have hfound := cpt_sel (cpt_leFlag hsum hx) (cpt_const [])
    (cpt_sel (cpt_leFlag hx hsum) (cpt_const []) (cpt_const [true]))
  have hwrap := cpt_sel (cpt_leFlag hb hx) (cpt_const [])
    (cpt_sel (cpt_leFlag hx hb) (cpt_const []) (cpt_const [true]))
  have hfnd' := cpt_sel hfnd hfound (cpt_const [true])
  have ha' := cpt_sel hwrap ha (cpt_cons1 true ha)
  have hb' := cpt_sel hwrap (cpt_cons1 true hb) (cpt_const [])
  exact cpt_pairB2 ha' (cpt_pairB2 hb' (cpt_pairB2 hfnd' hx))

theorem tsStep_length (s : List Bool) : (tsStep s).length ≤ s.length + 10 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := unpairB_length (unpairB (unpairB s).2).2
  have hfound : (sel (leFlag (mulU (unpairB s).1 (unpairB s).1 ++
        mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1)
        (unpairB (unpairB (unpairB s).2).2).2) []
      (sel (leFlag (unpairB (unpairB (unpairB s).2).2).2
        (mulU (unpairB s).1 (unpairB s).1 ++
          mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1)) [] [true])).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  have hwrap : (sel (leFlag (unpairB (unpairB s).2).1
        (unpairB (unpairB (unpairB s).2).2).2) []
      (sel (leFlag (unpairB (unpairB (unpairB s).2).2).2
        (unpairB (unpairB s).2).1) [] [true])).length ≤ 1 := by
    unfold sel leFlag; split_ifs <;> simp
  have ha' : (sel (sel (leFlag (unpairB (unpairB s).2).1
        (unpairB (unpairB (unpairB s).2).2).2) []
      (sel (leFlag (unpairB (unpairB (unpairB s).2).2).2
        (unpairB (unpairB s).2).1) [] [true]))
      (unpairB s).1 (true :: (unpairB s).1)).length ≤ (unpairB s).1.length + 1 := by
    unfold sel; split_ifs <;> simp
  have hb' : (sel (sel (leFlag (unpairB (unpairB s).2).1
        (unpairB (unpairB (unpairB s).2).2).2) []
      (sel (leFlag (unpairB (unpairB (unpairB s).2).2).2
        (unpairB (unpairB s).2).1) [] [true]))
      (true :: (unpairB (unpairB s).2).1) []).length ≤
      (unpairB (unpairB s).2).1.length + 1 := by
    unfold sel; split_ifs <;> simp
  have hfnd' : (sel (unpairB (unpairB (unpairB s).2).2).1
      (sel (leFlag (mulU (unpairB s).1 (unpairB s).1 ++
        mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1)
        (unpairB (unpairB (unpairB s).2).2).2) []
      (sel (leFlag (unpairB (unpairB (unpairB s).2).2).2
        (mulU (unpairB s).1 (unpairB s).1 ++
          mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).1)) [] [true]))
      [true]).length ≤ 1 := by
    unfold sel; split_ifs <;> simp [hfound]
  simp only [tsStep, pairB_length, List.length_cons]
  omega

theorem mulU_length_eq (a b : List Bool) : (mulU a b).length = a.length * b.length := by
  simp [mulU]

theorem eqFlag_eq (a b : List Bool) :
    sel (leFlag a b) [] (sel (leFlag b a) [] [true]) =
      if a.length = b.length then [true] else [] := by
  unfold sel leFlag
  by_cases h1 : a.length ≤ b.length <;> by_cases h2 : b.length ≤ a.length
  · have heq : a.length = b.length := by omega
    simp [h1, h2, heq]
  · have hne : a.length ≠ b.length := by omega
    simp [h1, h2, hne]
  · have hne : a.length ≠ b.length := by omega
    simp [h1, h2, hne]
  · omega

/-- The step on a well-formed state, in `if` form. -/
theorem tsStep_apply (a₀ b₀ fnd₀ x : List Bool) (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    tsStep (pairB a₀ (pairB b₀ (pairB fnd₀ x))) =
      pairB (if b₀.length = x.length then true :: a₀ else a₀)
        (pairB (if b₀.length = x.length then [] else true :: b₀)
          (pairB (if a₀.length ^ 2 + b₀.length ^ 2 = x.length then [true] else fnd₀) x)) := by
  have hsumlen : (mulU a₀ a₀ ++ mulU b₀ b₀).length = a₀.length ^ 2 + b₀.length ^ 2 := by
    rw [List.length_append, mulU_length_eq, mulU_length_eq, ← pow_two, ← pow_two]
  simp only [tsStep, unpairB_pairB, eqFlag_eq, hsumlen]
  rcases hfnd with rfl | rfl <;> simp only [sel] <;> split_ifs <;> simp_all

/-- Uniqueness of the pair index `a * (n + 1) + b` for `b ≤ n`. -/
theorem idx_unique {n a b a₀ b₀ : ℕ} (hb : b ≤ n) (hb₀ : b₀ ≤ n)
    (h : a * (n + 1) + b = a₀ * (n + 1) + b₀) : a = a₀ ∧ b = b₀ := by
  have key : a ≤ a₀ ∧ a₀ ≤ a := by
    constructor
    · by_contra hlt
      push_neg at hlt
      have h1 : (a₀ + 1) * (n + 1) ≤ a * (n + 1) :=
        Nat.mul_le_mul hlt (le_refl (n + 1))
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · by_contra hlt
      push_neg at hlt
      have h1 : (a + 1) * (n + 1) ≤ a₀ * (n + 1) :=
        Nat.mul_le_mul hlt (le_refl (n + 1))
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
  have ha : a = a₀ := Nat.le_antisymm key.1 key.2
  refine ⟨ha, ?_⟩
  exact Nat.add_left_cancel (by rw [ha] at h; exact h)

theorem tsStep_iter_or (m : ℕ) (a₀ b₀ fnd₀ x : List Bool)
    (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    let r := (unpairB (unpairB (unpairB (tsStep^[m] (pairB a₀ (pairB b₀ (pairB fnd₀ x))))).2).2).1
    r = [] ∨ r = [true] := by
  induction m generalizing a₀ b₀ fnd₀ with
  | zero => simpa [unpairB_pairB] using hfnd
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    rw [tsStep_apply a₀ b₀ fnd₀ x hfnd]
    exact ih _ _ _ (by
      by_cases h : a₀.length ^ 2 + b₀.length ^ 2 = x.length
      · simp [h]
      · simp [h]; exact hfnd)

theorem tsStep_iter_iff (m : ℕ) (a₀ b₀ fnd₀ x : List Bool)
    (hb₀ : b₀.length ≤ x.length)
    (hfnd : fnd₀ = [] ∨ fnd₀ = [true]) :
    (unpairB (unpairB (unpairB (tsStep^[m] (pairB a₀ (pairB b₀ (pairB fnd₀ x))))).2).2).1 = [true] ↔
      (fnd₀ = [true] ∨ ∃ a b : ℕ,
        a₀.length * (x.length + 1) + b₀.length ≤ a * (x.length + 1) + b ∧
        a * (x.length + 1) + b < a₀.length * (x.length + 1) + b₀.length + m ∧
        b ≤ x.length ∧ a ^ 2 + b ^ 2 = x.length) := by
  induction m generalizing a₀ b₀ fnd₀ with
  | zero =>
    simp only [Function.iterate_zero, id_eq, unpairB_pairB]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨a, b, h1, h2, -, -⟩)
      · exact h
      · omega
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    rw [tsStep_apply a₀ b₀ fnd₀ x hfnd]
    have hb₁ : (if b₀.length = x.length then [] else true :: b₀).length ≤ x.length := by
      by_cases h : b₀.length = x.length
      · simp [h]
      · simp [h]; omega
    have hfnd₁ : (if a₀.length ^ 2 + b₀.length ^ 2 = x.length then [true] else fnd₀) = [] ∨
        (if a₀.length ^ 2 + b₀.length ^ 2 = x.length then [true] else fnd₀) = [true] := by
      by_cases h : a₀.length ^ 2 + b₀.length ^ 2 = x.length
      · simp [h]
      · simp [h]; exact hfnd
    rw [ih _ _ _ hb₁ hfnd₁]
    have hidx : (if b₀.length = x.length then true :: a₀ else a₀).length * (x.length + 1) +
        (if b₀.length = x.length then [] else true :: b₀).length =
        a₀.length * (x.length + 1) + b₀.length + 1 := by
      by_cases h : b₀.length = x.length
      · simp only [h, if_true, List.length_cons, List.length_nil]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [h, if_false, List.length_cons]
        omega
    have hfnd₁iff : (if a₀.length ^ 2 + b₀.length ^ 2 = x.length then [true] else fnd₀) = [true] ↔
        (fnd₀ = [true] ∨ a₀.length ^ 2 + b₀.length ^ 2 = x.length) := by
      by_cases h : a₀.length ^ 2 + b₀.length ^ 2 = x.length
      · rw [if_pos h]
        constructor
        · intro _; exact Or.inr h
        · intro _; rfl
      · rw [if_neg h]
        constructor
        · intro hc; exact Or.inl hc
        · rintro (h1 | h1)
          · exact h1
          · exact absurd h1 h
    have htest : (a₀.length ^ 2 + b₀.length ^ 2 = x.length) ↔
        ∃ a b : ℕ, a * (x.length + 1) + b = a₀.length * (x.length + 1) + b₀.length ∧
          b ≤ x.length ∧ a ^ 2 + b ^ 2 = x.length := by
      constructor
      · intro hsum
        exact ⟨a₀.length, b₀.length, rfl, hb₀, hsum⟩
      · rintro ⟨a, b, hidx0, hb, hsum⟩
        obtain ⟨ha, hb'⟩ := idx_unique hb hb₀ hidx0
        subst ha; subst hb'
        exact hsum
    rw [hidx]
    constructor
    · rintro (h | ⟨a, b, h1, h2, hb, hsum⟩)
      · rw [hfnd₁iff] at h
        rcases h with h | h
        · exact Or.inl h
        · rw [htest] at h
          obtain ⟨a, b, hidx0, hb, hsum⟩ := h
          exact Or.inr ⟨a, b, by omega, by omega, hb, hsum⟩
      · exact Or.inr ⟨a, b, by omega, by omega, hb, hsum⟩
    · rintro (h | ⟨a, b, h1, h2, hb, hsum⟩)
      · rw [hfnd₁iff]
        exact Or.inl (Or.inl h)
      · by_cases hidx0 : a * (x.length + 1) + b = a₀.length * (x.length + 1) + b₀.length
        · exact Or.inl ((hfnd₁iff).2 (Or.inr ((htest).2 ⟨a, b, hidx0, hb, hsum⟩)))
        · exact Or.inr ⟨a, b, by omega, by omega, hb, hsum⟩

def nonEmptyD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, some true)
  | true, _ => (true, none)

theorem cpt_nonEmpty :
    ComputableInPolyTime (fun x : List Bool => x) PvsNP.encodeAnswer
      (fun l : List Bool => !l.isEmpty) := by
  refine fst_polyTime _ _ _ nonEmptyD (fun q => if q then none else some false) false ?_
  intro l
  have htrue : ∀ t : List Bool,
      fstRun nonEmptyD (fun q => if q then none else some false) true t = [] := by
    intro t; induction t with | nil => rfl | cons _ _ ih => simp [fstRun, nonEmptyD, ih]
  cases l with
  | nil => rfl
  | cons b t => simp [PvsNP.encodeAnswer, Computability.encodeBool, fstRun, nonEmptyD, htrue]

end PvsNP.Units.tl_lang_len_two_squares_p

/-- The strings whose length is a sum of two squares are in P (TM2). -/
theorem PvsNP.Units.tl_lang_len_two_squares_p :
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = x.length} : Language Bool) ∈ PvsNP.P := by
  have hInit : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x))) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB2
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.constList_polyTime [])
          PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id))
  have hcnt : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool =>
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU (true :: x) (true :: x)) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_mulU2
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_cons1 true
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_cons1 true
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id)
  have hIter := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_iterGrow
    PvsNP.Units.tl_lang_len_two_squares_p.cpt_tsStep 10
    PvsNP.Units.tl_lang_len_two_squares_p.tsStep_length
    hcnt hInit
  have hFnd := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hIter
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB1_1
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2_1
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB2))
  have hDec := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hFnd
    PvsNP.Units.tl_lang_len_two_squares_p.cpt_nonEmpty
  refine ⟨_, hDec, ?_⟩
  intro x
  change (∃ a b : ℕ, a ^ 2 + b ^ 2 = x.length) ↔
    (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.tl_lang_len_two_squares_p.tsStep^[(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU (true :: x) (true :: x)).length]
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x))))).2).2).1.isEmpty) = true
  have hcntlen : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU (true :: x) (true :: x)).length =
      (x.length + 1) ^ 2 := by
    rw [PvsNP.Units.tl_lang_len_two_squares_p.mulU_length_eq]
    simp [pow_two]
  rw [hcntlen]
  have hiff := PvsNP.Units.tl_lang_len_two_squares_p.tsStep_iter_iff ((x.length + 1) ^ 2) [] [] [] x
    (by simp) (Or.inl rfl)
  have hor := PvsNP.Units.tl_lang_len_two_squares_p.tsStep_iter_or ((x.length + 1) ^ 2) [] [] [] x
    (Or.inl rfl)
  simp only [List.length_nil, zero_mul, zero_add, Nat.zero_le, true_and] at hiff
  have hiff' : (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.tl_lang_len_two_squares_p.tsStep^[(x.length + 1) ^ 2]
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x))))).2).2).1 = [true] ↔
      ∃ a b : ℕ, a * (x.length + 1) + b < (x.length + 1) ^ 2 ∧
        b ≤ x.length ∧ a ^ 2 + b ^ 2 = x.length := by
    rw [hiff]
    constructor
    · rintro (h | ⟨a, b, h2, hb, hsum⟩)
      · exact absurd h (by simp)
      · exact ⟨a, b, h2, hb, hsum⟩
    · rintro ⟨a, b, h2, hb, hsum⟩
      exact Or.inr ⟨a, b, h2, hb, hsum⟩
  have hne : (!(PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.tl_lang_len_two_squares_p.tsStep^[(x.length + 1) ^ 2]
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x))))).2).2).1.isEmpty) = true ↔
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
        (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
            (PvsNP.Units.tl_lang_len_two_squares_p.tsStep^[(x.length + 1) ^ 2]
              (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
                (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB []
                  (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB [] x))))).2).2).1 = [true] := by
    rcases hor with h | h <;> rw [h] <;> simp
  rw [hne, hiff']
  constructor
  · rintro ⟨a, b, hsum⟩
    have ha2 : a ^ 2 ≤ x.length := by omega
    have hb2 : b ^ 2 ≤ x.length := by omega
    have ha : a ≤ x.length := by
      rcases Nat.eq_zero_or_pos a with rfl | ha'
      · omega
      · have hle : a ≤ a ^ 2 := by
          calc a = a * 1 := (Nat.mul_one a).symm
            _ ≤ a * a := Nat.mul_le_mul (le_refl a) ha'
            _ = a ^ 2 := (pow_two a).symm
        omega
    have hb : b ≤ x.length := by
      rcases Nat.eq_zero_or_pos b with rfl | hb'
      · omega
      · have hle : b ≤ b ^ 2 := by
          calc b = b * 1 := (Nat.mul_one b).symm
            _ ≤ b * b := Nat.mul_le_mul (le_refl b) hb'
            _ = b ^ 2 := (pow_two b).symm
        omega
    have hmul : a * (x.length + 1) ≤ x.length * (x.length + 1) :=
      Nat.mul_le_mul ha (le_refl _)
    have hsq2 : (x.length + 1) ^ 2 = x.length * (x.length + 1) + (x.length + 1) := by
      rw [pow_two]; ring
    refine ⟨a, b, ?_, hb, hsum⟩
    rw [hsq2]
    omega
  · rintro ⟨a, b, -, -, hsum⟩
    exact ⟨a, b, hsum⟩
