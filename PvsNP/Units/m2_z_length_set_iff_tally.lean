import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_div_const
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_inv_hom_closed
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_p_subset_np

namespace PvsNP.Units.m2_z_length_set_iff_tally

theorem eq_replicate_of_all_true : ∀ x : List Bool,
    (∀ b ∈ x, b = true) → x = List.replicate x.length true := by
  intro x
  induction x with
  | nil => intro _; rfl
  | cons b y ih =>
    intro h
    have hb : b = true := h b (by simp)
    have hy : ∀ c ∈ y, c = true := fun c hc => h c (List.mem_cons_of_mem b hc)
    rw [hb, ih hy]
    simp [List.replicate_succ]

end PvsNP.Units.m2_z_length_set_iff_tally

/-- The lists with length in a set `A` are in P (or NP) exactly when the tally
language of `A` is: the length language Karp-reduces to the tally language by
the unary-length map (settled unit `m2_tm_unary_div_const` at `k = 1`), so
downward closure (settled units `m2_p_down_closed`, `m2_np_down_closed`)
gives one direction; the tally language is the intersection of the length
language with the all-true lists, which are in P as the preimage of the
finite language `{[]}` (settled units `m2_p_finite`, `m2_inv_hom_closed`),
hence in NP (settled unit `m2_p_subset_np`), giving the other direction by
closure under intersection (settled units `m2_p_inter`, `m2_np_inter`). -/
theorem PvsNP.Units.m2_z_length_set_iff_tally :
    ∀ A : Set ℕ, (({x : List Bool | x.length ∈ A} : Language Bool) ∈ PvsNP.P ↔ ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.P) ∧
  (({x : List Bool | x.length ∈ A} : Language Bool) ∈ PvsNP.NP ↔ ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.NP) := by
  intro A
  have hlen : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) := by
    convert PvsNP.Units.m2_tm_unary_div_const 1 using 1
    funext x
    simp
  have hkarp : PvsNP.KarpReducible ({x : List Bool | x.length ∈ A} : Language Bool)
      ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) := by
    refine ⟨fun x => List.replicate x.length true, hlen, ?_⟩
    intro x
    constructor
    · intro hx
      exact ⟨x.length, hx, rfl⟩
    · rintro ⟨n, hn, hxn⟩
      show x.length ∈ A
      have hlenx : x.length = n := by
        have h := congrArg List.length hxn
        simpa using h
      rw [hlenx]
      exact hn
  have hE : ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite {[]}
  have hpre := (PvsNP.Units.m2_inv_hom_closed (fun b => if b then [] else [false])
    ({y : List Bool | y ∈ ({[]} : Finset (List Bool))} : Language Bool)).1 hE
  have hflat : ∀ x : List Bool, (∀ b ∈ x, b = true) ↔
      x.flatMap (fun b => if b then [] else [false]) = [] := by
    intro x
    induction x with
    | nil => simp
    | cons a x ih =>
      simp only [List.flatMap_cons, List.append_eq_nil_iff, List.forall_mem_cons]
      rw [ih]
      constructor
      · rintro ⟨rfl, hx⟩
        refine ⟨?_, hx⟩
        simp
      · rintro ⟨ha, hx⟩
        refine ⟨?_, hx⟩
        cases a with
        | true => rfl
        | false => simp at ha
  have hT : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.P := by
    convert hpre using 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_singleton]
    exact hflat x
  have hTNP : ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np hT
  have hS : ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool)
      = ({x : List Bool | x.length ∈ A} : Language Bool) ⊓
        ({x : List Bool | ∀ b ∈ x, b = true} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      constructor
      · simpa using hn
      · intro b hb
        exact List.eq_of_mem_replicate hb
    · rintro ⟨hxlen, hxall⟩
      exact ⟨x.length, hxlen,
        PvsNP.Units.m2_z_length_set_iff_tally.eq_replicate_of_all_true x hxall⟩
  constructor
  · constructor
    · intro h
      rw [hS]
      exact PvsNP.Units.m2_p_inter _ _ h hT
    · intro h
      exact PvsNP.Units.m2_p_down_closed _ _ hkarp h
  · constructor
    · intro h
      rw [hS]
      exact PvsNP.Units.m2_np_inter _ _ h hTNP
    · intro h
      exact PvsNP.Units.m2_np_down_closed _ _ hkarp h
