module

public import Mathlib.Data.List.Shortlex
public import KnuthBendix.KnuthBendix

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]


--TERMINATION CONDITION

-- R is in the domain of KnuthBendix if after some number of iterations we get a fixpoint (i.e. no new rules are added)
def KnuthBendix_dom (R : List (Rule A)) : Prop :=
  ∃ n : Nat, (OneStepKnuthBendix^[n] R) = (OneStepKnuthBendix^[n + 1] R) ∧ (∀ i < n, (OneStepKnuthBendix^[i] R) ≠ (OneStepKnuthBendix^[i + 1] R))


--LEMMAS ABOUT KNUTH-BENDIX DOMAIN

lemma OSKB_fixpoint_of_succ_eq {n} (R : List (Rule A)) (h_succ_eq : (OneStepKnuthBendix^[n] R) = (OneStepKnuthBendix^[n + 1] R)) : ∀ i ≥ n,
  (OneStepKnuthBendix^[i] R) = (OneStepKnuthBendix^[n] R) := by
  have h (j : Nat) : (OneStepKnuthBendix^[n + j] R) = (OneStepKnuthBendix^[n] R) := by
    induction j with
    | zero => trivial
    | succ j ih =>
    have : n + (j + 1) = (n + j) + 1 := by grind
    rw [this, OneStepKnuthBendix_eq_NatIterate, ih, ←OneStepKnuthBendix_eq_NatIterate, h_succ_eq]
  intro i i_ge_n
  specialize h (i - n)
  simp_all

-- if R is in the domain of KnuthBendix then from some n on iterating OneStepKnuthBendix returns does nothing
lemma KnuthBendix_dom_fixpoint (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, ∀ i : Nat, i ≥ n →
  (OneStepKnuthBendix^[i] R) = (OneStepKnuthBendix^[n] R) := by
  obtain ⟨n, h⟩ := h_dom
  use n
  exact OSKB_fixpoint_of_succ_eq R h.1

lemma KnuthBendixDomain (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, KnuthBendix R = (OneStepKnuthBendix^[n] R)
  ∧ (∀ i ≥ n, (OneStepKnuthBendix^[i] R) = (OneStepKnuthBendix^[n] R))
  := by
  obtain ⟨n, hn⟩ := h_dom
  use n
  have h1 : ∀ i < n, KnuthBendix (OneStepKnuthBendix^[i] R) = KnuthBendix (OneStepKnuthBendix^[i + 1] R)
  := by
    intro i i_lt_n
    have hi : OneStepKnuthBendix^[i] R ≠ OneStepKnuthBendix^[i + 1] R := hn.2 i i_lt_n
    rw [KnuthBendix]
    rw [←OneStepKnuthBendix_eq_NatIterate]
    have : OneStepKnuthBendix^[i + 1] R ≠ OneStepKnuthBendix^[i] R := by exact Ne.symm hi
    simp_all
  have h2 : KnuthBendix (OneStepKnuthBendix^[n] R) = (OneStepKnuthBendix^[n] R) := by
    rw [KnuthBendix]
    rw [←OneStepKnuthBendix_eq_NatIterate]
    simp_all
  have h3 : KnuthBendix R = KnuthBendix (OneStepKnuthBendix^[n] R) := by
    match n with
    | 0 => trivial
    | n + 1 =>
    have : R = OneStepKnuthBendix^[0] R := by simp
    have h4 (j : Nat) : j < n + 1 → KnuthBendix (OneStepKnuthBendix^[j] R) = KnuthBendix (OneStepKnuthBendix^[0] R)
    := by
      induction j with
      | zero => intro h; simp
      | succ j ih =>
      intro hj
      specialize h1 j (Nat.lt_of_succ_lt hj)
      rw [← h1]
      exact ih (Nat.lt_of_succ_lt hj)
    have h5 : KnuthBendix (OneStepKnuthBendix^[0] R) = KnuthBendix (OneStepKnuthBendix^[n + 1] R) := by
      specialize h1 n (lt_add_one n)
      specialize h4 n (lt_add_one n)
      rw [←h4, h1]
    exact h5
  constructor
  · rw [h3, h2]
  · exact OSKB_fixpoint_of_succ_eq R hn.1

lemma KnuthBendixDomain_Fixpoint (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  OneStepKnuthBendix (KnuthBendix R) = KnuthBendix R := by
  obtain ⟨n, ⟨h_eq, hi⟩⟩ := KnuthBendixDomain R h_dom
  rw [h_eq]
  rw [←OneStepKnuthBendix_eq_NatIterate]
  exact hi (n + 1) (by exact Nat.le_add_right n 1)


lemma Ei_sub_KB (R : List (Rule A)) (i : Nat) (h_dom : KnuthBendix_dom R) :
  OneStepKnuthBendix^[i] R ⊆ KnuthBendix R := by
  obtain ⟨n, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  rw [h_eq]
  by_cases h_i_leq_n : i ≤ n
  · exact OneStepKnuthBendix_sub_of_leq R i n h_i_leq_n
  · specialize h_pow i (Nat.le_of_not_le h_i_leq_n)
    exact subset_of_subset_of_eq (fun ⦃a⦄ a_1 ↦ a_1) h_pow
