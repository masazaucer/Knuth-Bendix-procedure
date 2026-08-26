module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]


lemma lemma1 (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  ∀ r ∈ R, CheckOverlaps r R = [] := by
  intro r hr
  by_contra h_neq
  have h1 : List.flatMap (fun r ↦ CheckOverlaps r R) R ≠ [] := by
    have : ∃ R₁ R₂ : List (Rule A), R = R₁ ++ [r] ++ R₂ := by
      sorry
    obtain ⟨R₁, R₂, h_eq⟩ := this
    have : List.flatMap (fun r ↦ CheckOverlaps r R) R =
    List.flatMap (fun r ↦ CheckOverlaps r R) R₁ ++ List.flatMap (fun r ↦ CheckOverlaps r R) [r] ++
    List.flatMap (fun r ↦ CheckOverlaps r R) R₂ := by sorry
    rw [this]
    have : List.flatMap (fun r ↦ CheckOverlaps r R) [r] = CheckOverlaps r R := by
      simp
    rw [this]
    have : CheckOverlaps r R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R₂ ≠ [] := by
      exact List.append_ne_nil_of_left_ne_nil h_neq (List.flatMap (fun r ↦ CheckOverlaps r R) R₂)
    have := List.append_ne_nil_of_right_ne_nil (List.flatMap (fun r ↦ CheckOverlaps r R) R₁) this
    simp_all

  have h2 : List.length (List.flatMap (fun r ↦ CheckOverlaps r R) R) > 0 := by
    exact List.length_pos_of_ne_nil h1
  have h3 : List.length (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R) > List.length R := by
    rw [List.length_append]
    exact Nat.lt_add_of_pos_right h2
  have h4: List.length (SortRules (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R)) ≠ List.length R
    := by
    have (R' : List (Rule A)): List.length (SortRules R') = List.length R' := by
      unfold SortRules
      exact List.length_mergeSort R'
    rw [this]
    exact Nat.ne_of_lt' h3

  have h5: SortRules (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R) ≠ R := by
    exact Ne.symm fun a ↦ h4 (congrArg List.length h_fix)
  have : OneStepKnuthBendix R ≠ R := by
    unfold OneStepKnuthBendix
    exact h5
  contradiction


lemma lemma2 (r : Rule A) (R : List (Rule A)) (h : CheckOverlaps r R = []) :
  ∀ r' ∈ R, CheckOverlaps_rules r r' R = [] := by
  intro r' hr'
  by_contra h_neq
  sorry

lemma lemma3 (r₁ r₂ : Rule A) (R : List (Rule A)) (h : CheckOverlaps_rules r₁ r₂ R = []) :
  ∀ o : Overlap r₁.lhs r₂.lhs,
  Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = none := by sorry

lemma lemma4 (w u : Word A) (R : List (Rule A)) (h_test_eq_none : Test_for_rule w u R = none) :
  CanonicalReduction w R = CanonicalReduction u R := by sorry

lemma lemma5 (w : Word A) (R : List (Rule A)) : Reduction R w (CanonicalReduction w R) := by sorry

lemma locallyConfluent_of_fixpoint (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  LocallyConfluent R := by
  refine (localConfluence_and_Rules R).mpr ?_
  intro r₁ r₂ ⟨h₁, h₂⟩ o
  have h : CanonicalReduction (r₁.rhs ++ o.suffix₂) R = CanonicalReduction (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R := by
    refine lemma4 (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R ?_
    refine lemma3 r₁ r₂ R ?_ o
    refine lemma2 r₁ R ?_ r₂ h₂
    refine lemma1 R h_fix r₁ h₁
  use CanonicalReduction (r₁.rhs ++ o.suffix₂) R
  constructor
  · exact lemma5 (r₁.rhs ++ o.suffix₂) R
  · rw [h]
    exact lemma5 (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R


theorem KnuthBendixConfluent' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  refine (Confluent_iff_LocallyConfluent (KnuthBendix R)).mpr ?_
  refine locallyConfluent_of_fixpoint (KnuthBendix R) ?_
  exact KnuthBendixDomain_Fixpoint R h_dom

theorem KnuthBendix_Complete' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  exact (Confluent_iff_Complete (KnuthBendix R)).mp (KnuthBendixConfluent' R h_dom)
