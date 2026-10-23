module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]
variable {R : List (Rule A)} {r r₁ r₂ : Rule A} {o : Overlap r₁.lhs r₂.lhs}

/-
lemma lemma1 (h_fix : OneStepKnuthBendix R = R) :
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


lemma lemma2 (h : CheckOverlaps r R = []) :
  ∀ r' ∈ R, CheckOverlaps_rules r r' R = [] := by
  intro r' hr'
  by_contra h_neq
  sorry

lemma lemma3 (h : CheckOverlaps_rules r₁ r₂ R = []) :
  ∀ o : Overlap r₁.lhs r₂.lhs,
  Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = none := by sorry

lemma lemma6 : OneStepKnuthBendix R = R ↔
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ o : Overlap r₁.lhs r₂.lhs,
      Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = some r := by sorry
-/


lemma lemma4 {w u : Word A} (h_test_eq_none : Test_for_rule w u R = none) :
    CanonicalReduction R w = CanonicalReduction R u := by
  by_contra h_neq
  unfold Test_for_rule at h_test_eq_none
  simp_all

lemma Test_for_rule_none_of_OSKB_eq (h : OneStepKnuthBendix R = R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ o : Overlap r₁.lhs r₂.lhs,
      Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = none := by
  intro r₁ h₁ r₂ h₂ o
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro r
  by_contra hr
  have h_neq : OneStepKnuthBendix R ≠ R := by
    have : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r := by
      rw [← hr]
      exact Test_for_rule_symm
    refine OSKB_neq_of_Test_for_rule_some h₁ h₂ this
  contradiction


lemma locallyConfluent_of_fixpoint (h_fix : OneStepKnuthBendix R = R) : LocallyConfluent R := by
  refine localConfluence_and_Rules.mpr ?_
  intro r₁ h₁ r₂ h₂ o
  have h : CanonicalReduction R (r₁.rhs ++ o.suffix₂) =
      CanonicalReduction R (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) := by
    refine lemma4 ?_
    exact Test_for_rule_none_of_OSKB_eq h_fix r₁ h₁ r₂ h₂ o
  use CanonicalReduction R (r₁.rhs ++ o.suffix₂)
  constructor
  · exact reduces_to_CanonicalReduction
  · rw [h]
    exact reduces_to_CanonicalReduction


theorem KnuthBendixConfluent' (h_dom : KnuthBendix_dom R) : Confluent (KnuthBendix R) := by
  refine Confluent_iff_LocallyConfluent.mpr ?_
  refine locallyConfluent_of_fixpoint ?_
  exact KnuthBendixDomain_Fixpoint h_dom

theorem KnuthBendix_Complete' (h_dom : KnuthBendix_dom R) : Complete (KnuthBendix R) := by
  exact Confluent_iff_Complete.mp (KnuthBendixConfluent' h_dom)
