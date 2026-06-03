module

public import KnuthBendix.KnuthBendix

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

lemma k_Completeness (R : List (Rule A)) :
  ∀ k : Nat, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  k_Complete k (Nat.iterate OneStepKnuthBendix i R) ∧
  (∀ w : Word A, w.length ≤ k →
  Reduce w (Nat.iterate OneStepKnuthBendix i R) = Reduce w (Nat.iterate OneStepKnuthBendix n R)) :=
  by sorry

lemma k_ResiduesCoincide (k : Nat) (R R' : List (Rule A))
  (hR : k_Complete k R) (hR' : k_Complete k R')
  (h_irr : IrrSet R = IrrSet R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → Reduce w R = Reduce w R' := by sorry

def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  CheckOverlaps r r' R = []

lemma Completeness_and_Rules (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → CompleteRules r r' R := by
  sorry

lemma k_Complete_iff_kIrrSet_eq (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) := by
  sorry

lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  sorry

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  sorry



--- MAIN THEOREM: Knuth-Bendix algorithm produces a complete rwriting system (if it terminates)
theorem KnuthBendix_Complete (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  sorry

theorem ResiduesCoincide (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∀ w : Word A, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  Reduce w (KnuthBendix R) = Reduce w (Nat.iterate OneStepKnuthBendix i R) := by
  sorry

theorem KnuthBendix_confluent
  (R : List (Rule A))
  (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by sorry
