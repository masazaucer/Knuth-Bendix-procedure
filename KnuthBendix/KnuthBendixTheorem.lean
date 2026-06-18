module

public import KnuthBendix.KnuthBendix

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  let overlaps := FindOverlaps r.lhs r'.lhs
  ∀ o : Overlap A, o ∈ overlaps →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

def k_CompleteRules (k : Nat) (r r' : Rule A) (R : List (Rule A)) : Prop :=
  let overlaps := FindOverlaps r.lhs r'.lhs
  ∀ o : Overlap A, o ∈ overlaps →
  List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

lemma Completeness_and_Rules (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → k_CompleteRules k r r' R := by
  sorry

lemma k_Complete_iff_kIrrSet_eq_succ (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) := by
  constructor
  · intro h_complete
    sorry
  · intro h_eq
    sorry

lemma k_Complete_iff_kIrrSet_eq (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ i : Nat, kIrrSet k R = kIrrSet k (OneStepKnuthBendix^[i] R) := by
  sorry

lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by

  sorry

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  sorry

lemma kIrrSet_stabilizes (k : Nat) (R : List (Rule A)) : ∃ n : Nat, ∀ i : Nat, i ≥ n → kIrrSet k (OneStepKnuthBendix^[i] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := by sorry


lemma k_ResiduesCoincide (k : Nat) (R R' : List (Rule A))
  (hR : k_Complete k R) (hR' : k_Complete k R')
  (h_irr : kIrrSet k R = kIrrSet k R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → Reduce w R = Reduce w R' := by sorry

lemma k_Completeness (R : List (Rule A)) :
  ∀ k : Nat, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  k_Complete k (OneStepKnuthBendix^[i] R) ∧
  (∀ w : Word A, w.length ≤ k →
  Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R)) :=
  by
  intro k
  obtain ⟨n, h⟩ := kIrrSet_stabilizes k R
  use n
  intro i i_ge_n
  have k_complete : ∀ j : Nat, j ≥ n → k_Complete k (OneStepKnuthBendix^[j] R) := by
    intro j j_ge_n
    have hj : kIrrSet k (OneStepKnuthBendix^[j] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := h j j_ge_n
    have hj_succ : kIrrSet k (OneStepKnuthBendix^[j + 1] R) = kIrrSet k (OneStepKnuthBendix^[n] R) :=
    h (j + 1) (Nat.le_add_right_of_le j_ge_n)
    rw [Eq.symm hj_succ] at hj
    have h_succ : OneStepKnuthBendix^[j + 1] R = OneStepKnuthBendix (OneStepKnuthBendix^[j] R) := OneStepKnuthBendix_eq_NatIterate R j
    rw [h_succ] at hj
    exact (k_Complete_iff_kIrrSet_eq_succ k (OneStepKnuthBendix^[j] R)).mpr hj
  have residues_coincide : ∀ w : Word A, w.length ≤ k →
  Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R) :=
  by
    intro w w_le_k
    apply Eq.symm
    refine k_ResiduesCoincide k (OneStepKnuthBendix^[n] R) (OneStepKnuthBendix^[i] R) ?_ ?_ ?_ ?_ w w_le_k
    · exact k_complete n (Nat.le_refl n)
    · exact k_complete i i_ge_n
    · exact Eq.symm (h i i_ge_n)
    · exact OneStepKnuthBendix_sub_of_leq R n i i_ge_n
  exact ⟨k_complete i i_ge_n, residues_coincide⟩




--- MAIN THEOREM: Knuth-Bendix algorithm produces a complete rwriting system (if it terminates)
theorem KnuthBendix_Complete (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  sorry

theorem ResiduesCoincide (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∀ w : Word A, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  Reduce w (KnuthBendix R) = Reduce w (OneStepKnuthBendix^[i] R) := by
  sorry

theorem KnuthBendix_confluent (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by sorry
