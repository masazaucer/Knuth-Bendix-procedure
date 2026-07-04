module

public import KnuthBendix.KnuthBendix

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

--The order of the rules matters!
def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  let overlaps := FindOverlaps r.lhs r'.lhs
  ∀ o : Overlap A, o ∈ overlaps →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

def k_CompleteRules (k : Nat) (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap A, o ∈ FindOverlaps r.lhs r'.lhs →
  List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

lemma LocalConfluence_and_Rules (k : Nat) (R : List (Rule A)) :
  k_LocallyConfluent k R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → k_CompleteRules k r r' R := by
  constructor
  · intro h_LocConfluent r r' ⟨hr, hr'⟩
    unfold k_CompleteRules
    intro o ho h_len
    unfold k_LocallyConfluent at h_LocConfluent
    let w := o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂
    let v := r.rhs ++ o.suffix₂
    let u := o.prefix₁ ++ r'.rhs ++ o.suffix₁
    specialize h_LocConfluent w v u h_len
    have h_reduces_wv : OneStepReduction R w v := sorry
    have h_reduces_wu : OneStepReduction R w u := sorry
    specialize h_LocConfluent h_reduces_wv h_reduces_wu
    apply h_LocConfluent
  · intro h_complete_rules w v u h_len h_reduces_wv h_reduces_wu
    let ⟨r, r_mem, hr⟩ := rule_of_OneStepReduction R h_reduces_wv
    let ⟨r', r_mem', hr'⟩ := rule_of_OneStepReduction R h_reduces_wu
    specialize h_complete_rules r r' ⟨r_mem, r_mem'⟩
    unfold k_CompleteRules at h_complete_rules

    sorry

lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  sorry

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  sorry

lemma k_Complete_iff_kIrrSet_eq_succ (k : Nat) (R : List (Rule A)) :
  kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) → k_Complete k R := by
  sorry

/-
lemma k_Complete_iff_kIrrSet_eq (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ i : Nat, kIrrSet k R = kIrrSet k (OneStepKnuthBendix^[i] R) := by
  sorry
-/


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
    exact (k_Complete_iff_kIrrSet_eq_succ k (OneStepKnuthBendix^[j] R)) hj
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
  refine Complete_of_k_Complete (KnuthBendix R) ?_
  intro k
  have ⟨m, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  have k_complete := k_Completeness R
  specialize k_complete k
  obtain ⟨n, hn⟩ := k_complete
  rw [h_eq]
  by_cases h_n_leq_m : n ≤ m
  specialize hn m h_n_leq_m
  exact hn.1
  have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
    specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
    exact Eq.symm h_pow
  rw [h_En_eq_Em]
  specialize hn n (Nat.le_refl n)
  exact hn.1


theorem ResiduesCoincide (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∀ w : Word A, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  Reduce w (KnuthBendix R) = Reduce w (OneStepKnuthBendix^[i] R) := by
  intro w
  have ⟨m, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  rw [h_eq]
  have ⟨n, hn⟩ := k_Completeness R w.length
  use n
  intro i h_i_geq_n
  by_cases h_n_leq_m : n ≤ m
  have h1 : Reduce w (OneStepKnuthBendix^[m] R) = Reduce w (OneStepKnuthBendix^[n] R) := by
    specialize hn m h_n_leq_m
    have h : ∀ (v : Word A),
    List.length v ≤ List.length w →
    Reduce v (OneStepKnuthBendix^[m] R) = Reduce v (OneStepKnuthBendix^[n] R) :=
    hn.2
    specialize h w (by exact Nat.le_refl (List.length w))
    exact h
  have h2 : Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R) := by
    specialize hn i h_i_geq_n
    have h : ∀ (v : Word A),
    List.length v ≤ List.length w →
    Reduce v (OneStepKnuthBendix^[i] R) = Reduce v (OneStepKnuthBendix^[n] R) :=
    hn.2
    specialize h w (by exact Nat.le_refl (List.length w))
    exact h
  rw [h1]
  exact Eq.symm h2
  have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
    specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
    exact Eq.symm h_pow
  rw [h_En_eq_Em]
  specialize hn i h_i_geq_n
  obtain ⟨h1, h2⟩ := hn
  specialize h2 w (by exact Nat.le_refl (List.length w))
  exact Eq.symm h2


theorem KnuthBendix_confluent (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  exact (Confluent_iff_Complete (KnuthBendix R)).mpr (KnuthBendix_Complete R h_dom)
