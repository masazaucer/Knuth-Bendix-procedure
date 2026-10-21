module

public import KnuthBendix.KnuthBendixDomain
public import KnuthBendix.KnuthBendixLemmas
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.List.Basic


variable {A : Type} [Finite A] [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

--#check Test_for_rule_symm
-- If kIrrSet does not chenge with applying OneStepKnuthBendix then the set of rules is kComplete
-- TODO: check if we need ReductionOrderLen
-- TODO: break into lemmas?
lemma k_Complete_of_kIrrSet_eq_succ [ReductionOrderLen A] (k : Nat) (R : List (Rule A)) :
  kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) → k_Complete k R := by
  intro h_eq
  refine (k_Confluent_iff_k_Complete).mp ?_
  refine (k_Confluent_iff_k_LocallyConfluent).mpr ?_
  refine (kLocalConfluence_and_Rules k R).mpr ?_
  intro r₁ r₁_mem r₂ r₂_mem o h_len
  let u : Word A := r₁.rhs ++ o.suffix₂
  let v : Word A := o.prefix₁ ++ r₂.rhs ++ o.suffix₁
  by_contra h_notRelationJoin
  have CR_neq : CanonicalReduction u R ≠ CanonicalReduction v R :=
    CanonicalReduction_neq_of_notRelationJoin h_notRelationJoin
  let r : Rule A := MakeRule (CanonicalReduction u R) (CanonicalReduction v R) CR_neq
  have h_Test_for_rule : Test_for_rule u v R = some r := by
    unfold Test_for_rule
    simp [r]
    exact CR_neq
  have h_mem : r ∈ OneStepKnuthBendix R := by
    refine mem_OSKB_of_mem_CheckOverlaps r₁ r R r₁_mem ?_
    refine mem_CheckOverlaps_of_mem_CheckOverlaps_rules r₂_mem ?_
    refine mem_CheckOverlaps_rules_of_Test_for_rule_some r r₁ r₂ R o ?_
    rw [(Test_for_rule_symm (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R), h_Test_for_rule]
  have h_len_rlhs : (r.lhs).length ≤ k := by
    have h_max : r.lhs = max (CanonicalReduction u R) (CanonicalReduction v R) := by
      unfold r
      trivial
    have CRu_len : (CanonicalReduction u R).length ≤ k := by
      have : (CanonicalReduction u R).length ≤ u.length := by
        apply ReductionOrderLen.cwl
        exact CanonicalReduction_leq u R
      have u_len_leq : u.length ≤ k := by
        have : u.length ≤ (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂).length := by
          apply OneStepReduction_len_leq
          exact overlap_reduces R r₁  r₂ o r₁_mem
        exact Nat.le_trans this h_len
      exact Nat.le_trans this u_len_leq
    have CRv_len : (CanonicalReduction v R).length ≤ k := by
      have : (CanonicalReduction v R).length ≤ v.length := by
        apply ReductionOrderLen.cwl
        exact CanonicalReduction_leq v R
      have u_len_leq : v.length ≤ k := by
        have : v.length ≤ (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂).length := by
          apply OneStepReduction_len_leq
          exact overlap_reduces' R r₁  r₂ o r₂_mem
        exact Nat.le_trans this h_len
      exact Nat.le_trans this u_len_leq
    grind
  have h_mem_kIrrR : r.lhs ∈ kIrrSet k R := by
    have : r.lhs = max (CanonicalReduction u R) (CanonicalReduction v R) := by
      unfold r
      unfold MakeRule
      simp
    have : (r.lhs = CanonicalReduction u R) ∨ (r.lhs = CanonicalReduction v R) := by
      rw [this]
      simp only [sup_eq_left, sup_eq_right]
      exact Std.IsLinearOrder.le_total (CanonicalReduction v R) (CanonicalReduction u R)
    cases this with
    | inl h =>
      have : r.lhs ∈ IrrSet R := by rw [h]; exact CR_Irreducible u R
      rw [kIrrSet_mem]
      exact ⟨h_len_rlhs, this⟩
    | inr h =>
      have : r.lhs ∈ IrrSet R := by rw [h]; exact CR_Irreducible v R
      rw [kIrrSet_mem]
      exact ⟨h_len_rlhs, this⟩
  have h_not_mem_kIrrOSKBR : r.lhs ∉ kIrrSet k (OneStepKnuthBendix R) := by
    have : r.lhs ∉ IrrSet (OneStepKnuthBendix R) := LHS_Reducible r (OneStepKnuthBendix R) h_mem
    have h_subset : ↑(kIrrSet k (OneStepKnuthBendix R)) ⊆ IrrSet (OneStepKnuthBendix R) := by
      exact kIrrSet_sub_IrrSet k (OneStepKnuthBendix R)
    exact (Set.mem_compl_iff (kIrrSet k (OneStepKnuthBendix R)) r.lhs).mp fun a ↦ this (h_subset a)
  simp_all




lemma kIrrSet_stabilizes [Finite A] (k : Nat) (R : List (Rule A)) : ∃ n : Nat, ∀ i : Nat, i ≥ n →
    kIrrSet k (OneStepKnuthBendix^[i] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := by
  let S := {(kIrrSet k (OneStepKnuthBendix^[j] R))| j : Nat}
  have H : WellFounded (fun x y : Finset (Word A) ↦ x ⊂ y) := by
    exact IsWellFounded.wf
  have h_nonempty : S.Nonempty := by
    refine Set.nonempty_def.mpr ?_
    use kIrrSet k (OneStepKnuthBendix^[0] R)
    grind
  let Sₙ : Finset (Word A) := WellFounded.min H S h_nonempty
  have h_mem : Sₙ ∈ S := by exact WellFounded.min_mem H S h_nonempty
  obtain ⟨n, hn⟩ := h_mem
  use n
  intro i i_geq_n
  have h_sub : kIrrSet k (OneStepKnuthBendix^[i] R) ⊆ kIrrSet k (OneStepKnuthBendix^[n] R) := by
    exact kIrrSet_OSKB_sub_of_leq R k n i i_geq_n
  have h_mem : kIrrSet k (OneStepKnuthBendix^[i] R) ∈ S := by
    refine Set.mem_setOf.mpr ?_
    use i
  have : ¬kIrrSet k (OneStepKnuthBendix^[i] R) ⊂ Sₙ := WellFounded.not_lt_min H S h_mem
  grind


lemma k_ResiduesCoincide [ReductionOrderLen A] (k : Nat) (R R' : List (Rule A))
  (hR' : k_Complete k R') (h_irr_eq : kIrrSet k R = kIrrSet k R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → CanonicalReduction w R = CanonicalReduction w R' := by
  intro w h_len
  have h_reduces : Reduction R' w (CanonicalReduction w R) := by
    apply Reduction_of_Reduction_sub h_sub
    exact reduces_to_CanonicalReduction w R
  have h_irr : Irreducible R' (CanonicalReduction w R) := by
    have : (CanonicalReduction w R) ∈ kIrrSet k R := by
      have h_len : (CanonicalReduction w R).length ≤ k := by
        have : (CanonicalReduction w R).length ≤ w.length := by
          apply ReductionOrderLen.cwl
          exact CanonicalReduction_leq w R
        exact Nat.le_trans this h_len
      have h_irr : Irreducible R (CanonicalReduction w R) := by
        have : _ := CR_Irreducible w R
        unfold IrrSet at this
        simp_all
      rw [kIrrSet_mem]
      exact ⟨h_len, h_irr⟩
    rw [h_irr_eq] at this
    unfold kIrrSet at this
    simp_all
  exact CR_of_Reduction_Irr_kComplete hR' h_len h_reduces h_irr

variable [ReductionOrderLen A]

lemma k_Completeness (R : List (Rule A)) :
  ∀ k : Nat, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  k_Complete k (OneStepKnuthBendix^[i] R) ∧
  (∀ w : Word A, w.length ≤ k →
  CanonicalReduction w (OneStepKnuthBendix^[i] R) = CanonicalReduction w (OneStepKnuthBendix^[n] R)) :=
  by
  intro k
  obtain ⟨n, h⟩ := kIrrSet_stabilizes k R
  use n
  intro i i_ge_n
  have k_complete : ∀ j : Nat, j ≥ n → k_Complete k (OneStepKnuthBendix^[j] R) := by
    intro j j_ge_n
    have hj : kIrrSet k (OneStepKnuthBendix^[j] R) = kIrrSet k (OneStepKnuthBendix^[n] R) :=
      h j j_ge_n
    have hj_succ : kIrrSet k (OneStepKnuthBendix^[j + 1] R) = kIrrSet k (OneStepKnuthBendix^[n] R)
      := h (j + 1) (Nat.le_add_right_of_le j_ge_n)
    rw [Eq.symm hj_succ] at hj
    have h_succ : OneStepKnuthBendix^[j + 1] R = OneStepKnuthBendix (OneStepKnuthBendix^[j] R) :=
      OneStepKnuthBendix_eq_NatIterate R j
    rw [h_succ] at hj
    exact (k_Complete_of_kIrrSet_eq_succ k (OneStepKnuthBendix^[j] R)) hj
  have residues_coincide : ∀ w : Word A, w.length ≤ k →
  CanonicalReduction w (OneStepKnuthBendix^[i] R) = CanonicalReduction w (OneStepKnuthBendix^[n] R) :=
  by
    intro w w_le_k
    apply Eq.symm
    refine k_ResiduesCoincide k
      (OneStepKnuthBendix^[n] R) (OneStepKnuthBendix^[i] R) ?_ ?_ ?_ w w_le_k
    · exact k_complete i i_ge_n
    · exact Eq.symm (h i i_ge_n)
    · exact OneStepKnuthBendix_sub_of_leq R n i i_ge_n
  exact ⟨k_complete i i_ge_n, residues_coincide⟩



--- MAIN THEOREM: Knuth-Bendix algorithm produces a complete rewriting system (if it terminates)
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
  · specialize hn m h_n_leq_m
    exact hn.1
  · have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
      specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
      exact Eq.symm h_pow
    rw [h_En_eq_Em]
    specialize hn n (Nat.le_refl n)
    exact hn.1


theorem ResiduesCoincide (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∀ w : Word A, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  CanonicalReduction w (KnuthBendix R) = CanonicalReduction w (OneStepKnuthBendix^[i] R) := by
  intro w
  have ⟨m, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  rw [h_eq]
  have ⟨n, hn⟩ := k_Completeness R w.length
  use n
  intro i h_i_geq_n
  by_cases h_n_leq_m : n ≤ m
  · have h1 : CanonicalReduction w (OneStepKnuthBendix^[m] R) = CanonicalReduction w (OneStepKnuthBendix^[n] R)
    := by
      specialize hn m h_n_leq_m
      have h : ∀ (v : Word A),
      List.length v ≤ List.length w →
      CanonicalReduction v (OneStepKnuthBendix^[m] R) = CanonicalReduction v (OneStepKnuthBendix^[n] R) :=
      hn.2
      specialize h w (by exact Nat.le_refl (List.length w))
      exact h
    have h2 : CanonicalReduction w (OneStepKnuthBendix^[i] R) = CanonicalReduction w (OneStepKnuthBendix^[n] R)
    := by
      specialize hn i h_i_geq_n
      have h : ∀ (v : Word A),
      List.length v ≤ List.length w →
      CanonicalReduction v (OneStepKnuthBendix^[i] R) = CanonicalReduction v (OneStepKnuthBendix^[n] R) :=
      hn.2
      specialize h w (by exact Nat.le_refl (List.length w))
      exact h
    rw [h1]
    exact Eq.symm h2
  · have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
      specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
      exact Eq.symm h_pow
    rw [h_En_eq_Em]
    specialize hn i h_i_geq_n
    obtain ⟨h1, h2⟩ := hn
    specialize h2 w (by exact Nat.le_refl (List.length w))
    exact Eq.symm h2


theorem KnuthBendix_confluent (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  exact (Confluent_iff_Complete).mpr (KnuthBendix_Complete R h_dom)
