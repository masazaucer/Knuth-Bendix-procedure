module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.List.Basic

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]


lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  exact IrrSet_sub_of_sub R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  exact kIrrSet_sub_of_sub k R (OneStepKnuthBendix R) (R_sub_OneStepKB R)


lemma Test_for_rule_symm (u v : Word A) (R : List (Rule A)) : Test_for_rule u v R = Test_for_rule v u R := by sorry
/-
lemma Test_for_rule_Irreducible {u v : Word A} {r : Rule A} {R : List (Rule A)} (h : Test_for_rule u v R = some r) : r.lhs ∈ IrrSet R ∧ r.rhs ∈ IrrSet R := by sorry
-/

lemma CanonicalReduction_neq_of_notRelationJoin {u v : Word A} {R : List (Rule A)} (h_notRelationJoin : ¬Relation.Join (Reduction R) u v) : CanonicalReduction u R ≠ CanonicalReduction v R := by
  by_contra h_eq
  let t : Word A := CanonicalReduction u R
  have h_reduces_ut : Reduction R u t := by exact reduces_to_CanonicalReduction u R
  have h_reduces_vt : Reduction R v t := by
    unfold t; rw [h_eq];
    exact reduces_to_CanonicalReduction v R
  have : Relation.Join (Reduction R) u v := by use t
  trivial


lemma Overlaps_mem_FindOverlaps {u v : Word A} (o : Overlap u v) (hv : v ≠ []) : o ∈ FindOverlaps u v hv:= by
  sorry

--maybe add result that r.lhs = max(CR u, CR v) and r.rhs = min(CR u, CR v)
lemma TestForRule_some_of_CanonicalReduction_neq {u v : Word A} {R : List (Rule A)} (h_neq : CanonicalReduction u R ≠ CanonicalReduction v R) : Test_for_rule u v R = some r := by sorry

lemma lemma_1 (r r₁ r₂ : Rule A) (R : List (Rule A)) (o : Overlap r₁.lhs r₂.lhs) (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) : r ∈ CheckOverlaps_rules r₁ r₂ R := by sorry

lemma lemma_2 (r r₁ r₂ : Rule A) (R : List (Rule A)) (h : r ∈ CheckOverlaps_rules r₁ r₂ R) : r ∈ CheckOverlaps r₁ R := by sorry

lemma lemma_3 (r r' : Rule A) (R : List (Rule A)) (h : r' ∈ CheckOverlaps r R) : r' ∈ OneStepKnuthBendix R := by sorry


lemma k_Complete_of_kIrrSet_eq_succ (k : Nat) (R : List (Rule A)) :
  kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) → k_Complete k R := by
  intro h_eq
  refine (k_Confluent_iff_k_Complete k R).mp ?_
  refine (k_Confluent_iff_k_LocallyConfluent k R).mpr ?_
  refine (kLocalConfluence_and_Rules k R).mpr ?_
  intro r₁ r₂ ⟨r₁_mem, r₂_mem⟩ o h_len
  let u : Word A := r₁.rhs ++ o.suffix₂
  let v : Word A := o.prefix₁ ++ r₂.rhs ++ o.suffix₁
  by_contra h_notRelationJoin
  have CR_neq : CanonicalReduction u R ≠ CanonicalReduction v R :=
    CanonicalReduction_neq_of_notRelationJoin h_notRelationJoin
  let r : Rule A := MakeRule (CanonicalReduction u R) (CanonicalReduction v R) CR_neq
  have h_Test_for_rule : Test_for_rule u v R = some r := by sorry
  have h_mem : r ∈ OneStepKnuthBendix R := by
    refine lemma_3 r₁ r R ?_
    refine lemma_2 r r₁ r₂ R ?_
    refine lemma_1 r r₁ r₂ R o ?_
    rw [(Test_for_rule_symm (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R), h_Test_for_rule]
  have h_len_rlhs : (r.lhs).length ≤ k := by sorry
  have h_mem_kIrrR : r.lhs ∈ kIrrSet k R := by
    have : r.lhs = min (CanonicalReduction u R) (CanonicalReduction v R) := by sorry
    have : r.lhs = CanonicalReduction u R ∨ r.lhs = CanonicalReduction v R := by sorry
    cases this with
    | inl h =>
      have : r.lhs ∈ IrrSet R := by rw [h]; exact CanonicalReductionIrreducible u R
      exact ⟨h_len_rlhs, this⟩
    | inr h =>
      have : r.lhs ∈ IrrSet R := by rw [h]; exact CanonicalReductionIrreducible v R
      exact ⟨h_len_rlhs, this⟩
  have h_not_mem_kIrrOSKBR : ¬r.lhs ∈ kIrrSet k (OneStepKnuthBendix R) := by
    have : r.lhs ∉ IrrSet (OneStepKnuthBendix R) := LHS_Reducible r (OneStepKnuthBendix R) h_mem
    sorry
  simp_all

lemma kIrrSet_fin (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by sorry
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}


lemma kIrrSet_stabilizes (k : Nat) (R : List (Rule A)) : ∃ n : Nat, ∀ i : Nat, i ≥ n →
  kIrrSet k (OneStepKnuthBendix^[i] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := by
    sorry


lemma k_ResiduesCoincide (k : Nat) (R R' : List (Rule A))
  (hR : k_Complete k R) (hR' : k_Complete k R')
  (h_irr : kIrrSet k R = kIrrSet k R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → CanonicalReduction w R = CanonicalReduction w R' := by sorry

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
      (OneStepKnuthBendix^[n] R) (OneStepKnuthBendix^[i] R) ?_ ?_ ?_ ?_ w w_le_k
    · exact k_complete n (Nat.le_refl n)
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
  exact (Confluent_iff_Complete (KnuthBendix R)).mpr (KnuthBendix_Complete R h_dom)
