module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

--The order of the rules matters!
def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap A r.lhs r'.lhs,
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

def k_CompleteRules (k : Nat) (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap A r.lhs r'.lhs,
  List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

lemma words_from_overlap (u v : Word A) (o : Overlap A u v) :
  u = o.prefix₁ ++ o.overlap ++ o.suffix₁ ∧ v = o.overlap ++ o.suffix₂ := by

  sorry

lemma overlap_reduces (R : List (Rule A)) (r r' : Rule A) (o : Overlap A r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (r.rhs ++ o.suffix₂) := by
  have hr'_lhs: r'.lhs = o.overlap ++ o.suffix₂ := by
    exact (words_from_overlap r.lhs r'.lhs o).2
  have hr_lhs: r.lhs = o.prefix₁ ++ o.overlap ++ o.suffix₁ := by
    exact (words_from_overlap r.lhs r'.lhs o).1
  cases o.empty with
  |inl suf₁_empty =>
  rw [suf₁_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ []) r.rhs := by
    rw [←suf₁_empty, ←hr_lhs]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ [] ++ o.suffix₂) (r.rhs ++ o.suffix₂) := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ []) r.rhs [] o.suffix₂ this
  simp_all
  exact this
  |inr suf₂_empty =>
  rw [suf₂_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs := by
    rw [← hr_lhs]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ []) (r.rhs ++ []) := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs [] [] this
  simp_all
  exact this

lemma overlap_reduces'  (R : List (Rule A)) (r r' : Rule A) (o : Overlap A r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁) := by
  have hr'_lhs: r'.lhs = o.overlap ++ o.suffix₂ := by
    exact (words_from_overlap r.lhs r'.lhs o).2
  have hr_lhs: r.lhs = o.prefix₁ ++ o.overlap ++ o.suffix₁ := by
    exact (words_from_overlap r.lhs r'.lhs o).1
  cases o.empty with
    | inl v2_empty =>
      rw [v2_empty]
      have : SimpleReduction R (o.overlap ++ o.suffix₂) r'.rhs := by
        rw [←hr'_lhs]
        exact SimpleReduction.mk r' h_mem.2
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ (o.overlap ++ o.suffix₂) ++ []) (o.prefix₁ ++ r'.rhs ++ []) :=
        CongruenceClosure.mk (o.overlap ++ o.suffix₂) r'.rhs o.prefix₁ [] this
      simp_all
      exact this
    | inr u2_empty =>
      rw [u2_empty]
      have : SimpleReduction R o.overlap r'.rhs := by
        have : o.overlap ++ [] = r'.lhs := by
          rw [←u2_empty, ←hr'_lhs]
        simp at this
        rw [this]
        exact SimpleReduction.mk r' h_mem.2
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ o.overlap ++ o.suffix₁) (o.prefix₁ ++ r'.rhs ++ o.suffix₁) :=
        CongruenceClosure.mk o.overlap r'.rhs o.prefix₁ o.suffix₁ this
      simp_all
      exact this

lemma IsInfix_Reduces (R : List (Rule A)) (r : Rule A) (w u : Word A) (r_mem : r ∈ R) :
  (∃ u₁ u₂ : Word A, w = u₁ ++ r.lhs ++ u₂ ∧ u = u₁ ++ r.rhs ++ u₂) → Reduction R w u := by
  intro ⟨u₁, u₂, ⟨h_eq1, h_eq2⟩⟩
  refine Relation.ReflTransGen.single ?_
  have : CongruenceClosure (SimpleReduction R) (u₁ ++ r.lhs ++ u₂) (u₁ ++ r.rhs ++ u₂) :=
    CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem)
  rw [h_eq1, h_eq2]
  exact this

lemma localConfluence_and_Rules (R : List (Rule A)) :
  LocallyConfluent R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → CompleteRules r r' R := by
  constructor
  · intro h_LocConfluent r r' ⟨hr, hr'⟩ o
    let w := o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂
    let u := r.rhs ++ o.suffix₂
    let v := o.prefix₁ ++ r'.rhs ++ o.suffix₁
    have h_reduces_wv : OneStepReduction R w v := by
      exact overlap_reduces' R r r' o ⟨hr, hr'⟩
    have h_reduces_wu : OneStepReduction R w u := by
      exact overlap_reduces R r r' o ⟨hr, hr'⟩
    specialize h_LocConfluent w u v h_reduces_wu h_reduces_wv
    exact h_LocConfluent
  · intro h_complete_rules w u v h_reduces_wu h_reduces_wv
    let ⟨r, r_mem, ⟨v1, v2, hr⟩⟩ := rule_of_OneStepReduction R h_reduces_wv
    let ⟨r', r_mem', ⟨u1, u2, hr'⟩⟩ := rule_of_OneStepReduction R h_reduces_wu
    have h_complete : CompleteRules r r' R := by
      exact h_complete_rules r r' ⟨r_mem, r_mem'⟩
    by_cases h : List.IsPrefix (v1 ++ r.lhs ) u1 ∨ List.IsPrefix (u1 ++ r'.lhs) v1
    · cases h with
      |inl h_prefix_u =>
      rcases h_prefix_u with ⟨y, rfl⟩
      let t : Word A := v1 ++ r.rhs ++ y ++ r'.rhs ++ u2
      have h_reduces_vt : Reduction R v t := by
        refine IsInfix_Reduces R r' v t r_mem' ?_
        use (v1 ++ r.rhs ++ y)
        use u2
        constructor
        · have : v2 = y ++ r'.lhs ++ u2 := by simp_all
          grind
        · trivial
      have h_reduces_ut : Reduction R u t := by
        refine IsInfix_Reduces R r u t r_mem ?_
        use v1
        use y ++ r'.rhs ++ u2
        grind
      use t
      |inr h_prefix_v =>
        rcases h_prefix_v with ⟨y, rfl⟩
        let t : Word A := u1 ++ r'.rhs ++ y ++ r.rhs ++ v2
        have h_reduces_vt : Reduction R v t := by
          refine IsInfix_Reduces R r' v t r_mem' ?_
          use u1
          use y ++ r.rhs ++ v2
          grind
        have h_reduces_ut : Reduction R u t := by
          refine IsInfix_Reduces R r u t r_mem ?_
          use u1 ++ r'.rhs ++ y
          use v2
          constructor
          · have : u2 = y ++ r.lhs ++ v2 := by simp_all
            grind
          · trivial
        use t
    · by_cases h_left : List.length v1 ≤ List.length u1
      · by_cases h_right : List.length v2 ≤ List.length u2
        · match List.getRest u1 v1 with
          | some w1 => sorry
          | none => sorry
        · sorry
      · sorry

/-
lemma overlap_of_not_prefix (w v₁ v v₂ u₁ u u₂ : Word A) :
  w = v₁ ++ v ++ v₂ → w = u₁ ++ u ++ u₂ → ¬(List.IsPrefix (v₁ ++ v) u₁) → ¬(List.IsPrefix (u₁ ++ u) v₁)
  → (∃ o ∈ FindOverlaps v u, w = v₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ v₂)
  ∨ (∃ o ∈ FindOverlaps v u, w = v₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ u₂)
  ∨ (∃ o ∈ FindOverlaps u v, w = u₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ v₂)
  ∨ (∃ o ∈ FindOverlaps u v, w = u₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ u₂) := by
  sorry

push_neg at h
      have h : _ :=  overlap_of_not_prefix w v1 r.lhs v2 u1 r'.lhs u2 hr.1 hr'.1 h.1 h.2
      rcases h with h1 | h2 | h3 | h4
      · sorry
      · sorry
      · sorry
      · sorry
-/

lemma lemma1 (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  ∀ r ∈ R, CheckOverlaps r R = [] := by
  intro r hr
  by_contra h_neq
  have h1 : List.flatMap (fun r ↦ CheckOverlaps r R) R ≠ [] := by
    have : ∃ R₁ R₂ : List (Rule A), R = R₁ ++ [r] ++ R₂ := by
      sorry
    obtain ⟨R₁, R₂, h_eq⟩ := this
    have : List.flatMap (fun r ↦ CheckOverlaps r R) R = List.flatMap (fun r ↦ CheckOverlaps r R) R₁ ++ List.flatMap (fun r ↦ CheckOverlaps r R) [r] ++List.flatMap (fun r ↦ CheckOverlaps r R) R₂ := by sorry
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
  have h4: List.length (SortRules (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R)) ≠ List.length R := by
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
  ∀ o : Overlap A r₁.lhs r₂.lhs, Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = none := by sorry

lemma lemma4 (w u : Word A) (R : List (Rule A)) (h_test_eq_none : Test_for_rule w u R = none) :
  Reduce w R = Reduce u R := by sorry

lemma lemma5 (w : Word A) (R : List (Rule A)) : Reduction R w (Reduce w R) := by sorry

lemma locallyConfluent_of_fixpoint (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  LocallyConfluent R := by
  refine (localConfluence_and_Rules R).mpr ?_
  intro r₁ r₂ ⟨h₁, h₂⟩ o
  have h : Reduce (r₁.rhs ++ o.suffix₂) R = Reduce (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R := by
    refine lemma4 (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R ?_
    refine lemma3 r₁ r₂ R ?_ o
    refine lemma2 r₁ R ?_ r₂ h₂
    refine lemma1 R h_fix r₁ h₁
  use Reduce (r₁.rhs ++ o.suffix₂) R
  constructor
  · exact lemma5 (r₁.rhs ++ o.suffix₂) R
  · rw [h]
    exact lemma5 (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R



lemma kLocalConfluence_and_Rules (k : Nat) (R : List (Rule A)) :
  k_LocallyConfluent k R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → k_CompleteRules k r r' R := by
  constructor
  · intro h_LocConfluent r r' ⟨hr, hr'⟩
    unfold k_CompleteRules
    intro o h_len
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
  exact IrrSet_sub_of_sub R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  exact kIrrSet_sub_of_sub k R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma k_Complete_of_kIrrSet_eq_succ (k : Nat) (R : List (Rule A)) :
  kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) → k_Complete k R := by
  sorry

/-
lemma k_Complete_iff_kIrrSet_eq (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ i : Nat, kIrrSet k R = kIrrSet k (OneStepKnuthBendix^[i] R) := by
  sorry
-/
lemma kIrrSet_fin (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by sorry
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}


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
    exact (k_Complete_of_kIrrSet_eq_succ k (OneStepKnuthBendix^[j] R)) hj
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

theorem KnuthBendixConfluent' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  refine (Confluent_iff_LocallyConfluent (KnuthBendix R)).mpr ?_
  refine locallyConfluent_of_fixpoint (KnuthBendix R) ?_
  exact KnuthBendixDomain_Fixpoint R h_dom

theorem KnuthBendix_Complete' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  exact (Confluent_iff_Complete (KnuthBendix R)).mp (KnuthBendixConfluent' R h_dom)
