module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Finite.List

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

lemma MakeRule_dec {u v : Word A} {r : Rule A} {R : List (Rule A)} (h : Test_for_rule u v R = some r) :
(r.lhs = max (CanonicalReduction u R) (CanonicalReduction v R)) ∧
(r.rhs = min (CanonicalReduction u R) (CanonicalReduction v R)):= by
unfold Test_for_rule at h
by_cases h_CReq : CanonicalReduction u R = CanonicalReduction v R
· simp_all
· have : MakeRule (CanonicalReduction u R) (CanonicalReduction v R) h_CReq = some r := by
    refine Option.some_inj.mpr ?_
    simp only [h_CReq, ↓reduceDIte, Option.some.injEq] at h
    exact h
  unfold MakeRule at this
  simp_all only [↓reduceDIte, Option.some.injEq]
  rw [←this]
  simp

/-
lemma Test_for_rule_Irreducible {u v : Word A} {r : Rule A} {R : List (Rule A)} (h : Test_for_rule u v R = some r) : r.lhs ∈ IrrSet R ∧ r.rhs ∈ IrrSet R := by sorry
-/

lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  exact IrrSet_sub_of_sub R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  exact kIrrSet_sub_of_sub k R (OneStepKnuthBendix R) (R_sub_OneStepKB R)


lemma Test_for_rule_symm (u v : Word A) (R : List (Rule A)) : Test_for_rule u v R = Test_for_rule v u R := by
  unfold Test_for_rule
  by_cases h : CanonicalReduction u R = CanonicalReduction v R
  · simp_all
  · have h' : CanonicalReduction v R ≠ CanonicalReduction u R := by exact Ne.symm h
    simp [h, h']
    exact MakeRule_symm (CanonicalReduction u R) (CanonicalReduction v R) (of_eq_false (eq_false h))



lemma CanonicalReduction_neq_of_notRelationJoin {u v : Word A} {R : List (Rule A)} (h_notRelationJoin : ¬Relation.Join (Reduction R) u v) : CanonicalReduction u R ≠ CanonicalReduction v R := by
  by_contra h_eq
  let t : Word A := CanonicalReduction u R
  have h_reduces_ut : Reduction R u t := by exact reduces_to_CanonicalReduction u R
  have h_reduces_vt : Reduction R v t := by
    unfold t; rw [h_eq];
    exact reduces_to_CanonicalReduction v R
  have : Relation.Join (Reduction R) u v := by use t
  trivial

--maybe add result that r.lhs = max(CR u, CR v) and r.rhs = min(CR u, CR v)
lemma TestForRule_some_of_CanonicalReduction_neq {u v : Word A} {R : List (Rule A)} (h_neq : CanonicalReduction u R ≠ CanonicalReduction v R) :
∃ r : Rule A,
(Test_for_rule u v R = some r):= by
  use MakeRule (CanonicalReduction u R) (CanonicalReduction v R) h_neq
  unfold Test_for_rule
  simp [h_neq]




lemma b_nontriv {u v : Word A} (o : Overlap u v) : (o.overlap ++ o.suffix₁) ≠ [] := by
  exact List.append_ne_nil_of_left_ne_nil o.nontriv o.suffix₁

lemma v_nontriv {u v : Word A} (o : Overlap u v) : v ≠ [] := by
  rw [o.eq.2]
  exact List.append_ne_nil_of_left_ne_nil o.nontriv o.suffix₂

lemma ListGetRest_some {u v y u' v' : Word A} (hu : u = y ++ u') (hv : v = y ++ v') :
    List.getRest u v = some u' ↔ v' = [] := by
  constructor
  · intro h
    rw [ListGetRestDec] at h
    simp_all
  · intro h
    rw [h] at hv
    simp only [List.append_nil] at hv
    rw [←hv] at hu
    exact ListGetRestDec.mpr hu

lemma ListGetRest_none {v y v' : Word A} (hv : v = y ++ v') :
    List.getRest y v = none ↔ v' ≠ [] := by
  constructor
  · intro h
    by_contra hv'_empty
    have : List.getRest y v = some [] := by
      have : y = y ++ [] := by grind
      rw [this]
      exact (ListGetRest_some (by trivial) hv).mpr hv'_empty
    rw [this] at h
    contradiction
  · intro hv'_nonempty
    cases Option.eq_none_or_eq_some (List.getRest y v) with
    | inl h => exact h
    | inr h =>
      obtain ⟨u', hu⟩ := h
      rw [ListGetRestDec] at hu
      rw [hu] at hv
      simp at hv
      simp_all

lemma ListGetRest_none' {u u' v y v' : Word A} (hu : u = y ++ u') (hv : v = y ++ v') (hu' : u' = []) :
    List.getRest u v = none ↔ v' ≠ [] := by
  rw [hu'] at hu
  simp only [List.append_nil] at hu
  rw [hu]
  exact ListGetRest_none hv

lemma MakeOverlap_eq {u v : Word A} (o : Overlap u v) :
    MakeOverlap o.overlap o.prefix₁ o.suffix₁ o.suffix₂ o.nontriv o.empty o.eq = o := by
  unfold MakeOverlap
  simp


-- PROOF OF OVERLAP_MEM_FINDOVERLAPS

--(1)
lemma FindOverlap_some {u v : Word A} (o : Overlap u v) :
    FindOverlap (u := u) o.prefix₁ (o.overlap ++ o.suffix₁) v  (by simp [o.eq.1]) = some o := by
  unfold FindOverlap
  split <;> rename_i h_nontriv
  by_cases h_suf1 : o.suffix₁ = []
  · have h1 : List.getRest v (o.overlap ++ o.suffix₁) = some o.suffix₂ := by
      exact (ListGetRest_some (o.eq.2) rfl).mpr h_suf1
    rw! [h1]
    simp only [Option.some.injEq]
    rw! [h_suf1]
    simp only [List.append_nil]
    rw! [←h_suf1]
    exact MakeOverlap_eq o
  · have h_suf2 : o.suffix₂ = [] := Or.resolve_left o.empty h_suf1
    have h : List.getRest v (o.overlap ++ o.suffix₁) = none := by
      exact (ListGetRest_none' (y := o.overlap) (o.eq.2) rfl h_suf2).mpr h_suf1
    have h' : List.getRest (o.overlap ++ o.suffix₁) v = some o.suffix₁ := by
      exact (ListGetRest_some (y := o.overlap) rfl o.eq.2).mpr h_suf2
    rw! [h]
    rw! [h']
    simp only [Option.some.injEq]
    rw! [h_suf2]
    have : v = o.overlap := by sorry

    sorry
  push Not at h_nontriv
  have : o.overlap ++ o.suffix₁ ≠ [] := by sorry
  specialize h_nontriv this
  have v_nontriv : v ≠ [] := by exact v_nontriv o
  contradiction

--(3)
lemma S_sub_FindOverlaps_rec {u v : Word A} (a b : Word A) (h : u = a ++ b)
    (S : List (Overlap u v)) : S ⊆ FindOverlaps_rec a b v S h  := by
  induction b generalizing a S with
  | nil =>
    unfold FindOverlaps_rec
    simp
  | cons x b' ih =>
    unfold FindOverlaps_rec
    simp +zetaDelta only [List.concat_eq_append]
    have : u = a ++ [x] ++ b' := by simp [h]
    split <;> rename_i o h
    · exact ih (a ++ [x]) (by sorry) S
    · specialize ih (a ++ [x]) this (o :: S)
      exact List.subset_of_cons_subset ih


lemma mem_FindOverlaps_rec_of_FindOverlap_some {u v a b : Word A} {o : Overlap u v}
    (S : List (Overlap u v)) (hu : u = a ++ b) (hb : b ≠ []) (h : FindOverlap a b v hu = some o) :
    o ∈ FindOverlaps_rec a b v S hu := by
    unfold FindOverlaps_rec
    split <;> rename_i x b' hb'
    · contradiction
    · simp only [h, List.concat_eq_append]
      have h1 : o ∈ (o :: S) := by exact List.mem_cons_self
      have h2 : (o :: S) ⊆ FindOverlaps_rec (a ++ [x]) b' v (o :: S) (by grind) := by
        exact S_sub_FindOverlaps_rec (a ++ [x]) b' (by grind) (o :: S)
      exact Multiset.mem_coe.mp (h2 h1)

-- (2)
lemma Overlap_mem_FindOverlaps_rec {u v : Word A} (o : Overlap u v) (S : List (Overlap u v)) :
    o ∈ FindOverlaps_rec o.prefix₁ (o.overlap ++ o.suffix₁) v S
    (by rw [←List.append_assoc]; exact o.eq.1) := by
  have : o.overlap ++ o.suffix₁ ≠ [] := by exact b_nontriv o
  apply mem_FindOverlaps_rec_of_FindOverlap_some
  · exact b_nontriv o
  · exact FindOverlap_some o


--(5)
lemma FindOverlaps_rec_sub_of_sub {u v : Word A} {S S' : List (Overlap u v)}
    (a b : Word A) (hu : u = a ++ b) (h_sub : S ⊆ S') :
    FindOverlaps_rec a b v S hu  ⊆ FindOverlaps_rec a b v S' hu  := by
  induction b generalizing a S S' with
  | nil =>
    unfold FindOverlaps_rec
    simp_all
  | cons x b' ih =>
    unfold FindOverlaps_rec
    simp only [List.concat_eq_append]
    have hu' : u = a ++ [x] ++ b' := by grind
    split <;> rename_i o h
    · exact ih (a ++ [x]) hu' h_sub
    · have h_sub' : (o :: S) ⊆ (o :: S') := by exact List.cons_subset_cons o h_sub
      exact ih (a ++ [x]) hu' h_sub'

lemma FindOverlaps_rec_sub_constructor {u v : Word A}
    (x : A) (a b : Word A) (S : List (Overlap u v)) (hu : u = a ++ (x :: b)) :
    FindOverlaps_rec (a ++ [x]) b v S (by simp [hu]) ⊆ FindOverlaps_rec a (x :: b) v S hu := by
  conv =>
  rhs
  unfold FindOverlaps_rec
  simp
  split <;> rename_i o h
  · simp
  · have : S ⊆ (o :: S) := by exact List.subset_cons_of_subset o fun ⦃a⦄ a_1 ↦ a_1
    exact FindOverlaps_rec_sub_of_sub (a ++ [x]) b (by grind) this

--TODO: is there a nicer way to handle a ++ b
-- (4')
lemma FindOverlaps_rec_sub_concat' {u v : Word A}
    (a b c : Word A) (S : List (Overlap u v)) (hu : u = c ++ a ++ b) :
    FindOverlaps_rec (c ++ a) b v S hu  ⊆
    FindOverlaps_rec c (a ++ b) v S (by simp [hu])  := by
  induction a generalizing c S with
  | nil =>
    simp
  | cons x a' ih =>
    have h1 : FindOverlaps_rec (c ++ x :: a') b v S hu ⊆
        FindOverlaps_rec (c ++ [x]) (a' ++ b) v S (by simp [hu]) := by
      specialize ih (c ++ [x]) S (by grind)
      have : c ++ x :: a' = c ++ [x] ++ a' := by grind
      rw! [this]
      grind
    have h2 : FindOverlaps_rec (c ++ [x]) (a' ++ b) v S (by simp [hu]) ⊆
        FindOverlaps_rec c (x :: a' ++ b) v S (by simp [hu]) := by
      exact FindOverlaps_rec_sub_constructor x c (a' ++ b) S (by grind)
    exact List.Subset.trans h1 h2

-- (4)
lemma FindOverlaps_rec_sub_concat {u v : Word A} (a b : Word A) (S : List (Overlap u v)) (hu : u = a ++ b) :
    FindOverlaps_rec a b v S hu ⊆
    FindOverlaps_rec [] (a ++ b) v S (by simp [hu]) := by
  exact FindOverlaps_rec_sub_concat' a b [] S hu


lemma Overlap_mem_FindOverlaps {u v : Word A} (o : Overlap u v) : o ∈ FindOverlaps u v  := by
  unfold FindOverlaps
  have h_mem : o ∈ FindOverlaps_rec o.prefix₁ (o.overlap ++ o.suffix₁) v []
      (by rw [←List.append_assoc]; exact o.eq.1) :=
    Overlap_mem_FindOverlaps_rec o []
  have h_sub : FindOverlaps_rec (v := u) o.prefix₁ (o.overlap ++ o.suffix₁) v [] (by grind) ⊆
      FindOverlaps_rec [] (o.prefix₁ ++ o.overlap ++ o.suffix₁) v []
    (by grind) := by
    have : _ := FindOverlaps_rec_sub_concat (u := u) (v := v) o.prefix₁ (o.overlap ++ o.suffix₁) []
      (by grind)
    simp_all
  have h_eq : FindOverlaps_rec (v := u) [] (o.prefix₁ ++ o.overlap ++ o.suffix₁) v [] (by grind) =
      FindOverlaps_rec [] u v [] (by grind) := by grind
  rw [←h_eq]
  exact Multiset.mem_coe.mp (h_sub h_mem)


lemma lemma_1 (r r₁ r₂ : Rule A) (R : List (Rule A)) (o : Overlap r₁.lhs r₂.lhs) (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) : r ∈ CheckOverlaps_rules r₁ r₂ R := by
  --unfold CheckOverlaps_rules
  have overlap_mem : o ∈ FindOverlaps r₁.lhs r₂.lhs := by
    exact Overlap_mem_FindOverlaps o
  sorry


lemma lemma_2_rec''' {r : Rule A} (R R' : List (Rule A)) :
    ∀ S : List (Rule A), CheckOverlaps_rec r R R' S = S ++ (CheckOverlaps_rec r R R' []) := by
    induction R' with
    | nil =>
      unfold CheckOverlaps_rec
      intro S
      exact Eq.symm (List.append_nil S)
    | cons r' R'' ih =>
      intro S
      unfold CheckOverlaps_rec
      simp only [List.nil_append]
      have h1 : _ := ih (S ++ CheckOverlaps_rules r r' R)
      have h2 : _ := ih (CheckOverlaps_rules r r' R)
      rw [h1, h2]
      simp


lemma lemma_2_rec'' {r r' : Rule A} (R R' S : List (Rule A)) :
    CheckOverlaps_rec r R R' S ⊆ CheckOverlaps_rec r R (r' :: R') S := by
  conv =>
    rhs
    unfold CheckOverlaps_rec
    simp
  rw [lemma_2_rec''' R R' S, lemma_2_rec''' R R' (S ++ CheckOverlaps_rules r r' R)]
  have : S ⊆ (S ++ CheckOverlaps_rules r r' R) := by
    exact List.subset_append_of_subset_left (CheckOverlaps_rules r r' R)
      (by exact List.subset_def.mpr fun {a} a_1 ↦ a_1)
  grind

lemma lemma_2_rec' {r : Rule A} (R R' S : List (Rule A)) : S ⊆ CheckOverlaps_rec r R R' S := by
  rw [lemma_2_rec''' R R' S]
  exact List.subset_append_of_subset_left (CheckOverlaps_rec r R R' []) fun ⦃a⦄ a_1 ↦ a_1

--R in  CheckOverlaps_rules r₁ r₂ R should not be R!!!
lemma lemma_2_rec {r r₁ r₂ : Rule A} (R R' S : List (Rule A)) (r₂_mem : r₂ ∈ R')
    (h : r ∈ CheckOverlaps_rules r₁ r₂ R) :
    r ∈ CheckOverlaps_rec r₁ R R' S := by
  induction R' with
  | nil =>
    contradiction
  | cons r' R' ih =>
    by_cases hr' : r' = r₂
    · unfold CheckOverlaps_rec
      simp +zetaDelta only
      rw [hr']
      apply lemma_2_rec'
      exact List.mem_append_right S h
    · have r₂_mem' : r₂ ∈ R' := by
        exact List.mem_of_ne_of_mem (fun a ↦ hr' (id (Eq.symm a))) r₂_mem
      specialize ih r₂_mem'
      exact lemma_2_rec'' R R' S ih

lemma lemma_2 {r r₁ r₂ : Rule A} {R : List (Rule A)} (r₂_mem : r₂ ∈ R) (h : r ∈ CheckOverlaps_rules r₁ r₂ R) :
  r ∈ CheckOverlaps r₁ R := by
  unfold CheckOverlaps
  exact lemma_2_rec R R [] r₂_mem h


lemma lemma_3 (r r' : Rule A) (R : List (Rule A)) (h_mem : r ∈ R) (h : r' ∈ CheckOverlaps r R) :
  r' ∈ OneStepKnuthBendix R := by
  unfold OneStepKnuthBendix
  unfold SortRules
  apply List.mem_mergeSort.mpr
  refine List.mem_append_right R ?_
  exact List.mem_flatMap_of_mem h_mem h

-- TODO: check if we need ReductionOrderLen
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
    refine lemma_3 r₁ r R r₁_mem ?_
    refine lemma_2 r₂_mem ?_
    refine lemma_1 r r₁ r₂ R o ?_
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
      exact ⟨h_len_rlhs, this⟩
    | inr h =>
      have : r.lhs ∈ IrrSet R := by rw [h]; exact CR_Irreducible v R
      exact ⟨h_len_rlhs, this⟩
  have h_not_mem_kIrrOSKBR : r.lhs ∉ kIrrSet k (OneStepKnuthBendix R) := by
    have : r.lhs ∉ IrrSet (OneStepKnuthBendix R) := LHS_Reducible r (OneStepKnuthBendix R) h_mem
    have h_subset : kIrrSet k (OneStepKnuthBendix R) ⊆ IrrSet (OneStepKnuthBendix R) := by
      exact kIrrSet_sub_IrrSet k (OneStepKnuthBendix R)
    exact (Set.mem_compl_iff (kIrrSet k (OneStepKnuthBendix R)) r.lhs).mp fun a ↦ this (h_subset a)
  simp_all

lemma kIrrSet_fin [Finite A] (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by
    exact List.finite_length_le A k
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}


lemma kIrrSet_stabilizes (k : Nat) (R : List (Rule A)) : ∃ n : Nat, ∀ i : Nat, i ≥ n →
  kIrrSet k (OneStepKnuthBendix^[i] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := by
    sorry

lemma k_ResiduesCoincide (k : Nat) (R R' : List (Rule A))
  (hR : k_Complete k R) (hR' : k_Complete k R')
  (h_irr : kIrrSet k R = kIrrSet k R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → CanonicalReduction w R = CanonicalReduction w R' := by sorry

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
  exact (Confluent_iff_Complete).mpr (KnuthBendix_Complete R h_dom)
