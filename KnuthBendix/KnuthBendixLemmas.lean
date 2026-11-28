module

public import KnuthBendix.KnuthBendix

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]
variable {u v a b : Word A} {R : Array (Rule A)} {o : Overlap u v}
variable (hu : u = a.reverse ++ b) {S S' : Array (Overlap u v)}

-- LEMMAS ABOUT TEST_FOR_RULE
lemma Test_for_rule_symm : Test_for_rule u v R = Test_for_rule v u R := by
  unfold Test_for_rule
  by_cases h : CanonicalReduction R u = CanonicalReduction R v
  · simp_all
  · have h' : CanonicalReduction R v ≠ CanonicalReduction R u := by exact Ne.symm h
    simp only [h, ↓reduceDIte, h', Option.some.injEq]
    exact MakeRule_symm

lemma TestForRule_some_of_CanonicalReduction_neq
    (h_neq : CanonicalReduction R u ≠ CanonicalReduction R v) :
    ∃ r : Rule A, (Test_for_rule u v R = some r):= by
  use MakeRule (CanonicalReduction R u) (CanonicalReduction R v) h_neq
  unfold Test_for_rule
  simp [h_neq]

lemma TestForRule_some_lhs {r : Rule A} (h : Test_for_rule u v R = some r) :
    (r.lhs = max (CanonicalReduction R u) (CanonicalReduction R v)) ∧
    (r.rhs = min (CanonicalReduction R u) (CanonicalReduction R v)) := by
  unfold Test_for_rule at h
  by_cases h_CReq : CanonicalReduction R u = CanonicalReduction R v
  · simp_all
  · simp +zetaDelta at h
    simp [h_CReq] at h
    unfold MakeRule at h
    grind



-- PROOF OF OVERLAP_MEM_FINDOVERLAPS

section FindOverlaps
omit [LinearOrder (Word A)] [ReductionOrder A]

instance : HasSubset (Array (Overlap u v)) := by sorry

--(1)
lemma FindOverlap_some [LinearOrder (Word A)] :
    FindOverlap u o.prefix₁.reverse (o.overlap ++ o.suffix₁) v  (by simp [o.eq.1]) = some o := by
  unfold FindOverlap
  split <;> rename_i h_nontriv
  · by_cases h_suf1 : o.suffix₁ = []
    · have h1 : List.getRest v (o.overlap ++ o.suffix₁) = some o.suffix₂ := by
        exact (ListGetRest_some (o.eq.2) rfl).mpr h_suf1
      rw! [h1]
      simp only [Option.some.injEq]
      rw! [h_suf1]
      simp only [List.append_nil]
      rw! [←h_suf1]
      simp
      exact MakeOverlap_def o
    · have h_suf2 : o.suffix₂ = [] := Or.resolve_left o.empty h_suf1
      have h : List.getRest v (o.overlap ++ o.suffix₁) = none := by
        exact (ListGetRest_none' (y := o.overlap) (o.eq.2) rfl h_suf2).mpr h_suf1
      have h' : List.getRest (o.overlap ++ o.suffix₁) v = some o.suffix₁ := by
        exact (ListGetRest_some (y := o.overlap) rfl o.eq.2).mpr h_suf2
      rw! [h]
      rw! [h']
      simp only [Option.some.injEq]
      have : v = o.overlap := by
        simp_rw [o.eq.2, h_suf2]
        simp
      simp_rw [this]
      rw! [←h_suf2]
      simp only [List.reverse_reverse]
      exact MakeOverlap_def o
  · push Not at h_nontriv
    specialize h_nontriv (b_nontriv o)
    have v_nontriv : v ≠ [] := by exact v_nontriv o
    contradiction

--(3)
lemma S_sub_FindOverlaps_rec (h : u = a.reverse ++ b) (S : Array (Overlap u v)) :
    S ⊆ (FindOverlaps_rec a b v S h)  := by
  induction b generalizing a S with
  | nil =>
    unfold FindOverlaps_rec
    --exact Array_subset_refl (as := S)
    sorry
  | cons x b' ih =>
    unfold FindOverlaps_rec
    have : u = (x :: a).reverse ++ b' := by simp [h]
    split <;> rename_i o h
    · exact ih (by grind) S
    · specialize ih this (S.push o)
      have : S ⊆ (S.push o) := by sorry
      sorry
      --exact List.subset_def.mpr fun {a} a_1 ↦ ih (this a_1)
      -- List.subset_of_cons_subset ih

lemma mem_FindOverlaps_rec_of_FindOverlap_some (hb : b ≠ []) (h : FindOverlap u a b v hu = some o) :
    o ∈ FindOverlaps_rec a b v S hu := by
  unfold FindOverlaps_rec
  split <;> rename_i x b' hb'
  · contradiction
  · simp only [h, List.concat_eq_append]
    have h1 : o ∈ (S.push o) := by exact Array.mem_push_self
    have h2 : (S.push o) ⊆ (FindOverlaps_rec (x :: a) b' v (S.push o) (by grind)) := by
      exact S_sub_FindOverlaps_rec (by grind) (S.push o)
    sorry
    --exact Multiset.mem_coe.mp (h2 h1)

-- (2)
lemma Overlap_mem_FindOverlaps_rec [LinearOrder (Word A)] :
    o ∈ FindOverlaps_rec o.prefix₁.reverse (o.overlap ++ o.suffix₁) v S
    (by rw [←List.append_assoc]; simp [o.eq.1]) := by
  have : o.overlap ++ o.suffix₁ ≠ [] := by exact b_nontriv o
  apply mem_FindOverlaps_rec_of_FindOverlap_some
  · exact b_nontriv o
  · exact FindOverlap_some


--(5)
lemma FindOverlaps_rec_sub_of_sub (h_sub : S ⊆ S') :
    FindOverlaps_rec a b v S hu  ⊆ FindOverlaps_rec a b v S' hu  := by
  induction b generalizing a S S' with
  | nil =>
    unfold FindOverlaps_rec
    simp_all
  | cons x b' ih =>
    unfold FindOverlaps_rec
    have hu' : u = (x :: a).reverse ++ b' := by grind
    split <;> rename_i o h
    · exact ih hu' h_sub
    · have h_sub' : (S.push o) ⊆ (S'.push o) := by

        sorry
        --exact List.cons_subset_cons o h_sub
      exact ih hu' h_sub'

lemma FindOverlaps_rec_sub_constructor {x : A} (hu : u = a.reverse ++ (x :: b)) :
    FindOverlaps_rec (x :: a) b v S (by simp [hu]) ⊆ FindOverlaps_rec a (x :: b) v S hu := by
  conv =>
  rhs
  unfold FindOverlaps_rec
  simp
  split <;> rename_i o h
  · sorry
  · have : S ⊆ (S.push o) := by
      sorry
      --exact List.subset_cons_of_subset o fun ⦃a⦄ a_1 ↦ a_1
    exact FindOverlaps_rec_sub_of_sub (by grind) this

--TODO: is there a nicer way to handle a ++ b
-- (4')
lemma FindOverlaps_rec_sub_concat' (c : Word A) (S : Array (Overlap u v)) (hu : u = (a.reverse ++ c).reverse ++ b) :
    FindOverlaps_rec (a.reverse ++ c) b v S hu  ⊆
    FindOverlaps_rec c (a ++ b) v S (by simp [hu])  := by
  induction a generalizing c S with
  | nil =>
    simp
    sorry
  | cons x a' ih =>
    have h1 : FindOverlaps_rec ((x :: a').reverse ++ c) b v S (by simp [hu]) ⊆
        FindOverlaps_rec (x :: c) (a' ++ b) v S (by simp [hu]) := by
      specialize ih (x :: c) S (by simp [hu])
      simp
      exact ih
    have h2 : FindOverlaps_rec (x :: c) (a' ++ b) v S (by simp [hu]) ⊆
        FindOverlaps_rec c (x :: a' ++ b) v S (by simp [hu]) := by
      exact FindOverlaps_rec_sub_constructor (by grind)
    sorry
    --exact List.Subset.trans h1 h2

-- (4)
lemma FindOverlaps_rec_sub_concat :
    FindOverlaps_rec a b v S hu ⊆
    FindOverlaps_rec [] (a.reverse ++ b) v S (by simp [hu]) := by
  sorry
  --exact FindOverlaps_rec_sub_concat' (a := a.reverse) (b := b) [] S (by simp [hu])


lemma Overlap_mem_FindOverlaps [LinearOrder (Word A)] : o ∈ FindOverlaps u v  := by
  unfold FindOverlaps
  have h_mem : o ∈ FindOverlaps_rec o.prefix₁.reverse (o.overlap ++ o.suffix₁) v #[]
      (by rw [←List.append_assoc]; simp [o.eq.1]) :=
    Overlap_mem_FindOverlaps_rec
  have h_sub : FindOverlaps_rec (v := u) o.prefix₁.reverse (o.overlap ++ o.suffix₁) v #[] (by simp [o.eq.1]) ⊆
      FindOverlaps_rec [] (o.prefix₁ ++ o.overlap ++ o.suffix₁) v #[]
    (by grind) := by
    have : _ := FindOverlaps_rec_sub_concat (u := u) (v := v)
      (a := o.prefix₁.reverse) (b := (o.overlap ++ o.suffix₁)) (S := #[]) (by simp [o.eq.1])
    simp_all
  have h_eq : FindOverlaps_rec (v := u) [] (o.prefix₁ ++ o.overlap ++ o.suffix₁) v #[] (by grind) =
      FindOverlaps_rec [] u v #[] (by grind) := by grind
  rw [←h_eq]
  sorry
  --exact Multiset.mem_coe.mp (h_sub h_mem)

end  FindOverlaps


-- PROOF THAT IF TEST_FOR_RULE RETURNS SOME r, r APPEARS IN OSKB
section OneStepKnuthBendix
variable {r r' r₁ r₂ : Rule A} {R R' S : Array (Rule A)} {o : Overlap r₁.lhs r₂.lhs}

lemma mem_CheckOverlaps_rules_of_Test_for_rule_some
    (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) :
    r ∈ CheckOverlaps_rules r₁ r₂ R := by
  have overlap_mem : o ∈ FindOverlaps r₁.lhs r₂.lhs := by
    exact Overlap_mem_FindOverlaps
  apply Array.mem_filterMap.mpr
  use o
/-
lemma CheckOverlaps_rec_eq_append (S : List (Rule A)) :
    CheckOverlaps_rec r R R' S = S ++ (CheckOverlaps_rec r R R' []) := by
    induction R' generalizing S with
    | nil =>
      unfold CheckOverlaps_rec
      exact Eq.symm (List.append_nil S)
    | cons r' R'' ih =>
      unfold CheckOverlaps_rec
      simp only [List.nil_append]
      have h1 : _ := ih (S ++ CheckOverlaps_rules r r' R)
      have h2 : _ := ih (CheckOverlaps_rules r r' R)
      rw [h1, h2]
      simp

lemma CheckOverlaps_rec_sub_constr :
    CheckOverlaps_rec r R R' S ⊆ CheckOverlaps_rec r R (r' :: R') S := by
  conv =>
    rhs
    unfold CheckOverlaps_rec
    simp
  rw [CheckOverlaps_rec_eq_append S, CheckOverlaps_rec_eq_append (S ++ CheckOverlaps_rules r r' R)]
  have : S ⊆ (S ++ CheckOverlaps_rules r r' R) := by
    exact List.subset_append_of_subset_left (CheckOverlaps_rules r r' R)
      (by exact List.subset_def.mpr fun {a} a_1 ↦ a_1)
  grind

lemma S_sub_CheckOverlaps_rec_S : S ⊆ CheckOverlaps_rec r R R' S := by
  rw [CheckOverlaps_rec_eq_append S]
  exact List.subset_append_of_subset_left (CheckOverlaps_rec r R R' []) fun ⦃a⦄ a_1 ↦ a_1

lemma mem_CheckOverlaps_rec_of_mem_CheckOverlaps_rules
    (r₂_mem : r₂ ∈ R') (h : r ∈ CheckOverlaps_rules r₁ r₂ R) :
    r ∈ CheckOverlaps_rec r₁ R R' S := by
  induction R' with
  | nil =>
    contradiction
  | cons r' R' ih =>
    by_cases hr' : r' = r₂
    · unfold CheckOverlaps_rec
      simp +zetaDelta only
      rw [hr']
      apply S_sub_CheckOverlaps_rec_S
      exact List.mem_append_right S h
    · have r₂_mem' : r₂ ∈ R' := by
        exact List.mem_of_ne_of_mem (fun a ↦ hr' (Eq.symm a)) r₂_mem
      specialize ih r₂_mem'
      exact CheckOverlaps_rec_sub_constr ih
-/

lemma mem_CheckOverlaps_of_mem_CheckOverlaps_rules
    (r₂_mem : r₂ ∈ R) (h : r ∈ CheckOverlaps_rules r₁ r₂ R) :
    r ∈ CheckOverlaps r₁ R := by
  unfold CheckOverlaps
  exact Array.mem_flatMap_of_mem r₂_mem h

lemma mem_OSKB_of_mem_CheckOverlaps (h_mem : r ∈ R) (h : r' ∈ CheckOverlaps r R) :
    r' ∈ OneStepKnuthBendix R := by
  unfold OneStepKnuthBendix
  --unfold SortRules
  --apply List.mem_mergeSort.mpr
  refine Array.mem_append_right R ?_
  exact Array.mem_flatMap_of_mem h_mem h

lemma mem_OSKB_of_Test_for_rule_some (h_mem₁ : r₁ ∈ R) (h_mem₂ : r₂ ∈ R)
    (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) :
    r ∈ OneStepKnuthBendix R := by
  have : r ∈ CheckOverlaps_rules r₁ r₂ R := mem_CheckOverlaps_rules_of_Test_for_rule_some h
  have : r ∈ CheckOverlaps r₁ R := mem_CheckOverlaps_of_mem_CheckOverlaps_rules h_mem₂ this
  exact mem_OSKB_of_mem_CheckOverlaps h_mem₁ this


lemma not_mem_R_of_Test_for_rule_some
    (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) :
    r ∉ R := by
  have h_mem_irr : r.lhs ∈ IrrSet R := by
    have _ : r.lhs = max (CanonicalReduction R (o.prefix₁ ++ r₂.rhs ++ o.suffix₁))
        (CanonicalReduction R (r₁.rhs ++ o.suffix₂)) := by
      exact (TestForRule_some_lhs h).1
    by_cases h_leq : CanonicalReduction R (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) <
        CanonicalReduction R (r₁.rhs ++ o.suffix₂)
    · have h_eq : r.lhs = CanonicalReduction R (r₁.rhs ++ o.suffix₂) := by grind
      rw [h_eq]
      exact CR_mem_IrrSet
    · have h_eq : r.lhs = CanonicalReduction R (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) := by grind
      rw [h_eq]
      exact CR_mem_IrrSet
  by_contra h_mem
  have h_not_mem_irr : r.lhs ∉ IrrSet R := by
    exact LHS_Reducible h_mem
  contradiction

lemma OSKB_neq_of_Test_for_rule_some (h_mem₁ : r₁ ∈ R) (h_mem₂ : r₂ ∈ R)
    (h : Test_for_rule (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) (r₁.rhs ++ o.suffix₂) R = some r) :
    OneStepKnuthBendix R ≠ R := by
  have h_mem : r ∈ OneStepKnuthBendix R := by exact mem_OSKB_of_Test_for_rule_some h_mem₁ h_mem₂ h
  have h_not_mem : r ∉ R := by exact not_mem_R_of_Test_for_rule_some h
  exact ne_of_mem_of_not_mem' h_mem h_not_mem



--LEMMAS ABOUT ONE STEP KB
variable {i j k n : Nat}

instance : HasSubset (Array (Rule A)) := sorry

lemma Subset_List_to_Array (h : R.toList ⊆ R'.toList) : R ⊆ R' := by
  sorry

lemma OneStepKnuthBendix_eq_NatIterate :
OneStepKnuthBendix^[i + 1] R = OneStepKnuthBendix (OneStepKnuthBendix^[i] R) := by
  have h : OneStepKnuthBendix^[i + 1] R = OneStepKnuthBendix^[1] (OneStepKnuthBendix^[i] R) := by
    have hi : i + 1 = 1 + i := by grind
    rw [hi]
    exact Function.iterate_add_apply OneStepKnuthBendix 1 i R
  rw [h]
  simp

lemma R_sub_OneStepKB :
  R ⊆ OneStepKnuthBendix R := by
  sorry
  /-
  intro r h_mem
  unfold OneStepKnuthBendix
  unfold SortRules
  apply List.mem_mergeSort.mpr
  exact List.mem_append_left (List.flatMap (fun r ↦ CheckOverlaps r R) R) h_mem
-/
lemma R_sub_OneStepKB_Nat :
  R ⊆ OneStepKnuthBendix^[n] R := by
  induction n with
  | zero => simp; sorry
  | succ n hn =>
  rw [OneStepKnuthBendix_eq_NatIterate]
  have : OneStepKnuthBendix^[n] R ⊆ OneStepKnuthBendix (OneStepKnuthBendix^[n] R) := by
    exact R_sub_OneStepKB
  sorry
  --exact List.Subset.trans hn this

lemma OneStepKB_sub_of_succ :
  OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[i + 1] R := by
  rw [OneStepKnuthBendix_eq_NatIterate]
  exact R_sub_OneStepKB

lemma OneStepKnuthBendix_sub_of_leq (h_leq : i ≤ j) :
  OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[j] R := by
  have h : ∀ n : Nat, OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[i + n] R := by
    intro n
    induction n with
    | zero => simp; sorry
    | succ n ih =>
    have : OneStepKnuthBendix^[i + n] R ⊆ OneStepKnuthBendix^[i + (n + 1)] R := by
      apply OneStepKB_sub_of_succ
    sorry
    --exact List.Subset.trans ih this
  specialize h (j - i)
  simp_all



lemma OSKB_fixpoint_of_succ_eq
    (h_succ_eq : (OneStepKnuthBendix^[n] R) = (OneStepKnuthBendix^[n + 1] R)) :
    ∀ i ≥ n, (OneStepKnuthBendix^[i] R) = (OneStepKnuthBendix^[n] R) := by
  have h (j : Nat) : (OneStepKnuthBendix^[n + j] R) = (OneStepKnuthBendix^[n] R) := by
    induction j with
    | zero => trivial
    | succ j ih =>
    have : n + (j + 1) = (n + j) + 1 := by grind
    rw [this, OneStepKnuthBendix_eq_NatIterate, ih, ←OneStepKnuthBendix_eq_NatIterate, h_succ_eq]
  intro i i_ge_n
  specialize h (i - n)
  simp_all


lemma IrrSet_sub : IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  sorry
  --exact IrrSet_sub_of_sub R_sub_OneStepKB

section kIrrSetsOSKB
variable [Finite A]
variable {R : Array (Rule A)}

noncomputable instance : DecidablePred (Irreducible R) := by
  exact Classical.decPred (Irreducible R)
noncomputable instance : DecidablePred (Irreducible (OneStepKnuthBendix R)) := by
  exact Classical.decPred (Irreducible (OneStepKnuthBendix R))

lemma kIrrSet_sub :
  ↑(kIrrSet k (OneStepKnuthBendix R)) ⊆ kIrrSet k R := by
  sorry
  --exact kIrrSet_sub_of_sub R_sub_OneStepKB

lemma kIrrSet_OSKB_sub_of_leq (h_leq : i ≤ j) :
    kIrrSet k (OneStepKnuthBendix^[j] R) ⊆ kIrrSet k (OneStepKnuthBendix^[i] R) := by
  apply kIrrSet_sub_of_sub
  sorry
  --exact OneStepKnuthBendix_sub_of_leq h_leq

lemma kIrrFinset_OSKB_sub_of_leq (h_leq : i ≤ j) :
    kIrrSet k (OneStepKnuthBendix^[j] R) ⊆ kIrrSet k (OneStepKnuthBendix^[i] R) := by
  apply kIrrSet_sub_of_sub
  sorry
  --exact OneStepKnuthBendix_sub_of_leq h_leq

end kIrrSetsOSKB

end OneStepKnuthBendix

/-
lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  exact kIrrSet_sub_of_sub k R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma kIrrSet_OSKB_sub_of_leq (R : List (Rule A)) (k i j : Nat) (h_leq : i ≤ j) :
    kIrrSet k (OneStepKnuthBendix^[j] R) ⊆ kIrrSet k (OneStepKnuthBendix^[i] R) := by
  apply kIrrSet_sub_of_sub
  exact OneStepKnuthBendix_sub_of_leq R i j h_leq

lemma kIrrFinset_OSKB_sub_of_leq (R : List (Rule A)) (k i j : Nat) (h_leq : i ≤ j) :
    kIrrFinset k (OneStepKnuthBendix^[j] R) ⊆ kIrrFinset k (OneStepKnuthBendix^[i] R) := by
  apply kIrrSet_sub_of_sub
  exact OneStepKnuthBendix_sub_of_leq R i j h_leq
-/
