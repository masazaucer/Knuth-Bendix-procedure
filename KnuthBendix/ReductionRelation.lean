module

public import KnuthBendix.CanonicalReduction
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.List


@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A] [DecidableEq A]

section Reduction

--DEFINITION OF REDUCTION RELATION AND EQUIVALENCE OF WORDS
-- LHS of rules reduce to corresponding RHS
inductive SimpleReduction (R : List (Rule A)) : Word A → Word A → Prop
  | mk : ∀ r ∈ R, SimpleReduction R r.lhs r.rhs

inductive CongruenceClosure (r : Word A → Word A → Prop) : Word A → Word A → Prop
  | mk : ∀ w w' u₁ u₂ : Word A, r w w' → (CongruenceClosure r (u₁ ++ w ++ u₂) (u₁ ++ w' ++ u₂))

-- congruence closure of simple reduction (i. e. reducing a word by applying one rule)
def OneStepReduction (R : List (Rule A)) := CongruenceClosure (SimpleReduction R)

-- reflexive transitive closure of one step reduction
def Reduction (R : List (Rule A)) := Relation.ReflTransGen (OneStepReduction R)

-- reflexive transitive symmetric closure of one step reduction
def EquivalenceOfWords (R : List (Rule A)) := Relation.EqvGen (OneStepReduction R)



--LEMMAS ABOUT REDUCTION AND ONESTEPREDUCTION
variable {w w' : Word A} {R R' : List (Rule A)}

-- OneStepReduction implies Reduction
lemma Reduction_of_OneStepReduction (h : OneStepReduction R w w') :
    Reduction R w w' := by
  unfold Reduction
  exact Relation.ReflTransGen.single h


-- Characterization or OneStep Reduction with rules
lemma OneStepReduction_iff : OneStepReduction R w w' ↔
    ∃ r ∈ R, ∃ u v : Word A, w = u ++ r.lhs ++ v ∧ w' = u ++ r.rhs ++ v
  := by
  constructor
  · intro OSReduces
    unfold OneStepReduction at OSReduces
    induction OSReduces with
    | mk w w' u₁ u₂ reduces =>
    induction reduces with
    | mk r _ =>
    grind
  · intro ⟨r, h_mem, u, v, ⟨hw, hw'⟩⟩
    unfold OneStepReduction
    have : SimpleReduction R r.lhs r.rhs := by exact SimpleReduction.mk r h_mem
    rw [hw, hw']
    exact CongruenceClosure.mk r.lhs r.rhs u v this

lemma Reduction_iff : Reduction R w w' ↔
    w = w' ∨ (∃ u : Word A, OneStepReduction R w u ∧ Reduction R u w') := by
  unfold Reduction
  exact Relation.ReflTransGen.cases_head_iff

lemma Reduction_of_eq (h_eq : w = w') : Reduction R w w' := by
  apply Reduction_iff.mpr
  exact Or.inl h_eq


-- (OneStep)Reduction returns (strictly) smaller word
lemma OneStepReduction_le (h : OneStepReduction R w w') :
   w' < w := by
  obtain ⟨r, h_mem, u, v, h⟩ := OneStepReduction_iff.mp h
  rw [h.1, h.2]
  apply tir_le
  apply til_le
  exact r.rhs_lt_lhs

lemma Reduction_leq (h : Reduction R w w') :
    w' ≤ w := by
  let C : Word A → Prop := fun x ↦ ∀ y : Word A, Reduction R x y → y ≤ x
  have : C w := by
    apply WellFounded.fix (C := C) ReductionOrder.wf.wf
    intro x ih y reduces_xy
    cases Reduction_iff.mp reduces_xy with
    | inl h_eq => simp_all
    | inr h =>
      obtain ⟨u, hu⟩ := h
      have hux : u < x := by exact OneStepReduction_le hu.1
      have huy : y ≤ u := by exact ih u hux y hu.2
      exact LT.lt.le (lt_of_le_of_lt huy hux)
  exact this w' h


-- (OneStep)Reduction returns shorter word, if the order is consistent with length
lemma Reduction_len_leq [ReductionOrderLen A] (h : Reduction R w w') :
    w'.length ≤ w.length := by
  refine ReductionOrderLen.cwl w' w ?_
  exact Reduction_leq h

lemma OneStepReduction_len_leq [ReductionOrderLen A] (h : OneStepReduction R w w') :
    w'.length ≤ w.length := by
  have : Reduction R w w' := Reduction_of_OneStepReduction h
  exact Reduction_len_leq this


-- If w reduces (in one step) wrt smaller set of rules, it reduces (in one step) also wrt bigger set of rules
lemma OSR_of_OSR_sub (h_sub : R ⊆ R') (h : OneStepReduction R w w') :
    OneStepReduction R' w w' := by
  unfold OneStepReduction at *
  induction h with
  | mk w w' u₁ u₂ h =>
    induction h with
    | mk r r_mem =>
      have r_mem' : r ∈ R' := by exact Multiset.mem_coe.mp (h_sub r_mem)
      have : SimpleReduction R' r.lhs r.rhs := by exact SimpleReduction.mk r (h_sub r_mem)
      exact CongruenceClosure.mk r.lhs r.rhs u₁ u₂ this

lemma Reduction_of_Reduction_sub (h_sub : R ⊆ R') (h : Reduction R w w') :
    Reduction R' w w' := by
  let C : Word A → Prop := fun x ↦ ∀ x', Reduction R x x' → Reduction R' x x'
  have : C w := by
    apply WellFounded.fix ReductionOrder.wf.wf
    intro x ih
    unfold C at *
    intro z reduces_xz
    cases Reduction_iff.mp reduces_xz with
    | inl hl =>
      exact Reduction_of_eq hl
    | inr hr =>
      obtain ⟨u, hu⟩ := hr
      have OSR : OneStepReduction R' x u := by exact OSR_of_OSR_sub h_sub hu.1
      have reduces' : Reduction R' u z := by
        have u_le_x : u < x := by exact OneStepReduction_le OSR
        exact ih u u_le_x z hu.2
      apply Reduction_iff.mpr
      refine Or.inr ?_
      use u
  exact this w' h


-- If ReduceOnce changes w (some rule applies) then w → (ReduceOnce w)
lemma OneStepReduction_ReduceOnce (h_neq : ReduceOnce R w ≠ w) :
    OneStepReduction R w (ReduceOnce R w) := by
  obtain ⟨r, r_mem, v, u, h⟩ := rule_infix_append_of_ReduceOnce_neq h_neq
  unfold OneStepReduction
  have : SimpleReduction R r.lhs r.rhs := by exact SimpleReduction.mk r r_mem
  rw [h.2, h.1]
  refine CongruenceClosure.mk r.lhs r.rhs v u this

-- w →* (ReduceOnce w)
lemma Reduction_ReduceOnce :
    Reduction R w (ReduceOnce R w) := by
  by_cases h_eq : ReduceOnce R w = w
  · nth_rw 1 [h_eq]
    unfold Reduction
    exact Relation.ReflTransGen.refl
  · refine Reduction_of_OneStepReduction ?_
    exact OneStepReduction_ReduceOnce h_eq

-- w →* (CR w R)
lemma reduces_to_CanonicalReduction :
    Reduction R w (CanonicalReduction R w) := by
  let C : Word A → Prop := fun x ↦ Reduction R x (CanonicalReduction R x)
  refine WellFounded.induction (ReductionOrder.wf.wf) (C := C) w ?_
  intro x h
  unfold C at *
  by_cases h_eq : ReduceOnce R x = x
  · have : CanonicalReduction R x = x := fixpoint_CanonicalReduction_of_ReduceOnce h_eq
    rw [this]
    unfold Reduction
    exact Relation.ReflTransGen.refl
  · have h1 : Reduction R x (ReduceOnce R x) := Reduction_ReduceOnce
    have h2 : Reduction R (ReduceOnce R x) (CanonicalReduction R (ReduceOnce R x)) :=
      h (ReduceOnce R x) (ReduceOnce_le x h_eq)
    have h3 : CanonicalReduction R (ReduceOnce R x) = CanonicalReduction R x :=
      CanonicalReduction_ReduceOnce_eq_CanonicalReduction
    rw [←h3]
    unfold Reduction
    exact Relation.ReflTransGen.trans h1 h2



--TRANSLATION INVARIANCE
variable {u v w₁ w₂ : Word A}

lemma OneStepReduction_ti (h : OneStepReduction R u v) :
    OneStepReduction R (w₁ ++ u ++ w₂) (w₁ ++ v ++ w₂) := by
  induction h with
  | mk w w' u₁ u₂ h =>
    have h1 : w₁ ++ (u₁ ++ w ++ u₂) ++ w₂ = (w₁ ++ u₁) ++ w ++ (u₂ ++ w₂) := by
      simp only [List.append_assoc]
    have h2 : w₁ ++ (u₁ ++ w' ++ u₂) ++ w₂ = (w₁ ++ u₁) ++ w' ++ (u₂ ++ w₂) := by
      simp only [List.append_assoc]
    rw [h1, h2]
    exact CongruenceClosure.mk w w' (w₁ ++ u₁) (u₂ ++ w₂) h

lemma Reduction_ti (h : Reduction R v u) : Reduction R (w₁ ++ v ++ w₂) (w₁ ++ u ++ w₂) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | tail reduces_vb reduces_onestep_bc ih =>
    apply Relation.ReflTransGen.tail ih
    exact OneStepReduction_ti reduces_onestep_bc

lemma reduction_relation_ti (h : Relation.Join (Reduction R) u v) :
    Relation.Join (Reduction R) (w₁ ++ u ++ w₂) (w₁ ++ v ++ w₂) := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  have reduces_wvt : Reduction R (w₁ ++ v ++ w₂) (w₁ ++ t ++ w₂) := by
    exact Reduction_ti h_reduces_ut
  have reduces_wut : Reduction R (w₁ ++ u ++ w₂) (w₁ ++ t ++ w₂) := by
    exact Reduction_ti h_reduces_vt
  use (w₁ ++ t ++ w₂)

lemma relation_join_symm (h : Relation.Join (Reduction R) v u) : Relation.Join (Reduction R) u v := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  use t


--OVERLAP REDUCES WRT FIRST AND SECOND RULE
variable {r r' : Rule A} {o : Overlap r.lhs r'.lhs}

lemma overlap_reduces  (h_mem : r ∈ R) :
    OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (r.rhs ++ o.suffix₂) := by
  cases o.empty with
  |inl suf₁_empty =>
  rw [suf₁_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ []) r.rhs := by
    rw [←suf₁_empty, ←(o.eq).1]
    exact SimpleReduction.mk r h_mem
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ [] ++ o.suffix₂) (r.rhs ++ o.suffix₂)
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ []) r.rhs [] o.suffix₂ this
  simp_all only [List.append_nil, List.append_assoc]
  exact this
  |inr suf₂_empty =>
  rw [suf₂_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs := by
    rw [← (o.eq).1]
    exact SimpleReduction.mk r h_mem
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ []) (r.rhs ++ [])
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs [] [] this
  simp_all only [List.append_assoc, List.append_nil]
  exact this

lemma overlap_reduces' (h_mem' : r' ∈ R) :
    OneStepReduction R
    (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)
  := by
  cases o.empty with
    | inl v2_empty =>
      rw [v2_empty]
      have : SimpleReduction R (o.overlap ++ o.suffix₂) r'.rhs := by
        rw [←(o.eq).2]
        exact SimpleReduction.mk r' h_mem'
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ (o.overlap ++ o.suffix₂) ++ []) (o.prefix₁ ++ r'.rhs ++ []) :=
        CongruenceClosure.mk (o.overlap ++ o.suffix₂) r'.rhs o.prefix₁ [] this
      simp_all only [List.append_nil, List.append_assoc]
      exact this
    | inr u2_empty =>
      rw [u2_empty]
      have : SimpleReduction R o.overlap r'.rhs := by
        have : o.overlap ++ [] = r'.lhs := by
          rw [←u2_empty, ←(o.eq).2]
        simp only [List.append_nil] at this
        rw [this]
        exact SimpleReduction.mk r' h_mem'
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ o.overlap ++ o.suffix₁) (o.prefix₁ ++ r'.rhs ++ o.suffix₁) :=
        CongruenceClosure.mk o.overlap r'.rhs o.prefix₁ o.suffix₁ this
      simp_all only [List.append_assoc, List.append_nil]
      exact this

lemma IsInfix_Reduces (r_mem : r ∈ R) (h : ∃ u₁ u₂ : Word A, w = u₁ ++ r.lhs ++ u₂ ∧ v = u₁ ++ r.rhs ++ u₂) :
    Reduction R w v := by
  obtain ⟨u₁, u₂, h⟩ := h
  refine Relation.ReflTransGen.single ?_
  rw [h.1, h.2]
  exact CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem)

end Reduction



section Irreducibles

--IRREDUCIBLE ELEMENTS AND NORMAL FORMS

-- word w is irreducible with respect to R if it is equal to its normal form
def Irreducible (R : List (Rule A)) (w : Word A) : Prop :=
  ∀ r ∈ R, ¬ (List.IsInfix r.lhs w)

def IrrSet (R : List (Rule A)) : Set (Word A) := {w | Irreducible R w}

/-
def kIrrSet (k : Nat) (R : List (Rule A)) : Set (Word A) :=
  {w | w.length ≤ k ∧ Irreducible R w}

lemma kIrrSet_fin [Finite A] (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by
    exact List.finite_length_le A k
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}

noncomputable def kIrrFinset [Finite A] (k : Nat) (R : List (Rule A)) : Finset (Word A) :=
    have : Fintype (kIrrSet k R) := by
      exact Set.Finite.fintype (kIrrSet_fin k R)
    Set.toFinset (kIrrSet k R)

lemma kIrrSet_eq_kIrrFinset [Finite A] (k : Nat) (R : List (Rule A)) :
    kIrrFinset k R = kIrrSet k R := by
  unfold kIrrFinset
  simp +zetaDelta
-/
--def kSet (k : Nat) : Set (Word A) := {w : Word A| w.length ≤ k}

noncomputable def kFinset [Finite A] (k : Nat) : Finset (Word A) :=
  --have fin_len : (kSet k).Finite := by exact List.finite_length_le A k
  Set.Finite.toFinset (List.finite_length_le A k)

open Classical in
noncomputable def kIrrSet [Finite A] (k : Nat) (R : List (Rule A)) : Finset (Word A) :=
  Finset.filter (Irreducible R) (kFinset k)


def UniqueResidue (R : List (Rule A)) (w : Word A) : Prop :=
  ∃! v : Word A, v ∈ IrrSet R ∧ (Reduction R) w v

noncomputable def NormalForm (w : Word A) (R : List (Rule A)) (h_unique_res : UniqueResidue R w) :
  Word A := Classical.choose h_unique_res



--LEMMAS ABOUT IRREDUCIBLES AND NORMAL FORMS
variable {w w' : Word A} {R R' : List (Rule A)}

-- Irreducible element can only reduce to itself
lemma Irreducible_fix (h_irr : Irreducible R w) (h_reduces : Reduction R w w') : w = w' := by
  unfold Irreducible at h_irr
  unfold Reduction at h_reduces
  cases Relation.reflTransGen_iff_eq_or_transGen.mp h_reduces with
  | inl h_eq => simp_all
  | inr h =>
    have : ∃ u, OneStepReduction R w u := by
      obtain ⟨u, hu⟩ := Relation.TransGen.head'_iff.mp h
      exact ⟨u, hu.1⟩
    obtain ⟨w', h_onestep⟩  := this
    obtain ⟨r, r_mem, u, v, h⟩ := OneStepReduction_iff.mp h_onestep
    specialize h_irr r r_mem
    grind

-- If w is irreducible wrt bigger set of rules, it is also irreducible wrt smaller one
lemma Irreducible_of_sub_irr (h_sub : R ⊆ R') (h_irr : Irreducible R' w) :
    Irreducible R w := by
  intro r h_mem
  exact h_irr r (h_sub h_mem)

-- Smaller set of rules gives more irreducible elements
lemma IrrSet_sub_of_sub (h_sub : R ⊆ R') :
    IrrSet R' ⊆ IrrSet R := by
  intro w h_mem
  exact Irreducible_of_sub_irr h_sub h_mem
/-
lemma kIrrSet_sub_of_sub (k : Nat) (R R' : List (Rule A)) (h_sub : R ⊆ R') :
    kIrrSet k R' ⊆ kIrrSet k R := by
  intro w ⟨h_len, h_irr⟩
  exact ⟨h_len, Irreducible_of_sub_irr w R R' h_sub h_irr⟩

lemma kIrrFinset_sub_of_sub [Finite A] (k : Nat) (R R' : List (Rule A)) (h_sub : R ⊆ R') :
    kIrrFinset k R' ⊆ kIrrFinset k R := by
  unfold kIrrFinset
  simp +zetaDelta
  exact kIrrSet_sub_of_sub k R R' h_sub

lemma kIrrSet_sub_IrrSet (k : Nat) (R : List (Rule A)) : kIrrSet k R ⊆ IrrSet R := by
  unfold kIrrSet
  unfold IrrSet
  simp only [Set.setOf_subset_setOf, and_imp, imp_self, implies_true]

lemma kIrrFinset_sub_IrrSet [Finite A] (k : Nat) (R : List (Rule A)) : ↑(kIrrFinset k R) ⊆ IrrSet R := by
  rw [kIrrSet_eq_kIrrFinset k R]
  exact kIrrSet_sub_IrrSet k R
-/

section kIrrSets
variable [Finite A]
variable [DecidablePred (Irreducible R)] [DecidablePred (Irreducible R')] {k : Nat}

lemma kIrrSet_mem :
    w ∈ kIrrSet k R ↔ (w.length ≤ k ∧ Irreducible R w) := by
  unfold kIrrSet
  unfold kFinset
  simp

lemma kIrrSet_sub_of_sub (h_sub : R ⊆ R') :
    kIrrSet k R' ⊆ kIrrSet k R := by
  intro w h_mem
  apply kIrrSet_mem.mpr
  apply kIrrSet_mem.mp at h_mem
  exact ⟨h_mem.1, Irreducible_of_sub_irr h_sub h_mem.2⟩

lemma kIrrSet_sub_IrrSet : ↑(kIrrSet k R) ⊆ IrrSet R := by
  unfold kIrrSet
  rw [Finset.coe_filter]
  unfold IrrSet
  simp

end kIrrSets


-- w irreducible iff ReduceOnce does nothing
lemma irreducible_iff_reduceOnce_eq :
    Irreducible R w ↔ ReduceOnce R w = w := by
  unfold Irreducible
  exact Iff.symm ReduceOnce_eq_iff

-- (CR w) is irreducible
lemma CR_Irreducible : Irreducible R (CanonicalReduction R w) := by
  apply irreducible_iff_reduceOnce_eq.2
  exact CR_fix_ReduceOnce

lemma CR_mem_IrrSet : CanonicalReduction R w ∈ IrrSet R := by
  unfold IrrSet
  exact CR_Irreducible

-- LHS of any r ∈ R is reducible
lemma LHS_Reducible {r : Rule A} (h_mem : r ∈ R) : r.lhs ∉ IrrSet R := by
  unfold IrrSet
  by_contra h_irr
  specialize h_irr r h_mem
  have : List.IsInfix r.lhs r.lhs := List.infix_refl r.lhs
  contradiction


-- If w is irreducible, CR returns the same word
lemma CanonicalReduction_fix_of_Irreducible [DecidableEq A] (h_irr : Irreducible R w) :
    CanonicalReduction R w = w := by
  apply fixpoint_CanonicalReduction_of_ReduceOnce
  exact irreducible_iff_reduceOnce_eq.mp h_irr


-- With canonical reduction we get normal form of w (if it exists!)
lemma NormalForm_eq_CanonicalReduction [DecidableEq A] (h_unique_res : UniqueResidue R w) :
    NormalForm w R h_unique_res = CanonicalReduction R w := by
  have h_reduces : Reduction R w (CanonicalReduction R w) := reduces_to_CanonicalReduction
  have h_irr : CanonicalReduction R w ∈ IrrSet R := CR_mem_IrrSet
  have h_unique : ∀ v : Word A, v ∈ IrrSet R ∧ (Reduction R) w v → v = NormalForm w R h_unique_res
    := (Classical.choose_spec h_unique_res).2
  specialize h_unique (CanonicalReduction R w) ⟨h_irr, h_reduces⟩
  exact Eq.symm h_unique

end Irreducibles
