module

public import KnuthBendix.CanonicalReduction
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.List


@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A] [DecidableEq A]

section Reduction

--DEFINITION OF REDUCTION RELATION AND EQUIVALENCE OF WORDS
-- LHS of rules reduce to corresponding RHS
inductive SimpleReduction (R : Array (Rule A)) : Word A → Word A → Prop
  | mk : ∀ r ∈ R, SimpleReduction R r.lhs r.rhs

inductive CongruenceClosure (r : Word A → Word A → Prop) : Word A → Word A → Prop
  | mk : ∀ w w' u₁ u₂ : Word A, r w w' → (CongruenceClosure r (u₁ ++ w ++ u₂) (u₁ ++ w' ++ u₂))

-- congruence closure of simple reduction (i. e. reducing a word by applying one rule)
def OneStepReduction (R : Array (Rule A)) := CongruenceClosure (SimpleReduction R)

-- reflexive transitive closure of one step reduction
def Reduction (R : Array (Rule A)) := Relation.ReflTransGen (OneStepReduction R)

-- reflexive transitive symmetric closure of one step reduction
def EquivalenceOfWords (R : Array (Rule A)) := Relation.EqvGen (OneStepReduction R)



--LEMMAS ABOUT REDUCTION AND ONESTEPREDUCTION
variable {w w' : Word A} {R R' : Array (Rule A)}

-- OneStepReduction implies Reduction
lemma Reduction_of_OneStepReduction (h : OneStepReduction R w w') :
    Reduction R w w' := by
  unfold Reduction
  exact Relation.ReflTransGen.single h


-- Characterization of OneStep Reduction with rules
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


instance : HasSubset (Array (Rule A)) := by
  refine { Subset := ?_ }
  exact fun as bs ↦ as.toList ⊆ bs.toList

-- If w reduces (in one step) wrt smaller set of rules, it reduces (in one step) also wrt bigger set of rules
lemma OSR_of_OSR_sub (h_sub : R ⊆ R') (h : OneStepReduction R w w') :
    OneStepReduction R' w w' := by
  unfold OneStepReduction at *
  induction h with
  | mk w w' u₁ u₂ h =>
    induction h with
    | mk r r_mem =>
      have r_mem' : r ∈ R' := by
        exact Array_subset_mem h_sub r_mem
      exact CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem')

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
      have OSR : OneStepReduction R' x u := by
        exact OSR_of_OSR_sub h_sub hu.1
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
lemma reduces_to_ReduceOnce :
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
  · have h1 : Reduction R x (ReduceOnce R x) := reduces_to_ReduceOnce
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

lemma RelationJoin_ti (h : Relation.Join (Reduction R) u v) :
    Relation.Join (Reduction R) (w₁ ++ u ++ w₂) (w₁ ++ v ++ w₂) := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  have reduces_wvt : Reduction R (w₁ ++ v ++ w₂) (w₁ ++ t ++ w₂) := by
    exact Reduction_ti h_reduces_ut
  have reduces_wut : Reduction R (w₁ ++ u ++ w₂) (w₁ ++ t ++ w₂) := by
    exact Reduction_ti h_reduces_vt
  use (w₁ ++ t ++ w₂)

lemma RelationJoin_symm (h : Relation.Join (Reduction R) v u) : Relation.Join (Reduction R) u v := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  use t


--OVERLAP REDUCES WRT FIRST AND SECOND RULE
variable {r r' : Rule A} {o : Overlap r.lhs r'.lhs}

lemma Overlap_reduces_fst  (h_mem : r ∈ R) :
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

lemma Overlap_reduces_snd (h_mem' : r' ∈ R) :
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

-- same for ProperOverlap
variable {o : ProperOverlap r.lhs r'.lhs}
lemma ProperOverlap_reduces_fst (h_mem : r ∈ R) :
    OneStepReduction R (o.pref ++ o.overlap ++ o.suf) (r.rhs ++ o.suf) := by
  sorry

lemma ProperOverlap_reduces_snd (h_mem' : r' ∈ R) :
    OneStepReduction R (o.pref ++ o.overlap ++ o.suf) (o.pref ++ r'.rhs) := by
  sorry

lemma IsInfix_reduces (r_mem : r ∈ R) (h : ∃ u₁ u₂ : Word A, w = u₁ ++ r.lhs ++ u₂ ∧ v = u₁ ++ r.rhs ++ u₂) :
    Reduction R w v := by
  obtain ⟨u₁, u₂, h⟩ := h
  refine Relation.ReflTransGen.single ?_
  rw [h.1, h.2]
  exact CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem)

end Reduction
