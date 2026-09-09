module

public import KnuthBendix.CanonicalReduction

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A] [DecidableEq A]


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

-- LEMMAS ABOUT REDUCTION

lemma rule_of_OneStepReduction (R : List (Rule A)) :
  OneStepReduction R w w' →
  ∃ r : Rule A, r ∈ R ∧ ∃ u v : Word A, w = u ++ r.lhs ++ v ∧ w' = u ++ r.rhs ++ v
  := by
  intro OSReduces
  unfold OneStepReduction at OSReduces
  induction OSReduces with
  | mk w w' u₁ u₂ reduces =>
  induction reduces with
  | mk r _ =>
  grind

--IRREDUCIBLE ELEMENTS AND NORMAL FORMS
-- word w is irreducible with respect to R if it is equal to its normal form
def Irreducible (R : List (Rule A)) (w : Word A) : Prop :=
  ∀ r ∈ R, ¬ (List.IsInfix r.lhs w)

def IrrSet (R : List (Rule A)) : Set (Word A) := {w | Irreducible R w}

def kIrrSet (k : Nat) (R : List (Rule A)) : Set (Word A) :=
  {w | w.length ≤ k ∧ Irreducible R w}

def UniqueResidue (R : List (Rule A)) (w : Word A) : Prop :=
  ∃! v : Word A, v ∈ IrrSet R ∧ (Reduction R) w v

noncomputable def NormalForm (w : Word A) (R : List (Rule A)) (h_unique_res : UniqueResidue R w) :
  Word A := Classical.choose h_unique_res


--LEMMAS ABOUT IRREDUCIBLES AND NORMAL FORMS
lemma Irreducible_of_sub_irr (w : Word A) (R R' : List (Rule A)) (h_sub : R ⊆ R')
(h_irr : Irreducible R' w) :
Irreducible R w := by
  intro r h_mem
  exact h_irr r (h_sub h_mem)

lemma IrrSet_sub_of_sub (R R' : List (Rule A)) (h_sub : R ⊆ R') :
IrrSet R' ⊆ IrrSet R := by
  intro w h_mem
  exact Irreducible_of_sub_irr w R R' h_sub h_mem

lemma kIrrSet_sub_of_sub (k : Nat) (R R' : List (Rule A)) (h_sub : R ⊆ R') :
kIrrSet k R' ⊆ kIrrSet k R := by
  intro w ⟨h_len, h_irr⟩
  exact ⟨h_len, Irreducible_of_sub_irr w R R' h_sub h_irr⟩


lemma irreducible_iff_reduceOnce_eq (w : Word A) (R : List (Rule A)) :
  Irreducible R w ↔ ReduceOnce w R = w := by
  unfold Irreducible
  exact Iff.symm (ReduceOnce_eq_iff w R)


lemma CanonicalReductionIrreducible (w : Word A) (R : List (Rule A)) : CanonicalReduction w R ∈ IrrSet R := by
  have : _ := CR_fix_ReduceOnce w R
  apply (irreducible_iff_reduceOnce_eq (CanonicalReduction w R) R).2
  exact CR_fix_ReduceOnce w R

lemma LHS_Reducible (r : Rule A) (R : List (Rule A)) (h_mem : r ∈ R) : r.lhs ∉ IrrSet R := by
  unfold IrrSet
  by_contra h_irr
  specialize h_irr r h_mem
  have : List.IsInfix r.lhs r.lhs := List.infix_refl r.lhs
  contradiction

--Prestavi v CanonicalReduction
lemma fixpoint_CanonicalReduction_of_ReduceOnce (w : Word A) (R : List (Rule A)) (h : ReduceOnce w R = w) :
  CanonicalReduction w R = w := by
  unfold CanonicalReduction
  rw [h]
  simp

lemma CanonicalReduction_fix_of_Irreducible [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_irr : Irreducible R w) : CanonicalReduction w R = w := by
  apply fixpoint_CanonicalReduction_of_ReduceOnce
  exact (irreducible_iff_reduceOnce_eq w R).mp h_irr

lemma Reduction_of_OneStepReduction (w u : Word A) (R : List (Rule A)) (h : OneStepReduction R w u) :
  Reduction R w u := by
  unfold Reduction
  exact Relation.ReflTransGen.single h

lemma isPrefixOf?_eq_some_iff (v w : Word A) :
(∃u : Word A, List.isPrefixOf? v w = some u) ↔ v <+: w := by
  constructor
  · intro ⟨u, hu⟩
    exact ⟨u, List.isPrefixOf?_eq_some_iff_append_eq.mp hu⟩
  · intro ⟨u, hu⟩
    exact ⟨u, List.isPrefixOf?_eq_some_iff_append_eq.mpr hu⟩

lemma isPrefixOf?_eq_none_iff (v w : Word A) :
List.isPrefixOf? v w = none ↔ ¬(v <+: w) := by
  constructor
  · intro h
    by_contra h_pref
    obtain ⟨u, hu⟩ := (isPrefixOf?_eq_some_iff v w).mpr h_pref
    rw [hu] at h
    contradiction
  · intro h_pref
    by_contra neq_none
    have : ∃u : Word A, List.isPrefixOf? v w = some u := by
      exact Option.ne_none_iff_exists'.mp neq_none
    have : v <+: w := by exact (isPrefixOf?_eq_some_iff v w).mp this
    contradiction

lemma ReduceOnce_rec_step (x : A) (a b : Word A) (R : List (Rule A)) (h : ∀ r ∈ R, ¬ r.lhs <+: (x :: b)) :
ReduceOnce_rec a (x :: b) R = ReduceOnce_rec (a ++ [x]) b R := by
  have : Reduce_if_IsPrefix (x :: b) R = none := by
    exact (Reduce_if_IsPrefix_none_iff (x :: b) R).mpr h
  conv =>
  lhs
  unfold ReduceOnce_rec
  rw [this]
  simp

lemma append_eq_of_Reduce_if_IsPrefix_eq_some (w w' : Word A) (R : List (Rule A)) (h : Reduce_if_IsPrefix w R = some w') :
  ∃ r ∈ R, ∃ u : Word A, w = r.lhs ++ u ∧ w' = r.rhs ++ u := by
  let ⟨r, r_mem, h_pref⟩ := (Reduce_if_IsPrefix_some_iff w R).1 ⟨w', h⟩
  induction R with
  | nil =>
    contradiction
  | cons r' R' ih =>
    by_cases h_pref' : r'.lhs <+: w
    · use r'
      constructor
      · exact List.mem_cons_self
      · obtain ⟨u, hu⟩ := h_pref'
        use u
        constructor
        · exact Eq.symm hu
        · unfold Reduce_if_IsPrefix at h
          have : List.isPrefixOf? r'.lhs w = some u := by
            exact List.isPrefixOf?_eq_some_iff_append_eq.mpr hu
          rw [this] at h
          simp only [Option.some.injEq] at h
          exact Eq.symm h
    · have : List.isPrefixOf? r'.lhs w = none := by
        exact (isPrefixOf?_eq_none_iff r'.lhs w).mpr h_pref'
      unfold Reduce_if_IsPrefix at h
      rw [this] at h
      have r_mem' : r ∈ R' := by
        have h_neq : r ≠ r' := by
          by_contra h_eq
          rw [h_eq] at h_pref
          contradiction
        exact List.mem_of_ne_of_mem h_neq r_mem
      specialize ih h r_mem'
      exact List.exists_mem_cons_of_exists ih


lemma rule_infix_of_Reduce_if_IsPrefix_eq_some (w w' : Word A) (R : List (Rule A)) (h : Reduce_if_IsPrefix w R = some w') :
  ∃ r ∈ R, r.lhs <+: w ∧ r.rhs <+: w' := by
  obtain ⟨r, r_mem, u, hu⟩ := append_eq_of_Reduce_if_IsPrefix_eq_some w w' R h
  use r
  exact ⟨r_mem, ⟨u, Eq.symm hu.1⟩, ⟨u, Eq.symm hu.2⟩⟩



lemma rule_infix_ReduceOnce_append_of_lhs_infix (w : Word A) (R : List (Rule A)) (h : ∃ r ∈ R, r.lhs <:+: w) :
  ∃r ∈ R, ∃ v u : Word A, w = v ++ r.lhs ++ u ∧ (ReduceOnce w R) = v ++ r.rhs ++ u := by
  obtain ⟨r, r_mem, h_infix⟩ := h
  induction w with
  | nil =>
    have : r.lhs = [] := by exact List.eq_nil_of_infix_nil h_infix
    have : r.lhs ≠ [] := by exact lhsNonempty r
    contradiction
  | cons x w' ih =>
    let w := x :: w'
    by_cases h_pref : ∃ r' ∈ R, r'.lhs <+: (x :: w')
    · obtain ⟨u, hu⟩ := (Reduce_if_IsPrefix_some_iff (x :: w') R).mpr h_pref
      obtain ⟨r',⟨r_mem', ⟨v, hv⟩⟩⟩ := append_eq_of_Reduce_if_IsPrefix_eq_some (x :: w') u R hu
      have h_eq : ReduceOnce (x :: w') R = u := by
        unfold ReduceOnce
        unfold ReduceOnce_rec
        rw [hu]
        simp
      use r'
      constructor
      · exact r_mem'
      · use []
        use v
        rw [h_eq]
        simp only [List.nil_append]
        exact hv
    · have h' : ∀ r'' ∈ R, ¬(r''.lhs <+: (x :: w')) := by
        push Not at h_pref
        exact h_pref
      have h_pref' : r.lhs <:+: w' := by
        specialize h' r r_mem
        have : r.lhs <+: x :: w' ∨ r.lhs <:+: w' := List.infix_cons_iff.mp h_infix
        grind
      obtain ⟨r', ⟨r_mem', ⟨v, u, h⟩⟩⟩ := ih h_pref'
      use r'
      constructor
      · exact r_mem'
      · use (x :: v)
        use u
        constructor
        · rw [h.1]
          simp
        · have : ReduceOnce (x :: w') R = x :: ReduceOnce w' R := by
            calc _ = ReduceOnce_rec [] (x :: w') R := by unfold ReduceOnce; trivial
                _ = ReduceOnce_rec [x] w' R := by exact ReduceOnce_rec_step x [] w' R h'
                _ = [x] ++ ReduceOnce_rec [] w' R := by exact ReduceOnce_rec_eq_append w' R [x]
                _ = x :: ReduceOnce w' R := by exact List.singleton_append
          rw [this, h.2]
          simp


lemma rule_infix_ReduceOnce_of_lhs_infix (w : Word A) (R : List (Rule A)) (h : ∃ r ∈ R, r.lhs <:+: w) :
  ∃ r' ∈ R, r'.lhs <:+: w ∧ r'.rhs <:+: ReduceOnce w R := by
  obtain ⟨r, r_mem, v, u, h_append⟩ := rule_infix_ReduceOnce_append_of_lhs_infix w R h
  use r
  exact ⟨r_mem, ⟨v, u, Eq.symm h_append.1⟩, ⟨v, u, Eq.symm h_append.2⟩⟩


lemma rule_infix_append_of_ReduceOnce_neq [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnce w R ≠ w) :
  ∃r ∈ R, ∃ v u : Word A, w = v ++ r.lhs ++ u ∧ (ReduceOnce w R) = v ++ r.rhs ++ u := by
  have : ∃ r ∈ R, r.lhs <:+: w := by
    have : _ := (not_congr (ReduceOnce_eq_iff w R)).mp h_neq
    grind
  exact rule_infix_ReduceOnce_append_of_lhs_infix w R this

lemma OneStepReduction_ReduceOnce (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnce w R ≠ w) :
  OneStepReduction R w (ReduceOnce w R) := by
  obtain ⟨r, r_mem, v, u, h⟩ := rule_infix_append_of_ReduceOnce_neq w R h_neq
  unfold OneStepReduction
  have : SimpleReduction R r.lhs r.rhs := by exact SimpleReduction.mk r r_mem
  rw [h.2, h.1]
  refine CongruenceClosure.mk r.lhs r.rhs v u this


lemma Reduction_ReduceOnce (w : Word A) (R : List (Rule A)) :
  Reduction R w (ReduceOnce w R) := by
  by_cases h_eq : ReduceOnce w R = w
  · nth_rw 1 [h_eq]
    unfold Reduction
    exact Relation.ReflTransGen.refl
  · refine Reduction_of_OneStepReduction w (ReduceOnce w R) R ?_
    exact OneStepReduction_ReduceOnce w R h_eq

lemma CanonicalReduction_ReduceOnce_eq_CanonicalReduction (w : Word A) (R : List (Rule A)) :
  CanonicalReduction (ReduceOnce w R) R = CanonicalReduction w R := by
  by_cases h_eq : ReduceOnce w R = w
  · rw [h_eq]
  · conv =>
    rhs
    unfold CanonicalReduction
    simp [h_eq]


lemma reduces_to_CanonicalReduction (w : Word A) (R : List (Rule A)) :
  Reduction R w (CanonicalReduction w R) := by
  let C : Word A → Prop := fun x ↦ Reduction R x (CanonicalReduction x R)
  refine WellFounded.induction (ReductionOrder.wf.wf) (C := C) w ?_
  intro x h
  unfold C at *
  by_cases h_eq : ReduceOnce x R = x
  · have : CanonicalReduction x R = x := fixpoint_CanonicalReduction_of_ReduceOnce x R h_eq
    rw [this]
    unfold Reduction
    exact Relation.ReflTransGen.refl
  · have h1 : Reduction R x (ReduceOnce x R) := Reduction_ReduceOnce x R
    have h2 : Reduction R (ReduceOnce x R) (CanonicalReduction (ReduceOnce x R) R) :=
      h (ReduceOnce x R) (ReduceOnce_le x R h_eq)
    have h3 : CanonicalReduction (ReduceOnce x R) R = CanonicalReduction x R :=
      CanonicalReduction_ReduceOnce_eq_CanonicalReduction x R
    rw [←h3]
    unfold Reduction
    exact Relation.ReflTransGen.trans h1 h2



lemma NormalForm_eq_CanonicalReduction [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_unique_res : UniqueResidue R w) :
  NormalForm w R h_unique_res = CanonicalReduction w R := by
  sorry


--TRANSLATION INVARIANCE
lemma OneStepReduction_ti {v u w₁ w₂ : Word A} (R : List (Rule A))
(h : OneStepReduction R v u) :
  OneStepReduction R (w₁ ++ v ++ w₂) (w₁ ++ u ++ w₂) := by
  induction h with
  | mk w w' u₁ u₂ h =>
    have h1 : w₁ ++ (u₁ ++ w ++ u₂) ++ w₂ = (w₁ ++ u₁) ++ w ++ (u₂ ++ w₂) := by
      simp only [List.append_assoc]
    have h2 : w₁ ++ (u₁ ++ w' ++ u₂) ++ w₂ = (w₁ ++ u₁) ++ w' ++ (u₂ ++ w₂) := by
      simp only [List.append_assoc]
    rw [h1, h2]
    exact CongruenceClosure.mk w w' (w₁ ++ u₁) (u₂ ++ w₂) h

lemma reduction_ti {v u w₁ w₂ : Word A} (R : List (Rule A)) (h : Reduction R v u) :
Reduction R (w₁ ++ v ++ w₂) (w₁ ++ u ++ w₂) := by
  induction h with
  | refl =>
    exact Relation.ReflTransGen.refl
  | tail reduces_vb reduces_onestep_bc ih =>
    apply Relation.ReflTransGen.tail ih
    exact OneStepReduction_ti R reduces_onestep_bc

lemma reduction_relation_ti {v u w₁ w₂ : Word A} (R : List (Rule A))
(h : Relation.Join (Reduction R) v u) :
  Relation.Join (Reduction R) (w₁ ++ v ++ w₂) (w₁ ++ u ++ w₂) := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  have reduces_wvt : Reduction R (w₁ ++ v ++ w₂) (w₁ ++ t ++ w₂) := by
    exact reduction_ti R h_reduces_vt
  have reduces_wut : Reduction R (w₁ ++ u ++ w₂) (w₁ ++ t ++ w₂) := by
    exact reduction_ti R h_reduces_ut
  use (w₁ ++ t ++ w₂)

lemma relation_join_symm {v u : Word A} (R : List ( Rule A))
(h : Relation.Join (Reduction R) v u) :
  Relation.Join (Reduction R) u v := by
  obtain ⟨t, ⟨h_reduces_vt, h_reduces_ut⟩⟩ := h
  use t


--OVERLAP REDUCES WRT FIRST AND SECOND RULE
lemma overlap_reduces (R : List (Rule A)) (r r' : Rule A) (o : Overlap r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (r.rhs ++ o.suffix₂) := by
  cases o.empty with
  |inl suf₁_empty =>
  rw [suf₁_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ []) r.rhs := by
    rw [←suf₁_empty, ←(o.eq).1]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ [] ++ o.suffix₂) (r.rhs ++ o.suffix₂)
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ []) r.rhs [] o.suffix₂ this
  simp_all only [List.append_nil, List.append_assoc]
  exact this
  |inr suf₂_empty =>
  rw [suf₂_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs := by
    rw [← (o.eq).1]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ []) (r.rhs ++ [])
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs [] [] this
  simp_all only [List.append_assoc, List.append_nil]
  exact this

lemma overlap_reduces'  (R : List (Rule A)) (r r' : Rule A)
  (o : Overlap r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)
  := by
  cases o.empty with
    | inl v2_empty =>
      rw [v2_empty]
      have : SimpleReduction R (o.overlap ++ o.suffix₂) r'.rhs := by
        rw [←(o.eq).2]
        exact SimpleReduction.mk r' h_mem.2
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
        exact SimpleReduction.mk r' h_mem.2
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ o.overlap ++ o.suffix₁) (o.prefix₁ ++ r'.rhs ++ o.suffix₁) :=
        CongruenceClosure.mk o.overlap r'.rhs o.prefix₁ o.suffix₁ this
      simp_all only [List.append_assoc, List.append_nil]
      exact this

lemma IsInfix_Reduces (R : List (Rule A)) (r : Rule A) (w u : Word A) (r_mem : r ∈ R) :
  (∃ u₁ u₂ : Word A, w = u₁ ++ r.lhs ++ u₂ ∧ u = u₁ ++ r.rhs ++ u₂) → Reduction R w u := by
  intro ⟨u₁, u₂, ⟨h_eq1, h_eq2⟩⟩
  refine Relation.ReflTransGen.single ?_
  have : CongruenceClosure (SimpleReduction R) (u₁ ++ r.lhs ++ u₂) (u₁ ++ r.rhs ++ u₂) :=
    CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem)
  rw [h_eq1, h_eq2]
  exact this
