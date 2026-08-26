module

public import KnuthBendix.CanonicalReduction

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A]


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


lemma NormalForm_eq_CanonicalReduction [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_unique_res : UniqueResidue R w) :
  NormalForm w R h_unique_res = CanonicalReduction w R := by
  sorry

lemma CanonicalReduction_fix_of_Irreducible [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_irr : Irreducible R w) :
  CanonicalReduction w R = w := by
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
