module

public import KnuthBendix.reductions
public import Mathlib.SetTheory.Lists

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

--DEFINITION OF EQUIVALENCE OF WORDS
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

lemma Irreducible_of_sub_irr (w : Word A) (R R' : List (Rule A)) (h_sub : R ⊆ R') (h_irr : Irreducible R' w) :
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


lemma NormalForm_eq_Reduce [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_unique_res : UniqueResidue R w) :
  NormalForm w R h_unique_res = Reduce w R := by
  sorry

lemma Reduce_eq_of_Irreducible [DecidableEq A] (w : Word A) (R : List (Rule A))
(h_irr : Irreducible R w) :
  Reduce w R = w := by
  sorry


-- DEFINITION OF CONFLUENCE AND COMPLETENESS
-- R is confluent if w → v and w → u implies ∃ t, v → t and u → t
def Confluent (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    (Reduction R) w v →
    (Reduction R) w u →
    (Relation.Join (Reduction R)) v u

-- confluence for words of lenght at most k
def k_Confluent (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    w.length ≤ k →
    (Reduction R) w v →
    (Reduction R) w u →
    (Relation.Join (Reduction R)) v u

def k_Complete (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w : Word A, w.length ≤ k → UniqueResidue R w

def Complete (R : List (Rule A)) : Prop :=
  ∀ w : Word A, UniqueResidue R w

def LocallyConfluent (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    (OneStepReduction R) w v →
    (OneStepReduction R) w u →
    (Relation.Join (Reduction R)) v u

def k_LocallyConfluent (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    w.length ≤ k →
    (OneStepReduction R) w v →
    (OneStepReduction R) w u →
    (Relation.Join (Reduction R)) v u

-- LEMMAS ABOUT CONFLUENCE, LOCAL CONFLUENCE AND COMPLETENESS
lemma Confluent_iff_Complete (R : List (Rule A)) : Confluent R ↔ Complete R := by
  sorry

lemma k_Confluent_iff_k_Complete (k : Nat) (R : List (Rule A)) :
  k_Confluent k R ↔ k_Complete k R := by sorry

lemma k_Complete_of_Complete (k : Nat) (R : List (Rule A)) (h_complete : Complete R) :
  k_Complete k R := by sorry

lemma Complete_of_k_Complete (R : List (Rule A)) (h_k_complete : ∀ k : Nat, k_Complete k R) :
  Complete R := by sorry

lemma k_Confluent_of_Confluent (k : Nat) (R : List (Rule A)) (h_confluent : Confluent R) :
  k_Confluent k R := by sorry

lemma Confluent_of_k_Confluent (R : List (Rule A)) (h_k_confluent : ∀ k : Nat, k_Confluent k R) :
  Confluent R := by sorry

lemma Confluent_iff_LocallyConfluent (R : List (Rule A)) : Confluent R ↔ LocallyConfluent R := by sorry

lemma k_Confluent_iff_k_LocallyConfluent (k : Nat) (R : List (Rule A)) :
  k_Confluent k R ↔ k_LocallyConfluent k R := by sorry
