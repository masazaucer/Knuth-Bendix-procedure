module

public import KnuthBendix.KnuthBendix
public import Mathlib.Data.PFun

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

def Irreducible (w : Word A) (R : List (Rule A)) : Prop := NormalForm w R = w

/-
def IsSubword (v w : Word A) : Prop := ∃ (x y : Word A), w = x ++ v ++ y

def NoSubwords (R : List (Rule A)) : Prop :=
  ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → r.lhs ≠ r'.lhs ∧ ¬ IsSubword r.lhs r'.lhs

def RulesIndependent [DecidableEq (Rule A)] (R : List (Rule A)) : Prop :=
  ∀ r ∈ R, Irreducible r.lhs (R.erase r) ∧ Irreducible r.rhs (R.erase r)

def ReducedRewritingSystem
    [DecidableEq (Rule A)]
    (R : List (Rule A)) : Prop :=
  ∀ r ∈ R,
    let R' := R.erase r
    Irreducible r.rhs R ∧
    Irreducible r.lhs R'

def OneStepReduction' (R : List (Rule A)) (w : Word A) : Word A := ReduceOnceList w R

def OneStepRelation (R : List (Rule A)) (w v : Word A) : Prop :=
  OneStepReduction' R w = v

lemma KnuthBendixConfluent (R : List (Rule A)) (mem_dom : R ∈ PFun.Dom KnuthBendix) : Confluent (KnuthBendix R) := by
  sorry
-/
inductive SimpleReduction (R : List (Rule A)) : Word A → Word A → Prop
  | mk : ∀ r ∈ R, SimpleReduction R r.lhs r.rhs

inductive CongruenceClosure (r : Word A → Word A → Prop) : Word A → Word A → Prop
  | mk : ∀ w w' u₁ u₂ : Word A, r w w' → (CongruenceClosure r (u₁ ++ w ++ u₂) (u₁ ++ w' ++ u₂))

def OneStepReduction (R : List (Rule A)) := CongruenceClosure (SimpleReduction R)

def EquivalenceOfWords (R : List (Rule A)) := Relation.EqvGen (OneStepReduction R)

def Confluent (R : List (Rule A)) : Prop :=
  ∀ a b c,
    Relation.ReflTransGen (OneStepReduction R) a b →
    Relation.ReflTransGen (OneStepReduction R) a c →
    Relation.Join (Relation.ReflTransGen (OneStepReduction R)) b c
