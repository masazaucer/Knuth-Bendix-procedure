module

public import KnuthBendix.ReductionRelation
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.List


@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A]


section Irreducibles

--IRREDUCIBLE ELEMENTS AND NORMAL FORMS

-- word w is irreducible with respect to R if it is equal to its normal form
def Irreducible (R : Array (Rule A)) (w : Word A) : Prop :=
  ∀ r ∈ R, ¬ (List.IsInfix r.lhs w)

def IrrSet (R : Array (Rule A)) : Set (Word A) := {w | Irreducible R w}

/-
def kIrrSet (k : Nat) (R : List (Rule A)) : Set (Word A) :=
  {w | w.length ≤ k ∧ Irreducible R w}

lemma kIrrSet_fin [Finite A] (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by
    exact List.finite_length_le A k
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}

def kIrrFinset [Finite A] (k : Nat) (R : List (Rule A)) : Finset (Word A) :=
    Set.Finite.toFinset (kIrrSet_fin k R)

lemma kIrrSet_eq_kIrrFinset [Finite A] (k : Nat) (R : List (Rule A)) :
    kIrrFinset k R = kIrrSet k R := by
  unfold kIrrFinset
  simp +zetaDelta

--def kSet (k : Nat) : Set (Word A) := {w : Word A| w.length ≤ k}
-/

instance {R : Array (Rule A)} : DecidablePred (Irreducible R) := fun
  | .nil => by
    sorry
    --apply List.decidableBAll
  | .cons x w => by
    sorry
    --apply List.decidableBAll


noncomputable def kFinset [Finite A] (k : Nat) : Finset (Word A) :=
  Set.Finite.toFinset (List.finite_length_le A k)

open Classical in
noncomputable def kIrrSet [Finite A] (k : Nat) (R : Array (Rule A)) : Finset (Word A) :=
  Finset.filter (Irreducible R) (kFinset k)


def UniqueResidue (R : Array (Rule A)) (w : Word A) : Prop :=
  ∃! v : Word A, v ∈ IrrSet R ∧ (Reduction R) w v

noncomputable def NormalForm (w : Word A) (R : Array (Rule A)) (h_unique_res : UniqueResidue R w) :
  Word A := Classical.choose h_unique_res



--LEMMAS ABOUT IRREDUCIBLES AND NORMAL FORMS
variable {w w' : Word A} {R R' : Array (Rule A)}

-- Irreducible element can only reduce to itself
lemma Irreducible_Infix {v : Word A} (h_irr : Irreducible R w) (h_infix : v <:+: w) :
    Irreducible R v := by sorry


lemma Irreducible_fix [DecidableEq A] (h_irr : Irreducible R w) (h_reduces : Reduction R w w') : w = w' := by
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
  have : r ∈ R' := by exact Array_subset_mem h_sub h_mem
  --refine Array.mem_def.mpr ?_; exact h_sub (h_mem.val)
  exact h_irr r this

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
variable {k : Nat}


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
variable [DecidableEq A]

-- w irreducible iff ReduceOnce does nothing
lemma Irreducible_iff_ReduceOnce_eq :
    Irreducible R w ↔ ReduceOnce R w = w := by
  unfold Irreducible
  exact Iff.symm ReduceOnce_eq_iff

-- (CR w) is irreducible
lemma CR_Irreducible : Irreducible R (CanonicalReduction R w) := by
  apply Irreducible_iff_ReduceOnce_eq.2
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
  exact Irreducible_iff_ReduceOnce_eq.mp h_irr



-- With canonical reduction we get normal form of w (if it exists!)
lemma NormalForm_eq_CanonicalReduction [DecidableEq A] (h_unique_res : UniqueResidue R w) :
    NormalForm w R h_unique_res = CanonicalReduction R w := by
  have h_reduces : Reduction R w (CanonicalReduction R w) := reduces_to_CanonicalReduction
  have h_irr : CanonicalReduction R w ∈ IrrSet R := CR_mem_IrrSet
  have h_unique : ∀ v : Word A, v ∈ IrrSet R ∧ (Reduction R) w v → v = NormalForm w R h_unique_res
    := (Classical.choose_spec h_unique_res).2
  specialize h_unique (CanonicalReduction R w) ⟨h_irr, h_reduces⟩
  exact Eq.symm h_unique
