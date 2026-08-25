module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.MinMax
public import Mathlib.Order.WellFounded
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Prod.Lex

@[expose] public section

-- we represent word as a list of characters of a given alphabet A
abbrev Word (A : Type) := List A

-- Ordered pair of words
@[ext] structure Rule (A : Type) [LT (Word A)] where
  lhs : Word A
  rhs : Word A
  rhs_lt_lhs : rhs < lhs
deriving DecidableEq

structure Overlap {A : Type} (w u : Word A) where
  overlap : Word A
  prefix₁ : Word A
  suffix₁ : Word A
  suffix₂ : Word A
  nontriv : overlap ≠ []
  eq : w = prefix₁ ++ overlap ++ suffix₁ ∧ u = overlap ++ suffix₂
  empty : suffix₁ = [] ∨ suffix₂ = []

-- linear order that is well-founded and translation invariant
-- we define it on words so that we can use concatenation of lists
class ReductionOrder (α : Type) [LinearOrder (Word α)] where
  wf : WellFoundedLT (Word α)
  tiₗ : ∀ (l₁ l₂ l : Word α), l₁ < l₂ → (l ++ l₁) < (l ++ l₂)
  tiᵣ : ∀ (l₁ l₂ l : Word α), l₁ < l₂ → (l₁ ++ l) < (l₂ ++ l)

attribute [instance] ReductionOrder.wf

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A]

open Function

def f : Rule A → Lex (Word A × Word A) := fun r ↦ (r.lhs, r.rhs)

lemma f_Injective : Injective (f (A := A)) := by
  intro r r' h_eq
  unfold f at h_eq
  ext1
  · grind
  · grind

instance : LinearOrder (Rule A) :=
  LinearOrder.lift' f f_Injective

lemma OrderOnRules (r₁ r₂ : Rule A) :
  r₁ < r₂ ↔ r₁.lhs < r₂.lhs ∨ (r₁.lhs = r₂.lhs ∧ r₁.rhs < r₂.rhs) := by
  constructor
  · intro h_leq
    have h_f_leq : f r₁ < f r₂ := by exact lt_of_lt_of_eq h_leq rfl
    refine Prod.lex_def.mp h_f_leq
  · intro h_le
    have h_f_leq : f r₁ < f r₂ := by exact Prod.Lex.lt_iff.mpr h_le
    exact lt_of_lt_of_eq h_f_leq rfl


def SortRules (R : List (Rule A)) : List (Rule A) := List.mergeSort R


-- Forms a (directed) rule from a pair of words
def MakeRule (w₁ w₂ : Word A) (h_neq : w₁ ≠ w₂) : Rule A := {
  lhs := max w₁ w₂,
  rhs := min w₁ w₂,
  rhs_lt_lhs := by rw [min_lt_max] ; exact h_neq }

def MakeOverlap (w v y w_pre w_suf v_suf : Word A) (h_nontriv : y ≠ [])
  (h_empty : w_suf = [] ∨ v_suf = []) (h_eq : w = w_pre ++ y ++ w_suf ∧ v = y ++ v_suf) :
  Overlap w v := {
    overlap := y,
    prefix₁ := w_pre,
    suffix₁ := w_suf,
    suffix₂ := v_suf,
    eq := h_eq
    nontriv := h_nontriv,
    empty := h_empty }

lemma til_leq (l₁ l₂ l : Word A) (h : l₁ ≤ l₂) : (l ++ l₁) ≤ (l ++ l₂) := by
  by_cases h_lt : l₁ < l₂
  · exact le_of_lt (ReductionOrder.tiₗ l₁ l₂ l h_lt)
  · have h_eq : l₁ = l₂ := le_antisymm h (le_of_not_gt h_lt)
    rw [h_eq]

lemma tir_leq (l₁ l₂ l : Word A) (h : l₁ ≤ l₂) : (l₁ ++ l) ≤ (l₂ ++ l) := by
  by_cases h_lt : l₁ < l₂
  · exact le_of_lt (ReductionOrder.tiᵣ l₁ l₂ l h_lt)
  · have h_eq : l₁ = l₂ := le_antisymm h (le_of_not_gt h_lt)
    rw [h_eq]

def pow (w : Word A) (n : Nat) : Word A :=
  match n with
  | 0 => []
  | Nat.succ m => (pow w m) ++ w

lemma pow_desc (w : Word A) (h : w < ([] : Word A)) :
  ∀ n : Nat, pow w (n + 1) < pow w n := by
  intro n
  induction n with
  | zero =>
    unfold pow
    unfold pow
    simp_all
  | succ m ih =>
    unfold pow
    exact ReductionOrder.tiᵣ (pow w (m + 1)) (pow w m) w ih

lemma EmptyWordBottom (w : Word A) : [] ≤ w := by
  by_contra h
  push Not at h
  have hacc : Acc (· < ·) ([] : Word A) := ReductionOrder.wf.wf.apply []
  have no_chain :
        ∀ u : Word A , Acc (· < ·) u →
        ∀ f : ℕ → Word A, f 0 = u → (∀ n, f (n+1) < f n) → False
      := by
      intro a ha
      induction ha with
      | intro a ha ih =>
          intro f hf0 hstep
          have hf1 :
              (fun n => f (n+1)) 0 = f 1 := rfl
          have htail :
              ∀ n, (fun n => f (n+1)) (n+1) <
                  (fun n => f (n+1)) n := by
            intro n
            simpa using hstep (n+1)
          have h_le : f 1 < a := by
            specialize hstep 0
            rw [←hf1, ←hf0]
            simp_all
          exact ih _ h_le (fun n => f (n+1)) hf1 htail
  have : pow w 0 = [] := by
    unfold pow
    trivial
  exact no_chain [] hacc (pow w) this (pow_desc w h)


lemma TrivOr (w : Word A) : w = [] ∨ [] < w := by
  have : [] ≤ w := EmptyWordBottom w
  exact Or.symm (Decidable.lt_or_eq_of_le' this)


lemma EmptyWordBottom' (w : Word A) : [] < w ↔ w ≠ [] := by
  constructor
  · intro h_neq
    by_contra h_triv
    rw [h_triv] at h_neq
    exact lt_irrefl [] h_neq
  · intro h_neq
    cases TrivOr w with
    | inl h1 =>
      rw [h1] at h_neq
      contradiction
    | inr h2 =>
      exact h2

lemma LeqTrivial_Empty (w : Word A) : w ≤ [] → w = [] := by
  intro leq_triv
  exact eq_of_ge_of_le (EmptyWordBottom w) leq_triv


lemma lhsNonempty (r : Rule A) : r.lhs ≠ [] := by
  apply (EmptyWordBottom' r.lhs).mp
  have rhs_lt_lhs : r.rhs < r.lhs := r.rhs_lt_lhs
  cases TrivOr r.rhs with
  | inl h1 =>
    rw [h1] at rhs_lt_lhs
    exact rhs_lt_lhs
  | inr h2 =>
    exact Std.lt_trans h2 rhs_lt_lhs
