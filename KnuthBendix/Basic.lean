import Mathlib

abbrev Word (A : Type) := List A

structure Rule (A : Type) [LT (Word A)] where
  lhs : Word A
  rhs : Word A
  rhs_lt_lhs : rhs < lhs

class ReductionOrder (α : Type) [LinearOrder (Word α)] where
  wf : WellFounded ((· < ·) : Word α → Word α → Prop)
  tiₗ : ∀ (l₁ l₂ l : Word α), l₁ < l₂ → (l ++ l₁) < (l ++ l₂)
  tiᵣ : ∀ (l₁ l₂ l : Word α), l₁ < l₂ → (l₁ ++ l) < (l₂ ++ l)

variable {A : Type} [LinearOrder A] [DecidableEq A] [WellFoundedLT A]

def MakeRule (w₁ w₂ : Word A) (h_neq : w₁ ≠ w₂) : Rule A := {
  lhs := max w₁ w₂,
  rhs := min w₁ w₂,
  rhs_lt_lhs := by rw [min_lt_max] ; exact h_neq }

def IsPrefix (w : Word A) (r : Rule A) : Option (Word A) := List.getRest w r.lhs

def ReduceOnce (w : Word A) (r : Rule A) : Word A := match w with
| [] => []
| a :: w' =>
  match IsPrefix w r with
  | some u => r.2 ++ u
  | none => a :: ReduceOnce w' r


lemma TrivOr (w : Word A) : w = [] ∨ [] < w := by
  cases w with
  | nil =>
      left
      rfl
  | cons a w' =>
      right
      exact List.nil_lt_cons a w'

lemma EmptyWordBottom (w : Word A) : [] ≤ w := by
  cases TrivOr w with
  | inl h1 =>
    exact Or.inl h1.symm
  | inr h2 =>
    exact Or.inr h2

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

lemma LeqTrivialEmpty (w : Word A) : w ≤ [] → w = [] := by
  intro leq_triv
  by_contra h_neq
  have h1 : [] < w := by
    exact (EmptyWordBottom' w).mpr h_neq
  have h2 : w < [] := by
    exact Std.lt_of_le_of_ne leq_triv h_neq
  exact (lt_self_iff_false []).mp (List.lt_trans h1 h2)


lemma lhsNonempty (r : Rule A) : r.lhs ≠ [] := by
  apply (EmptyWordBottom' r.lhs).mp
  have rhs_lt_lhs : r.rhs < r.lhs := r.rhs_lt_lhs
  cases TrivOr r.rhs with
  | inl h1 =>
    rw [h1] at rhs_lt_lhs
    exact rhs_lt_lhs
  | inr h2 =>
    exact Std.lt_trans h2 rhs_lt_lhs


lemma IsPrefixEmpty (s : Rule A) : IsPrefix [] s = none := by
  unfold IsPrefix
  have lhs_nonempty : s.lhs ≠ [] := lhsNonempty s
  have h1 : ∃ (x : A) (xs : List A), s.lhs = x :: xs := by
    apply List.ne_nil_iff_exists_cons.mp lhs_nonempty
  rcases h1 with ⟨x, xs, h_lhs⟩
  rw [h_lhs]
  exact Option.isNone_iff_eq_none.mp rfl


lemma IsPrefix_nontrivial (w : Word A) (r : Rule A) (h : IsPrefix w r = some u) : w ≠ [] := by
  by_contra h_triv
  rw [h_triv] at h
  rw [IsPrefixEmpty] at h
  contradiction

lemma getRest_eq_concat (w v : Word A) (h : List.getRest w v = some u) : w = v ++ u := by
  sorry

lemma IsPrefix_dec (w : Word A) (r : Rule A) (h : IsPrefix w r = some u) : w = r.lhs ++ u := by
  unfold IsPrefix at h
  exact getRest_eq_concat w r.lhs h


lemma ReduceOnce_leq [ReductionOrder A] (w : Word A) (r : Rule A) : ReduceOnce w r ≤ w := by
  induction w with
  | nil => simp [ReduceOnce]
  | cons a w' ih =>
    simp [ReduceOnce]
    cases h : IsPrefix (a :: w') r with
    | none =>
    simp
    exact List.cons_le_cons a ih
    | some u =>
    simp [h]
    have hw : (a :: w') = r.lhs ++ u :=
      IsPrefix_dec (a :: w') r h
    simp [hw]
    exact Or.inr (ReductionOrder.tiᵣ (α := A) r.rhs r.lhs u r.rhs_lt_lhs)


def ReduceOnceStar (w : Word A) (R : List (Rule A)) : Option (Word A) := sorry

def Reduce (w : Word A) (R : List (Rule A)) (n : Nat) : Option (Word A) := sorry

def CriticalPair (r₁ r₂ : Rule A) : Option (List (Word A)) := sorry
