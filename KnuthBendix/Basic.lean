module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.MinMax
public import Mathlib.Order.WellFounded
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Prod.Lex
public import Mathlib.SetTheory.Lists

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
  tiₗ : ∀ (l₁ l₂ l : Word α), l₁ ≤ l₂ → (l ++ l₁) ≤ (l ++ l₂)
  tiᵣ : ∀ (l₁ l₂ l : Word α), l₁ ≤ l₂ → (l₁ ++ l) ≤ (l₂ ++ l)

class ReductionOrderLen (α : Type) [LinearOrder (Word α)] extends ReductionOrder α where
  cwl : ∀ (l₁ l₂ : Word α), l₁ ≤ l₂ → l₁.length ≤ l₂.length


attribute [instance] ReductionOrder.wf

variable {A : Type}

variable [LinearOrder (Word A)]

open Function

-- ORDER ON RULES

def f : Rule A → Lex (Word A × Word A) := fun r ↦ (r.lhs, r.rhs)

lemma f_Injective : Injective (f (A := A)) := by
  intro r r' h_eq
  unfold f at h_eq
  ext1
  · grind
  · grind

instance : LinearOrder (Rule A) :=
  LinearOrder.lift' f f_Injective

def SortRules (R : List (Rule A)) : List (Rule A) := List.mergeSort R

lemma OrderOnRules (r₁ r₂ : Rule A) :
  r₁ < r₂ ↔ r₁.lhs < r₂.lhs ∨ (r₁.lhs = r₂.lhs ∧ r₁.rhs < r₂.rhs) := by
  constructor
  · intro h_leq
    have h_f_leq : f r₁ < f r₂ := by exact lt_of_lt_of_eq h_leq rfl
    refine Prod.lex_def.mp h_f_leq
  · intro h_le
    have h_f_leq : f r₁ < f r₂ := by exact Prod.Lex.lt_iff.mpr h_le
    exact lt_of_lt_of_eq h_f_leq rfl



-- MAKE OVERLAP AND RULE

def MakeOverlap {w v : Word A} (y w_pre w_suf v_suf : Word A) (h_nontriv : y ≠ [])
  (h_empty : w_suf = [] ∨ v_suf = []) (h_eq : w = w_pre ++ y ++ w_suf ∧ v = y ++ v_suf) :
  Overlap w v := {
    overlap := y,
    prefix₁ := w_pre,
    suffix₁ := w_suf,
    suffix₂ := v_suf,
    nontriv := h_nontriv,
    empty := h_empty,
    eq := h_eq }

-- Forms a (directed) rule from a pair of words
def MakeRule (w₁ w₂ : Word A) (h_neq : w₁ ≠ w₂) : Rule A := {
  lhs := max w₁ w₂,
  rhs := min w₁ w₂,
  rhs_lt_lhs := by rw [min_lt_max] ; exact h_neq }


--LEMMAS ABOUT "MakeRule"

lemma MakeRule_symm (u v : Word A) (h : u ≠ v) : MakeRule u v h = MakeRule v u (Ne.symm h):= by
  unfold MakeRule
  have h_eq_max : max u v = max v u := by exact max_comm u v
  have h_eq_min : min u v = min v u := by exact min_comm u v
  exact Rule.ext h_eq_max h_eq_min

lemma LHS_eq (u v : Word A) (h_neq : u ≠ v) :
  let r := MakeRule u v h_neq;
  r.lhs = max u v := by
  unfold MakeRule
  simp +zetaDelta


lemma RHS_eq (u v : Word A) (h_neq : u ≠ v) :
  let r : Rule A := MakeRule u v h_neq;
  r.rhs = min u v := by
  unfold MakeRule
  simp +zetaDelta

lemma b_nontriv {u v : Word A} (o : Overlap u v) : (o.overlap ++ o.suffix₁) ≠ [] := by
  exact List.append_ne_nil_of_left_ne_nil o.nontriv o.suffix₁

lemma v_nontriv {u v : Word A} (o : Overlap u v) : v ≠ [] := by
  rw [o.eq.2]
  exact List.append_ne_nil_of_left_ne_nil o.nontriv o.suffix₂



variable [ReductionOrder A]


--TRANSLATION INVARIANCE (STRICT)

lemma til_le {l₁ l₂ l : Word A} (h : l₁ < l₂) : (l ++ l₁) < (l ++ l₂) := by
  refine Std.lt_iff_le_and_ne.mpr ?_
  constructor
  · apply ReductionOrder.tiₗ
    exact Std.le_of_lt h
  · by_contra h_eq
    have : l₁ = l₂ := by exact List.append_cancel_left h_eq
    simp_all

lemma tir_le {l₁ l₂ l : Word A} (h : l₁ < l₂) : (l₁ ++ l) < (l₂ ++ l) := by
  refine Std.lt_iff_le_and_ne.mpr ?_
  constructor
  · apply ReductionOrder.tiᵣ
    exact Std.le_of_lt h
  · by_contra h_eq
    have : l₁ = l₂ := by exact List.append_cancel_right h_eq
    simp_all


--LEMMAS ABOUT EMPTY WORD BEING THE LEAST ELEMENT

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
    exact tir_le ih

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


-- RULE CANNOT HAVE TRIVIAL LHS
lemma lhsNonempty (r : Rule A) : r.lhs ≠ [] := by
  apply (EmptyWordBottom' r.lhs).mp
  have rhs_lt_lhs : r.rhs < r.lhs := r.rhs_lt_lhs
  cases TrivOr r.rhs with
  | inl h1 =>
    rw [h1] at rhs_lt_lhs
    exact rhs_lt_lhs
  | inr h2 =>
    exact Std.lt_trans h2 rhs_lt_lhs


section ListGetRest
variable {A : Type}
variable [DecidableEq A]

lemma ListGetRestDec {w u v : Word A} : List.getRest w u = some v ↔ w = u ++ v := by
  constructor
  · intro h
    induction u generalizing w v with
    | nil =>
      unfold List.getRest at h
      grind
    | cons x u' ih =>
      cases w with
      | nil =>
        unfold List.getRest at h
        grind
      | cons y w' =>
        unfold List.getRest at h
        grind
  · intro h
    induction u generalizing w v with
    | nil =>
      unfold List.getRest
      grind
    | cons x u' ih =>
      unfold List.getRest
      cases w with
      | nil =>
        grind
      | cons y w' =>
        grind


lemma ListGetRest_some {u v y u' v' : Word A} (hu : u = y ++ u') (hv : v = y ++ v') :
    List.getRest u v = some u' ↔ v' = [] := by
  constructor
  · intro h
    rw [ListGetRestDec] at h
    simp_all
  · intro h
    rw [h] at hv
    simp only [List.append_nil] at hv
    rw [←hv] at hu
    exact ListGetRestDec.mpr hu

lemma ListGetRest_none {v y v' : Word A} (hv : v = y ++ v') :
    List.getRest y v = none ↔ v' ≠ [] := by
  constructor
  · intro h
    by_contra hv'_empty
    have : List.getRest y v = some [] := by
      have : y = y ++ [] := by grind
      rw [this]
      exact (ListGetRest_some (by trivial) hv).mpr hv'_empty
    rw [this] at h
    contradiction
  · intro hv'_nonempty
    cases Option.eq_none_or_eq_some (List.getRest y v) with
    | inl h => exact h
    | inr h =>
      obtain ⟨u', hu⟩ := h
      rw [ListGetRestDec] at hu
      rw [hu] at hv
      simp at hv
      simp_all

lemma ListGetRest_none' {u u' v y v' : Word A} (hu : u = y ++ u') (hv : v = y ++ v') (hu' : u' = []) :
    List.getRest u v = none ↔ v' ≠ [] := by
  rw [hu'] at hu
  simp only [List.append_nil] at hu
  rw [hu]
  exact ListGetRest_none hv

lemma MakeOverlap_eq {u v : Word A} (o : Overlap u v) :
    MakeOverlap o.overlap o.prefix₁ o.suffix₁ o.suffix₂ o.nontriv o.empty o.eq = o := by
  unfold MakeOverlap
  simp

end ListGetRest
