module

public import KnuthBendix.KnuthBendix
public import Init.Prelude
public import Mathlib.Data.List.Shortlex
public import Mathlib.Order.RelClasses

@[expose] public section

open List

namespace Example1

-- alphabet
inductive Gen where
  | a
  | a_inv
  | b
  | b_inv
  deriving DecidableEq, Repr

abbrev a : Gen := Gen.a
abbrev b : Gen := Gen.b
abbrev a_inv : Gen := Gen.a_inv
abbrev b_inv : Gen := Gen.b_inv

-- order on alphabet
def f : Gen → Fin 4
  | .a => 0
  | .a_inv => 1
  | .b => 2
  | .b_inv => 3

lemma f_inj : Function.Injective f := by
  intro x y h_eq
  unfold f at h_eq
  grind

def g : Fin 4 → Gen
  | 0 => .a
  | 1 => .a_inv
  | 2 => .b
  | 3 => .b_inv

lemma f_sur : Function.Surjective f := by
  refine Function.HasRightInverse.surjective ?_
  use g
  intro x
  unfold f
  unfold g
  grind

instance : LinearOrder Gen := LinearOrder.lift' f f_inj

-- ShortLex order on words
instance : IsStrictTotalOrder (Word Gen) (List.Shortlex (· < ·)) where
 trans := by
  intro a b c hab hbc
  by_cases h_eq_ab : a = b
  · rw [h_eq_ab]
    exact hbc
  · by_cases h_eq_bc : b = c
    · rw [←h_eq_bc]
      exact hab
    · have hab' : _ := List.shortlex_def.mp hab
      have hbc' : _ := List.shortlex_def.mp hbc
      apply List.shortlex_def.mpr
      cases hab' with
      | inl le_ab =>
        cases hbc' with
        | inl le_bc =>
          refine Or.inl (Nat.lt_trans le_ab le_bc)
        | inr h =>
          rw [h.1] at le_ab
          exact Or.inl le_ab
      | inr h =>
        cases hbc' with
        | inl le_bc =>
          rw [h.1]
          refine Or.inl le_bc
        | inr h' =>
          refine Or.inr ?_
          constructor
          · rw [←h.1] at h'
            exact h'.1
          · apply List.lex_trans ?_ h.2 h'.2
            exact fun {x y z} a a_1 ↦ Std.lt_trans a a_1

instance : DecidableRel (List.Shortlex (α := Gen) (· < ·)) := by
  intro u v
  apply decidable_of_iff' _ List.shortlex_def

instance ShortLex : LinearOrder (Word Gen) := linearOrderOfSTO (List.Shortlex (α := Gen) (· < ·))

instance : LT (Word Gen) where
  lt := List.Shortlex (α := Gen) (· < ·)

instance : LE (Word Gen) where
  le := List.Shortlex (α := Gen) (· < ·)

#synth LinearOrder (Word Gen)
#synth LT (Word Gen)
#synth LE (Word Gen)


lemma f_iff (x y : Gen) : x < y ↔ f x < f y := by
  constructor
  · exact fun a ↦ (fun {n} {a b} ↦ Fin.castSucc_lt_castSucc_iff.mp) a
  · exact fun a ↦ lt_of_lt_of_eq a rfl

instance : ReductionOrder Gen where
  wf := by
    refine { wf := ?_ }
    apply List.Shortlex.wf
    have : WellFounded (α := Gen) (· < ·) := by
      refine (Function.Surjective.wellFounded_iff (r := (· < ·)) (s := (· < ·)) f_sur
      (fun {x y} ↦ f_iff x y)).mpr ?_
      exact wellFounded_lt
    exact Subrelation.wf (fun {x y} a ↦ a) this
  tiₗ := by
    intro u v w huv
    cases huv with
    | inl h_eq =>
      rw [h_eq]
    | inr h_le =>
      have : _ := (List.shortlex_def (α := Gen) (r := (· < ·)) (s := u) (t := v)).mp h_le
      cases this with
      | inl h =>
        have h : (w ++ u).length < (w ++ v).length := by
          rw [List.length_append, List.length_append]
          exact Nat.add_lt_add_left h (length w)
        refine Or.inr ?_
        apply List.shortlex_def.mpr
        exact Or.inl h
      | inr h =>
        have h_len : (w ++ u).length = (w ++ v).length := by
          have : u.length = v.length := h.1
          rw [List.length_append, List.length_append]
          exact Nat.add_left_cancel_iff.mpr this
        have h_lex : List.Lex (fun x1 x2 ↦ x1 < x2) (w ++ u) (w ++ v) := by
          apply List.Lex.append_left
          exact h.2
        refine Or.inr ?_
        apply List.shortlex_def.mpr
        apply Or.intro_right
        exact ⟨h_len, h_lex⟩
  tiᵣ := by
    intro u v w huv
    cases huv with
    | inl h_eq => rw [h_eq]
    | inr h_le =>
      refine Or.inr ?_
      apply List.shortlex_def.mpr
      cases (List.shortlex_def (α := Gen) (r := (· < ·))).mp h_le with
      | inl h =>
        refine Or.inl ?_
        rw [List.length_append, List.length_append]
        exact Nat.add_lt_add_right h (length w)
      | inr h =>
        refine Or.inr ?_
        constructor
        · rw [List.length_append, List.length_append]
          simp [h.1]
        · induction u generalizing v with
          | nil =>
            have : v = [] := by
              simp only [length_nil] at h
              exact List.eq_nil_of_length_eq_zero (Eq.symm h.1)
            rw [this] at h
            contradiction
          | cons x u' ih =>
            have hv : ∃ y : Gen, ∃ v' : Word Gen, v = y :: v' := by
              apply List.exists_cons_of_length_pos
              rw [←h.1]
              exact Nat.zero_lt_succ u'.length
            obtain ⟨y, v', hv⟩ := hv
            have h_len : u'.length = v'.length := by
              rw [hv] at h
              simp_all
            rw [hv] at h
            rw [hv]
            cases List.cons_lex_cons_iff.mp h.2 with
            | inl hxy =>
              apply List.cons_lex_cons_iff.mpr
              exact Or.inl hxy
            | inr hxy =>
              apply List.cons_lex_cons_iff.mpr
              refine Or.inr ?_
              constructor
              · exact hxy.1
              · exact ih v' (List.Shortlex.of_lex h_len hxy.2) ⟨h_len, hxy.2⟩


-- words in rules
def aa_inv : Word Gen := [a, a_inv]
def a_inva : Word Gen := [a_inv, a]
def bb_inv : Word Gen := [b, b_inv]
def b_invb : Word Gen := [b_inv, b]
def ab : Word Gen := [a, b]
def ba : Word Gen := [b, a]
def ε : Word Gen := []

-- rules
def r₁ : Rule Gen := MakeRule aa_inv ε (ne_of_beq_false rfl)
def r₂ : Rule Gen := MakeRule a_inva ε (ne_of_beq_false rfl)
def r₃ : Rule Gen := MakeRule bb_inv ε (ne_of_beq_false rfl)
def r₄ : Rule Gen := MakeRule b_invb ε (ne_of_beq_false rfl)
def r₅ : Rule Gen := MakeRule ab ba (ne_of_beq_false rfl)

def R : List (Rule Gen) := [r₁, r₂, r₃, r₄, r₅]

--attribute [-instance] List.instLinearOrder

#eval! OneStepKnuthBendix R

#eval! List.flatMap (fun r => CheckOverlaps r (OneStepKnuthBendix R)) (OneStepKnuthBendix R)

#eval! KnuthBendix R

end Example1

section Example2

-- alphabet
inductive Gen where
  | a
  | b
  deriving DecidableEq, Repr

abbrev a : Gen := Gen.a
abbrev b : Gen := Gen.b

-- order on alphabet
def f' : Gen → Fin 2
  | .a => 0
  | .b => 1

lemma f_inj' : Function.Injective f' := by
  intro x y h_eq
  unfold f' at h_eq
  grind

def g' : Fin 2 → Gen
  | 0 => .a
  | 1 => .b


lemma f_sur' : Function.Surjective f' := by
  refine Function.HasRightInverse.surjective ?_
  use g'
  intro x
  unfold f'
  unfold g'
  grind

instance : LinearOrder Gen := LinearOrder.lift' f' f_inj'

-- ShortLex order on words
instance : IsStrictTotalOrder (Word Gen) (List.Shortlex (· < ·)) where
 trans := by
  intro a b c hab hbc
  by_cases h_eq_ab : a = b
  · rw [h_eq_ab]
    exact hbc
  · by_cases h_eq_bc : b = c
    · rw [←h_eq_bc]
      exact hab
    · apply List.shortlex_def.mpr
      cases List.shortlex_def.mp hab with
      | inl le_ab =>
        cases List.shortlex_def.mp hbc with
        | inl le_bc =>
          refine Or.inl (Nat.lt_trans le_ab le_bc)
        | inr h =>
          rw [h.1] at le_ab
          exact Or.inl le_ab
      | inr h =>
        cases List.shortlex_def.mp hbc with
        | inl le_bc =>
          rw [h.1]
          refine Or.inl le_bc
        | inr h' =>
          refine Or.inr ?_
          constructor
          · rw [←h.1] at h'
            exact h'.1
          · apply List.lex_trans ?_ h.2 h'.2
            exact fun {x y z} a a_1 ↦ Std.lt_trans a a_1

instance : DecidableRel (List.Shortlex (α := Gen) (· < ·)) := by
  intro u v
  apply decidable_of_iff' _ List.shortlex_def

instance ShortLex : LinearOrder (Word Gen) := linearOrderOfSTO (List.Shortlex (α := Gen) (· < ·))

/-
instance : LT (Word Gen) where
  lt := List.Shortlex (α := Gen) (· < ·)

instance : LE (Word Gen) where
  le := List.Shortlex (α := Gen) (· < ·)
-/

#synth LinearOrder (Word Gen)
#synth LT (Word Gen)
#synth LE (Word Gen)

lemma f_iff' (x y : Gen) : x < y ↔ f' x < f' y := by
  constructor
  · exact fun a ↦ (fun {n} {a b} ↦ Fin.castSucc_lt_castSucc_iff.mp) a
  · exact fun a ↦ lt_of_lt_of_eq a rfl

instance : ReductionOrder Gen where
  wf := by
    refine { wf := ?_ }
    apply List.Shortlex.wf
    have : WellFounded (α := Gen) (· < ·) := by
      refine (Function.Surjective.wellFounded_iff (r := (· < ·)) (s := (· < ·)) f_sur'
      (fun {x y} ↦ f_iff' x y)).mpr ?_
      exact wellFounded_lt
    exact Subrelation.wf (fun {x y} a ↦ a) this
  tiₗ := by
    intro u v w huv
    cases huv with
    | inl h_eq =>
      rw [h_eq]
    | inr h_le =>
      have : _ := (List.shortlex_def (α := Gen) (r := (· < ·)) (s := u) (t := v)).mp h_le
      cases this with
      | inl h =>
        have h : (w ++ u).length < (w ++ v).length := by
          rw [List.length_append, List.length_append]
          exact Nat.add_lt_add_left h (length w)
        refine Or.inr ?_
        apply List.shortlex_def.mpr
        exact Or.inl h
      | inr h =>
        have h_len : (w ++ u).length = (w ++ v).length := by
          have : u.length = v.length := h.1
          rw [List.length_append, List.length_append]
          exact Nat.add_left_cancel_iff.mpr this
        have h_lex : List.Lex (fun x1 x2 ↦ x1 < x2) (w ++ u) (w ++ v) := by
          apply List.Lex.append_left
          exact h.2
        refine Or.inr ?_
        apply List.shortlex_def.mpr
        apply Or.intro_right
        exact ⟨h_len, h_lex⟩
  tiᵣ := by
    intro u v w huv
    cases huv with
    | inl h_eq => rw [h_eq]
    | inr h_le =>
      refine Or.inr ?_
      apply List.shortlex_def.mpr
      cases (List.shortlex_def (α := Gen) (r := (· < ·))).mp h_le with
      | inl h =>
        refine Or.inl ?_
        rw [List.length_append, List.length_append]
        exact Nat.add_lt_add_right h (length w)
      | inr h =>
        refine Or.inr ?_
        constructor
        · rw [List.length_append, List.length_append]
          simp [h.1]
        · induction u generalizing v with
          | nil =>
            have : v = [] := by
              simp only [length_nil] at h
              exact List.eq_nil_of_length_eq_zero (Eq.symm h.1)
            rw [this] at h
            contradiction
          | cons x u' ih =>
            have hv : ∃ y : Gen, ∃ v' : Word Gen, v = y :: v' := by
              apply List.exists_cons_of_length_pos
              rw [←h.1]
              exact Nat.zero_lt_succ u'.length
            obtain ⟨y, v', hv⟩ := hv
            have h_len : u'.length = v'.length := by
              rw [hv] at h
              simp_all
            rw [hv] at h
            rw [hv]
            cases List.cons_lex_cons_iff.mp h.2 with
            | inl hxy =>
              apply List.cons_lex_cons_iff.mpr
              exact Or.inl hxy
            | inr hxy =>
              apply List.cons_lex_cons_iff.mpr
              refine Or.inr ?_
              constructor
              · exact hxy.1
              · exact ih v' (List.Shortlex.of_lex h_len hxy.2) ⟨h_len, hxy.2⟩

-- words in rules
def a2 : Word Gen := [a, a]
def b3 : Word Gen := [b, b, b]
def ab3 : Word Gen := [a, b, a, b, a, b]
def ε : Word Gen := []


-- rules
def r₁ : Rule Gen := MakeRule a2 ε (ne_of_beq_false rfl)
def r₂ : Rule Gen := MakeRule b3 ε (ne_of_beq_false rfl)
def r₃ : Rule Gen := MakeRule ab3 ε (ne_of_beq_false rfl)

def R : List (Rule Gen) := [r₁, r₂, r₃]

def eliminate_duplicate_rec (R R' : List (Rule Gen)) : List (Rule Gen) :=
  match R with
  | [] => R'
  | r :: R =>
    if r ∈ R' then eliminate_duplicate_rec R R' else eliminate_duplicate_rec R (r :: R')

def eliminate_duplicate (R : List (Rule Gen)) : List (Rule Gen) :=
  eliminate_duplicate_rec R []

#eval! OneStepKnuthBendix R

#eval! List.flatMap (fun r => CheckOverlaps r R) R

#eval! eliminate_duplicate (List.flatMap (fun r => CheckOverlaps r (OneStepKnuthBendix R)) (OneStepKnuthBendix R))

#eval! (eliminate_duplicate (KnuthBendix R))



end Example2
