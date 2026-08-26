module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A]

--DEFINITION OF ONE STEP REDUCTION
--check if any LHS of a rule in R is a prefix of w. If yes returns reduced word otherwise returns none
def Reduce_if_IsPrefix (w : Word A) (R : List (Rule A)) : Option (Word A) :=
  match R with
  | [] => none
  | r :: RS =>
    match List.isPrefixOf? r.lhs w with
    | none => Reduce_if_IsPrefix w RS
    | some w' => some (r.rhs ++ w')


-- if any rule is a prefix of "b" returns reduced word by that rule otherwise makes a recursive call with moving one generator from b to a (returns a if b is empty)
def ReduceOnce_rec (a b : Word A) (R : List (Rule A)) : Word A :=
  match b with
  | [] => a
  | x :: b' =>
    match Reduce_if_IsPrefix b R with
    | none => ReduceOnce_rec (List.concat a x) b' R
    | some b'' => a ++ b''

--reduces a word with the first rule that applies from left to right (if any)
--otherwise returns original word
def ReduceOnce (w : Word A) (R : List (Rule A)) : Word A := ReduceOnce_rec [] w R


--PROOF THAT "ReduceOnce" PRODUCES A SMALLER WORD
lemma Reduce_if_IsPrefix_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) :
  Reduce_if_IsPrefix w R ≤ w := by
    induction R with
    | nil => unfold Reduce_if_IsPrefix; trivial
    | cons r RS ih =>
    unfold Reduce_if_IsPrefix
    cases h : List.isPrefixOf? r.lhs w with
    | none =>
    exact le_of_le_of_eq ih rfl
    | some u =>
    simp only [Option.some_le_some]
    have hw : w = r.lhs ++ u := Eq.symm (List.isPrefixOf?_eq_some_iff_append_eq.1 h)
    rw [hw]
    refine tir_leq r.rhs r.lhs u ?_
    exact Std.le_of_lt r.rhs_lt_lhs

lemma ReduceOnce_rec_leq [ReductionOrder A] (b : Word A) (R : List (Rule A)) :
  ∀ a : Word A, ReduceOnce_rec a b R ≤ (a ++ b) := by
    induction b with
    | nil => simp only [List.append_nil]; unfold ReduceOnce_rec; exact Std.IsPreorder.le_refl
    | cons x b' ih =>
    intro a
    unfold ReduceOnce_rec
    cases hb : Reduce_if_IsPrefix (x :: b') R with
    | none =>
    simp only [List.concat_eq_append]
    specialize ih (a ++ [x])
    have : a ++ x :: b' = a ++ [x] ++ b' := by exact List.append_cons a x b'
    exact le_of_le_of_eq ih (id (Eq.symm this))
    | some b'' =>
    have h := Reduce_if_IsPrefix_leq (x :: b') R
    rw [hb] at h
    exact til_leq b'' (x :: b') a h

--ReduceOnce w R ≤ w
lemma ReduceOnce_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) : ReduceOnce w R ≤ w := by
  unfold ReduceOnce
  apply ReduceOnce_rec_leq w

--ReduceOnce w R < w if they are not equal
lemma ReduceOnce_le [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnce w R ≠ w)
: ReduceOnce w R < w := by
  unfold ReduceOnce
  apply lt_of_le_of_ne (ReduceOnce_leq w R) h_neq


-- REDUCTION BY ITERATION

--iterates ReduceOnce n times
def ReduceNat (w : Word A) (R : List (Rule A)) (n : Nat) : Word A :=
  Nat.iterate (ReduceOnce · R) n w

instance [ReductionOrder A] : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

--iterates ReduceOnce as long as the output is changing
def CanonicalReduction [ReductionOrder A] (w : Word A) (R : List (Rule A)) : Word A :=
  if h_reduceonce_eq : ReduceOnce w R = w then
    w
  else
    CanonicalReduction (ReduceOnce w R) R
termination_by w
decreasing_by
exact ReduceOnce_le w R h_reduceonce_eq
