module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A]

--DEFINITION OF ONE STEP REDUCTION
--check if any LHS of a rule in R is a prefix of w. If yes returns reduced word otherwise returns none
def CheckPrefix (w : Word A) (R : List (Rule A)) : Option (Word A) :=
  match R with
  | [] => none
  | r :: RS =>
    match List.isPrefixOf? r.lhs w with
    | none => CheckPrefix w RS
    | some w' => some (r.rhs ++ w')


-- if any rule is a prefix of "b" returns reduced word by that rule otherwise makes a recursive call with moving one generator from b to a (returns a if b is empty)
def ReduceOnce_rec (a b : Word A) (R : List (Rule A)) : Word A :=
  match b with
  | [] => a
  | x :: b' =>
    match CheckPrefix b R with
    | none => ReduceOnce_rec (List.concat a x) b' R
    | some b'' => a ++ b''

--reduces a word with the first rule that applies from left to right (if any), otherwise returns original word
def ReduceOnce (w : Word A) (R : List (Rule A)) : Word A := ReduceOnce_rec [] w R


--PROOF THAT REDUCEONCE PRODUCES A SMALLER WORD

lemma IsPrefixDec (w : Word A) (r : Rule A) (h : List.isPrefixOf? r.lhs w = some u) :
w = r.lhs ++ u
:= by
  simp at h
  exact Eq.symm h

lemma CheckPrefix_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) :
CheckPrefix w R ≤ w := by
  induction R with
  | nil => unfold CheckPrefix; trivial
  | cons r RS ih =>
  unfold CheckPrefix
  cases h : List.isPrefixOf? r.lhs w with
  | none =>
  exact le_of_le_of_eq ih rfl
  | some u =>
  simp
  have hw : w = r.lhs ++ u := IsPrefixDec w r h
  rw [hw]
  refine tir_leq r.rhs r.lhs u ?_
  exact Std.le_of_lt r.rhs_lt_lhs

lemma ReduceOnce_rec_leq [ReductionOrder A] (b : Word A) (R : List (Rule A)) :
∀ a : Word A, ReduceOnce_rec a b R ≤ (a ++ b) := by
  induction b with
  | nil => simp; unfold ReduceOnce_rec; exact Std.IsPreorder.le_refl
  | cons x b' ih =>
  intro a
  unfold ReduceOnce_rec
  cases hb : CheckPrefix (x :: b') R with
  | none =>
  simp
  specialize ih (a ++ [x])
  have : a ++ x :: b' = a ++ [x] ++ b' := by exact List.append_cons a x b'
  exact le_of_le_of_eq ih (id (Eq.symm this))
  | some b'' =>
  simp
  have h := CheckPrefix_leq (x :: b') R
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
def Reduce [ReductionOrder A] (w : Word A) (R : List (Rule A)) : Word A :=
  if h_reduceonce_eq : ReduceOnce w R = w then
    w
  else
    Reduce (ReduceOnce w R) R
termination_by w
decreasing_by
exact ReduceOnce_le w R h_reduceonce_eq
