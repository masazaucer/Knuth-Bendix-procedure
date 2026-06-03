module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

/--/
-- Returns some u if w = r.lhs ++ u, otherwise returns none
def IsPrefix (w : Word A) (r : Rule A) : Option (Word A) := List.getRest w r.lhs

-- LEMMAS ABOUT ISPREFIX
-- In case of an empty word IsPrefix returns none
lemma IsPrefixEmpty_eq_none (s : Rule A) : IsPrefix [] s = none := by
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
  rw [IsPrefixEmpty_eq_none] at h
  contradiction

-- decomposes w as v ++ u if v is a prefix of w
lemma getRest_eq_concat (w v : Word A) (h : List.getRest w v = some u) : w = v ++ u := by
  induction v generalizing w with
  | nil =>
    simp [List.getRest] at h
    trivial
  | cons a v' ih =>
    unfold List.getRest at h
    cases w with
    | nil =>
      contradiction
    | cons b w' =>
      simp at h
      rw [h.1]
      specialize ih w' h.2
      simp_all


-- decomposes w = r.lhs ++ u if IsPrefix w r = some u
lemma IsPrefixDec (w : Word A) (r : Rule A) (h : IsPrefix w r = some u) : w = r.lhs ++ u := by
  unfold IsPrefix at h
  exact getRest_eq_concat w r.lhs h

-- Returns w reduced by r if possible, otherwise returns w
def ReduceOnce (w : Word A) (r : Rule A) : Word A := match w with
| [] => []
| a :: w' =>
  match IsPrefix w r with
  | some u => r.rhs ++ u
  | none => a :: ReduceOnce w' r


--reduces a word by the first rule in R that applies, if any (otherwise returns w)
def ReduceOnceList' (w : Word A) (R : List (Rule A)) : Word A :=
  match R with
  | [] => w
  | r :: R' =>
  let w' := ReduceOnce w r
  if w' = w then ReduceOnceList' w R' else w'


--LEMMAS ABOUT ONE STEP REDUCTION
-- reducing a word by a rule produces a smaller (or equal) word
lemma ReduceOnce_leq' [ReductionOrder A] (w : Word A) (r : Rule A) : ReduceOnce w r ≤ w := by
  induction w with
  | nil => simp [ReduceOnce]
  | cons a w' ih =>
    simp only [ReduceOnce]
    cases h_isPrefix : IsPrefix (a :: w') r with
    | none =>
    simp
    have h1 : [a] ++ ReduceOnce w' r ≤ [a] ++ w' := by apply til_leq (ReduceOnce w' r) w' [a] ih
    --ReductionOrder.tiₗ (ReduceOnce w' r) w' [a] ih
    exact le_of_le_of_eq h1 rfl
    | some u =>
    simp
    have hw : (a :: w') = r.lhs ++ u := IsPrefixDec (a :: w') r h_isPrefix
    rw [hw]
    apply tir_leq r.rhs r.lhs u (le_of_lt r.rhs_lt_lhs)

-- reducing a word by a list of rules produces a smaller (or equal) word
lemma ReduceOnceList_leq' [ReductionOrder A] (w : Word A) (R : List (Rule A)) : ReduceOnceList' w R ≤ w := by
  induction R with
  | nil =>
    unfold ReduceOnceList'
    trivial
  | cons r R' ih =>
    unfold ReduceOnceList'
    by_cases h_reduce : ReduceOnce w r = w
    · simp [h_reduce]
      exact ih
    · simp [h_reduce]
      exact ReduceOnce_leq' w r

lemma ReduceOnceList_le' [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnceList' w R ≠ w) : ReduceOnceList' w R < w := by
  apply lt_of_le_of_ne (ReduceOnceList_leq' w R) h_neq
-/

--check if any LHS of a rule in R is a suffix of w. If yes returns reduced word otherwise returns none
def CheckSuffix (w : Word A) (R : List (Rule A)) : Option (Word A) :=
  match R with
  | [] => none
  | r :: RS =>
    match List.isSuffixOf? r.lhs w with
    | none => CheckSuffix w RS
    | some w' => some (w' ++ r.rhs)

-- if any rule is a suffix of "a" returns reduced word by that rule otherwise makes a recursive call with moving one generator from b to a (returns a if b is empty)
def ReduceOnceList_rec (a b : Word A) (R : List (Rule A)) : Word A :=
  match b with
  | [] => a
  | x :: b' =>
    let a' := CheckSuffix a R
    match a' with
    | none => ReduceOnceList_rec (List.concat a x) b' R
    | some a'' => a'' ++ b


def ReduceOnceList (w : Word A) (R : List (Rule A)) : Word A := ReduceOnceList_rec [] w R

lemma IsSuffix_eq_concat (v w : Word A) (h_suff : List.isSuffixOf? v w = some u) : w = u ++ v := by
  simp at h_suff
  exact Eq.symm h_suff


lemma IsSuffixDec (w : Word A) (r : Rule A) (h : List.isSuffixOf? r.lhs w = some u) : w = u ++ r.lhs :=
  by
  simp at h
  exact Eq.symm h

lemma CheckSuffix_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) : CheckSuffix w R ≤ w := by
  induction R with
  | nil => unfold CheckSuffix; trivial
  | cons r RS ih =>
  unfold CheckSuffix
  cases h : List.isSuffixOf? r.lhs w with
  | none =>
  exact le_of_le_of_eq ih rfl
  | some u =>
  simp
  have hw : w = u ++ r.lhs := IsSuffixDec w r h
  rw [hw]
  refine til_leq r.rhs r.lhs u ?_
  exact Std.le_of_lt r.rhs_lt_lhs



lemma ReduceOnceList_rec_leq [ReductionOrder A] (b : Word A) (R : List (Rule A)) : ∀ a : Word A, ReduceOnceList_rec a b R ≤ (a ++ b) := by
  induction b with
  | nil => simp; unfold ReduceOnceList_rec; exact Std.IsPreorder.le_refl
  | cons x b' ih =>
  unfold ReduceOnceList_rec
  intro a
  cases ha : CheckSuffix a R with
  | none =>
  simp
  specialize ih (a ++ [x])
  have : a ++ x :: b' = a ++ [x] ++ b' := by exact List.append_cons a x b'
  rw [this]
  exact le_of_le_of_eq ih rfl
  | some a' =>
  simp
  have h := CheckSuffix_leq a R
  rw [ha] at h
  simp at h
  exact tir_leq a' a (x :: b') h

lemma ReduceOnceList_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) : ReduceOnceList w R ≤ w := by
  unfold ReduceOnceList
  apply ReduceOnceList_rec_leq w

lemma ReduceOnceList_le [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnceList w R ≠ w) : ReduceOnceList w R < w := by
  unfold ReduceOnceList
  apply lt_of_le_of_ne (ReduceOnceList_leq w R) h_neq


-- REDUCTION BY ITERATION AND NORMAL FORMS
--iterates ReduceOnceList n times
def ReduceNat (w : Word A) (R : List (Rule A)) (n : Nat) : Word A :=
  Nat.iterate (ReduceOnceList · R) n w

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

--iterates ReduceOnceList as long as the output is changing
def Reduce [ReductionOrder A] (w : Word A) (R : List (Rule A)) : Word A :=
  if h_reduceonce_eq : ReduceOnceList w R = w then
    w
  else
    Reduce (ReduceOnceList w R) R
termination_by w
decreasing_by
exact ReduceOnceList_le w R h_reduceonce_eq
