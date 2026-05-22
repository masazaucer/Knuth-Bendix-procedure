module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

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
def ReduceOnceList (w : Word A) (R : List (Rule A)) : Word A :=
  match R with
  | [] => w
  | r :: R' =>
  let w' := ReduceOnce w r
  if w' = w then ReduceOnceList w R' else w'

--LEMMAS ABOUT ONE STEP REDUCTION
-- reducing a word by a rule produces a smaller (or equal) word
lemma ReduceOnce_leq [ReductionOrder A] (w : Word A) (r : Rule A) : ReduceOnce w r ≤ w := by
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
lemma ReduceOnceList_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) : ReduceOnceList w R ≤ w := by
  induction R with
  | nil =>
    unfold ReduceOnceList
    trivial
  | cons r R' ih =>
    unfold ReduceOnceList
    by_cases h_reduce : ReduceOnce w r = w
    · simp [h_reduce]
      exact ih
    · simp [h_reduce]
      exact ReduceOnce_leq w r

lemma ReduceOnceList_le [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_neq : ReduceOnceList w R ≠ w) : ReduceOnceList w R < w := by
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


--defines the normal form of w with respect to R as the result of iterating ReduceOnceList until it stabilizes
def NormalForm (w : Word A) (R : List (Rule A)) : Word A := Reduce w R
