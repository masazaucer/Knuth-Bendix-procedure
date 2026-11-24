module

public import KnuthBendix.Basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A]

section ReduceOnce

open Array

--DEFINITION OF ONE STEP REDUCTION

--if any LHS of a rule in R is a prefix of w returns reduced word otherwise returns none
def Reduce? (R : Array (Rule A)) (w : Word A) : Option (Word A) :=
  findSome? (fun r ↦ Option.map (fun u ↦ r.rhs ++ u) (List.isPrefixOf? r.lhs w)) R

-- if any rule is a prefix of "b" returns reduced word by that rule otherwise makes a recursive call
-- with moving one generator from b to a (returns a if b is empty)
def ReduceOnce_rec' (a b : Word A) (R : Array (Rule A)) : Word A :=
  match b with
  | [] => a.reverse
  | x :: b' =>
    match Reduce? R b with
    | none => ReduceOnce_rec' (x :: a) b' R
    | some u => a.reverse ++ u

--reduces a word with the first rule that applies from left to right (if any)
--otherwise returns original word
def ReduceOnce (R : Array (Rule A)) (w : Word A) : Word A := ReduceOnce_rec' [] w R



--LEMMAS ABOUT "Reduce?"
variable (v w : Word A) (R : Array (Rule A))

lemma isPrefixOf?_eq_some_iff :
    (∃u : Word A, List.isPrefixOf? v w = some u) ↔ v <+: w := by
  constructor
  · intro ⟨u, hu⟩
    exact ⟨u, List.isPrefixOf?_eq_some_iff_append_eq.mp hu⟩
  · intro ⟨u, hu⟩
    exact ⟨u, List.isPrefixOf?_eq_some_iff_append_eq.mpr hu⟩

lemma isPrefixOf?_eq_none_iff :
    List.isPrefixOf? v w = none ↔ ¬(v <+: w) := by
  have : List.isPrefixOf? v w = none ↔ ¬(∃u : Word A, List.isPrefixOf? v w = some u) := by
    apply Iff.trans Option.eq_none_iff_forall_ne_some (by simp)
  apply Iff.trans this (not_congr (isPrefixOf?_eq_some_iff v w))

-- If w cannot be reduced by (r :: R), then it cannot be reduced by R either
lemma Reduce?_none_succ (r : Rule A) :
    Reduce? (R.push r) w = none → Reduce? R w = none := by
  intro h
  unfold Reduce? at *
  rw [Array.findSome?_eq_none_iff] at *
  intro x h_mem
  exact h x (Array.mem_push_of_mem r h_mem)


-- Reduce? returns none iff no rule in R is a prefix of w
lemma Reduce?_none_iff :
    Reduce? R w = none ↔ ∀ r ∈ R, ¬ r.lhs <+: w := by
  unfold Reduce?
  conv =>
    lhs
    rw [Array.findSome?_eq_none_iff]
    simp
  constructor
  · intro h r h_mem
    exact (isPrefixOf?_eq_none_iff r.lhs w).mp (h r h_mem)
  · intro h r h_mem
    specialize h r h_mem
    exact (isPrefixOf?_eq_none_iff r.lhs w).mpr h


-- Reduce? returns some iff there is a rule in R whose lhs is a prefix of w
lemma Reduce?_some_iff :
    (∃ u, Reduce? R w = some u) ↔ ∃ r ∈ R, r.lhs <+: w := by
  apply not_iff_not.mp
  push Not
  conv =>
    lhs
    rw [←Option.eq_none_iff_forall_ne_some]
  exact Reduce?_none_iff w R


section
variable {w} {w' : Word A} {R}

-- If Reduce? returns some w' then w and w' differ by changing r.lhs to r.rhs
lemma append_eq_of_Reduce?_eq_some (h : Reduce? R w = some w') :
    ∃ r ∈ R, ∃ u : Word A, w = r.lhs ++ u ∧ w' = r.rhs ++ u := by
  unfold Reduce? at h
  let ⟨R₁, r, R₂, h_eq, h⟩ := Array.findSome?_eq_some_iff.mp h
  use r
  constructor
  · grind
  · let ⟨u, hu⟩ := Option.map_eq_some_iff.mp h.1
    use u
    constructor
    · exact Eq.symm (List.append_eq_of_isPrefixOf?_eq_some hu.1)
    · exact Eq.symm hu.2


-- If Reduce? returns some w' then there is r ∈ R s.t. r.lhs and r.rhs are prefixes of w and w' respectively
lemma rule_prefix_of_Reduce?_eq_some (h : Reduce? R w = some w') :
    ∃ r ∈ R, r.lhs <+: w ∧ r.rhs <+: w' := by
  obtain ⟨r, r_mem, u, hu⟩ := append_eq_of_Reduce?_eq_some h
  use r
  exact ⟨r_mem, ⟨u, Eq.symm hu.1⟩, ⟨u, Eq.symm hu.2⟩⟩

-- The word obtained by Reduce? is strictly smaller than w
lemma Reduce?_le [ReductionOrder A] (h : Reduce? R w = some w') : w' < w := by
  obtain ⟨r, h_mem, u, h⟩ := append_eq_of_Reduce?_eq_some h
  rw [h.1, h.2]
  refine tir_le ?_
  exact r.rhs_lt_lhs

end

--LEMMAS ABOUT "ReduceOnce"
variable {w} {R} {a b : Word A}

lemma ReduceOnce_rec_eq_append (a b : Word A) :
    ReduceOnce_rec' a b R = a.reverse ++ ReduceOnce_rec' [] b R := by
  induction b generalizing a with
  | nil =>
    unfold ReduceOnce_rec'
    simp
  | cons x b ih =>
    unfold ReduceOnce_rec'
    cases h : Reduce? R (x :: b) with
    | none =>
      rw [ih (x :: a), ih [x]]
      simp
    | some u =>
      simp

lemma ReduceOnce_rec_eq_not_pref [ReductionOrder A] :
    ReduceOnce_rec' [] w R = w → ∀ r ∈ R, ¬ r.lhs <+: w := by
  intro h_eq r h_mem
  by_contra h_pref
  unfold ReduceOnce_rec' at h_eq
  induction w with
  | nil =>
    have h_empty : _ := List.eq_nil_of_prefix_nil h_pref
    have h_nonempty : _ := lhsNonempty r
    contradiction
  | cons x w' ih =>
    simp at h_eq
    obtain ⟨u, hu⟩ := (Reduce?_some_iff (x :: w') R).mpr ⟨r, ⟨h_mem, h_pref⟩⟩
    simp [hu] at h_eq
    have : u < (x :: w') := Reduce?_le hu
    simp_all

lemma ReduceOnce_rec_def_of_not_prefix [ReductionOrder A] {x : A}
    (h : ∀ r ∈ R, ¬ r.lhs <+: (x :: b)) :
    ReduceOnce_rec' a (x :: b) R = ReduceOnce_rec' (x :: a) b R := by
  have : Reduce? R (x :: b) = none := by exact (Reduce?_none_iff (x :: b) R).mpr h
  conv =>
    lhs
    unfold ReduceOnce_rec'
  simp [this]


-- ReduceOnce_rec' returns the same word iff no r.lhs is a subword of w
lemma ReduceOnce_rec_eq_iff [ReductionOrder A] :
    ReduceOnce_rec' [] w R = w ↔ ∀ r ∈ R, ¬ r.lhs <:+: w := by
  induction w with
  | nil =>
    unfold ReduceOnce_rec'
    simp only [List.reverse_nil, List.infix_nil, true_iff]
    intro r h_mem
    exact lhsNonempty r
  | cons x b' ih =>
    constructor
    · intro h_eq r r_mem
      have h_pref : _ := ReduceOnce_rec_eq_not_pref h_eq
      have : ReduceOnce_rec' [] b' R = b' := by
        rw [ReduceOnce_rec_def_of_not_prefix h_pref, ReduceOnce_rec_eq_append] at h_eq
        simp_all
      have h_infix' : _ := ih.mp this
      by_contra h_infix
      cases List.infix_cons_iff.mp h_infix with
      | inl hl =>
        specialize h_pref r r_mem
        contradiction
      | inr hr =>
        specialize h_infix' r r_mem
        contradiction
    · intro h
      have h_infix : ∀ r ∈ R, ¬ r.lhs <:+: b' := by
        intro r r_mem
        specialize h r r_mem
        by_contra h_infix
        have : _ := List.infix_cons h_infix (a := x)
        contradiction
      have h_pref : ∀ r ∈ R, ¬ r.lhs <+: (x :: b') := by
        intro r r_mem
        by_contra h_pref
        have : r.lhs <:+: (x :: b') := by exact List.IsPrefix.isInfix h_pref
        specialize h r r_mem
        contradiction
      rw [ReduceOnce_rec_def_of_not_prefix h_pref, ReduceOnce_rec_eq_append, ih.mpr h_infix]
      simp


-- ReduceOnce returns same word iff no r.lhs is a subword of w
lemma ReduceOnce_eq_iff [ReductionOrder A] :
    ReduceOnce R w = w ↔ ∀ r ∈ R, ¬ r.lhs <:+: w := by
  unfold ReduceOnce
  exact ReduceOnce_rec_eq_iff

--If there is r ∈ R s.t. r.lhs is subword of w, then ReduceOnce w ≠ w
lemma ReduceOnce_neq_of_IsInfix [ReductionOrder A]
    (h_infix : ∃ r ∈ R, r.lhs <:+: w) : ReduceOnce R w ≠ w := by
  have : ¬ ∀ r ∈ R, ¬ r.lhs <:+: w := by grind
  unfold ReduceOnce
  exact (not_congr (ReduceOnce_rec_eq_iff)).mpr this


lemma rule_infix_ReduceOnce_append_of_lhs_infix [ReductionOrder A] {w : Word A} {R : Array (Rule A)}
    (h : ∃ r ∈ R, r.lhs <:+: w) :
    ∃ r ∈ R, ∃ v u : Word A, w = v ++ r.lhs ++ u ∧ (ReduceOnce R w) = v ++ r.rhs ++ u := by
  obtain ⟨r, r_mem, h_infix⟩ := h
  induction w with
  | nil =>
    have : r.lhs = [] := by exact List.eq_nil_of_infix_nil h_infix
    have : r.lhs ≠ [] := by exact lhsNonempty r
    contradiction
  | cons x w' ih =>
    let w := x :: w'
    by_cases h_pref : ∃ r' ∈ R, r'.lhs <+: (x :: w')
    · obtain ⟨u, hu⟩ := (Reduce?_some_iff (x :: w') R).mpr h_pref
      obtain ⟨r',⟨r_mem', ⟨v, hv⟩⟩⟩ := append_eq_of_Reduce?_eq_some hu
      have h_eq : ReduceOnce R (x :: w') = u := by
        unfold ReduceOnce
        unfold ReduceOnce_rec'
        rw [hu]
        simp
      use r'
      constructor
      · exact r_mem'
      · use []
        use v
        rw [h_eq]
        simp only [List.nil_append]
        exact hv
    · have h' : ∀ r'' ∈ R, ¬(r''.lhs <+: (x :: w')) := by
        push Not at h_pref
        exact h_pref
      have h_pref' : r.lhs <:+: w' := by
        specialize h' r r_mem
        have : r.lhs <+: x :: w' ∨ r.lhs <:+: w' := List.infix_cons_iff.mp h_infix
        grind
      obtain ⟨r', ⟨r_mem', ⟨v, u, h⟩⟩⟩ := ih h_pref'
      use r'
      constructor
      · exact r_mem'
      · use (x :: v)
        use u
        constructor
        · rw [h.1]
          simp
        · have : ReduceOnce R (x :: w') = x :: ReduceOnce R w' := by
            calc _ = ReduceOnce_rec' [] (x :: w') R := by unfold ReduceOnce; trivial
                _ = ReduceOnce_rec' [x] w' R := by exact ReduceOnce_rec_def_of_not_prefix h'
                _ = [x] ++ ReduceOnce_rec' [] w' R := by exact ReduceOnce_rec_eq_append [x] w'
                _ = x :: ReduceOnce R w' := by exact List.singleton_append
          rw [this, h.2]
          simp

lemma rule_infix_append_of_ReduceOnce_neq [ReductionOrder A]
    (h_neq : ReduceOnce R w ≠ w) :
    ∃r ∈ R, ∃ v u : Word A, w = v ++ r.lhs ++ u ∧ (ReduceOnce R w) = v ++ r.rhs ++ u := by
  have : ∃ r ∈ R, r.lhs <:+: w := by
    have : _ := (not_congr (ReduceOnce_eq_iff)).mp h_neq
    grind
  exact rule_infix_ReduceOnce_append_of_lhs_infix this

lemma rule_infix_ReduceOnce_of_lhs_infix [ReductionOrder A]
    (h : ∃ r ∈ R, r.lhs <:+: w) :
    ∃ r' ∈ R, r'.lhs <:+: w ∧ r'.rhs <:+: ReduceOnce R w := by
  obtain ⟨r, r_mem, v, u, h_append⟩ := rule_infix_ReduceOnce_append_of_lhs_infix h
  use r
  exact ⟨r_mem, ⟨v, u, Eq.symm h_append.1⟩, ⟨v, u, Eq.symm h_append.2⟩⟩



variable (w a)
--PROOF THAT "ReduceOnce" PRODUCES A SMALLER WORD

lemma ReduceOnce_rec_leq [ReductionOrder A] :
    ReduceOnce_rec' a w R ≤ (a.reverse ++ w) := by
  induction w generalizing a with
  | nil => simp only [List.append_nil]; unfold ReduceOnce_rec'; exact le_refl (List.reverse a)
  | cons x b' ih =>
    unfold ReduceOnce_rec'
    cases hb : Reduce? R (x :: b') with
    | none =>
      rw [ReduceOnce_rec_eq_append, List.reverse_cons]
      specialize ih []
      conv =>
        rhs
        rw [←List.singleton_append]
      rw [←List.append_assoc]
      apply ReductionOrder.tiₗ
      exact ih
    | some b'' =>
      refine ReductionOrder.tiₗ b'' (x :: b') (List.reverse a) ?_
      exact le_of_lt (Reduce?_le hb)

--ReduceOnce R w ≤ w
lemma ReduceOnce_leq [ReductionOrder A] : ReduceOnce R w ≤ w := by
  unfold ReduceOnce
  apply ReduceOnce_rec_leq w

--ReduceOnce R w < w if they are not equal
lemma ReduceOnce_le [ReductionOrder A] (h_neq : ReduceOnce R w ≠ w)
: ReduceOnce R w < w := by
  unfold ReduceOnce
  apply lt_of_le_of_ne (ReduceOnce_leq w) h_neq

end ReduceOnce


section CanonicalReduction

variable {w : Word A} {R : Array (Rule A)}
variable [ReductionOrder A]

-- REDUCTION BY ITERATION OF REDUCEONCE

--iterates ReduceOnce n times
def ReduceNat (w : Word A) (R : Array (Rule A)) (n : Nat) : Word A :=
  Nat.iterate (ReduceOnce R) n w

instance [ReductionOrder A] : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

--iterates ReduceOnce as long as the output is changing
def CanonicalReduction [ReductionOrder A] (R : Array (Rule A)) (w : Word A) : Word A :=
  if h_reduceonce_eq : ReduceOnce R w = w then
    w
  else
    CanonicalReduction R (ReduceOnce R w)
termination_by w
decreasing_by
exact ReduceOnce_le w h_reduceonce_eq


-- LEMMAS ABOUT CANONICAL REDUCTION

lemma CanonicalReduction_leq :
CanonicalReduction R w ≤ w := by
  let C : Word A → Prop := fun x ↦ CanonicalReduction R x ≤ x
  apply WellFounded.fix (C := C) ReductionOrder.wf.wf
  intro w ih
  unfold C at *
  specialize ih (ReduceOnce R w)
  unfold CanonicalReduction
  by_cases h_reduceonce_eq : ReduceOnce R w = w
  · simp_all
  · have h_reduceonce_lt : ReduceOnce R w < w := ReduceOnce_le w h_reduceonce_eq
    specialize ih h_reduceonce_lt
    simp_all only [↓reduceDIte, ge_iff_le]
    have h_reduceonce_leq : ReduceOnce R w ≤ w := ReduceOnce_leq w
    exact Std.IsPreorder.le_trans (CanonicalReduction R (ReduceOnce R w)) (ReduceOnce R w) w ih
        h_reduceonce_leq


lemma CR_fix_ReduceOnce :
  ReduceOnce R (CanonicalReduction R w) = CanonicalReduction R w := by
  let C : Word A → Prop := fun x ↦ ReduceOnce R (CanonicalReduction R x) = CanonicalReduction R x
  apply WellFounded.fix (C := C) ReductionOrder.wf.wf
  intro w ih
  unfold C at *
  unfold CanonicalReduction
  by_cases h_reduceonce_eq : ReduceOnce R w = w
  · simp_all
  · have h_reduceonce_lt : ReduceOnce R w < w := ReduceOnce_le w h_reduceonce_eq
    specialize ih (ReduceOnce R w) h_reduceonce_lt
    simp_all

lemma fixpoint_CanonicalReduction_of_ReduceOnce (h : ReduceOnce R w = w) :
  CanonicalReduction R w = w := by
  unfold CanonicalReduction
  rw [h]
  simp

lemma CanonicalReduction_ReduceOnce_eq_CanonicalReduction :
  CanonicalReduction R (ReduceOnce R w) = CanonicalReduction R w := by
  by_cases h_eq : ReduceOnce R w = w
  · rw [h_eq]
  · conv =>
    rhs
    unfold CanonicalReduction
    simp [h_eq]

end CanonicalReduction

section RewriteFromLeft

def RewriteFromLeft_rec [ReductionOrder A] [DecidableEq A] (a b : Word A) (R : Array (Rule A)) : Word A :=
  match b with
  | [] => a.reverse
  | x :: b' =>
    match Reduce? R (x :: b') with
    | none => RewriteFromLeft_rec (x :: a) b' R
    | some v => RewriteFromLeft_rec a v R
termination_by b
decreasing_by
· have : _ := ti_cons b' x
  simp_all
· sorry

def RewriteFromLeft [ReductionOrder A] [DecidableEq A] (R : Array (Rule A)) (w : Word A) : Word A :=
  RewriteFromLeft_rec [] w R

lemma RewriteFromLeft_leq [ReductionOrder A] {R : Array (Rule A)} {w : Word A} :
    RewriteFromLeft R w ≤ w := by
  sorry

end RewriteFromLeft
