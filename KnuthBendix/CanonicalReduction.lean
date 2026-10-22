module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A]

section ReduceOnce

--DEFINITION OF ONE STEP REDUCTION

--if any LHS of a rule in R is a prefix of w returns reduced word otherwise returns none
def Reduce_if_IsPrefix (R : List (Rule A)) (w : Word A) : Option (Word A) :=
  match R with
  | [] => none
  | r :: RS =>
    match List.isPrefixOf? r.lhs w with
    | none => Reduce_if_IsPrefix RS w
    | some w' => some (r.rhs ++ w')

--TODO: change List.concat to x :: a
-- if any rule is a prefix of "b" returns reduced word by that rule otherwise makes a recursive call
-- with moving one generator from b to a (returns a if b is empty)
def ReduceOnce_rec (a b : Word A) (R : List (Rule A)) : Word A :=
  match b with
  | [] => a
  | x :: b' =>
    match Reduce_if_IsPrefix R b with
    | none => ReduceOnce_rec (List.concat a x) b' R
    | some u => a ++ u

--reduces a word with the first rule that applies from left to right (if any)
--otherwise returns original word
def ReduceOnce (R : List (Rule A)) (w : Word A) : Word A := ReduceOnce_rec [] w R


--LEMMAS ABOUT "Reduce_if_IsPrefix"
variable (v w : Word A) (R : List (Rule A))

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
lemma Reduce_if_IsPrefix_none_succ (r : Rule A) :
    Reduce_if_IsPrefix (r :: R) w = none → Reduce_if_IsPrefix R w = none := by
  intro h
  by_cases h_pref : r.lhs <+: w
  · have : ∃ u, Reduce_if_IsPrefix (r :: R) w = some u := by
      have : ∃ u, List.isPrefixOf? r.lhs w = some u := by
        obtain ⟨u, hu⟩ := h_pref
        use u
        exact List.isPrefixOf?_eq_some_iff_append_eq.mpr hu
      obtain ⟨u, hu⟩ := this
      use (r.rhs ++ u)
      unfold Reduce_if_IsPrefix
      rw [hu]
    obtain ⟨u, hu⟩ := this
    rw [hu] at h
    contradiction
  · have : List.isPrefixOf? r.lhs w = none := by
      by_contra eq_some
      push Not at eq_some
      have : ∃ u, List.isPrefixOf? r.lhs w = some u := by exact Option.ne_none_iff_exists'.mp eq_some
      obtain ⟨u, hu⟩ := this
      unfold Reduce_if_IsPrefix at h
      rw [hu] at h
      simp at h
    unfold Reduce_if_IsPrefix at h
    rw [this] at h
    exact h

-- Reduce_if_IsPrefix returns none iff no rule in R is a prefix of w
lemma Reduce_if_IsPrefix_none_iff :
    Reduce_if_IsPrefix R w = none ↔ ∀ r ∈ R, ¬ r.lhs <+: w := by
  induction R with
  | nil =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    unfold Reduce_if_IsPrefix
    trivial
  | cons r R' ih =>
    constructor
    · intro h_pref r' r_mem'
      by_cases h_eq : r' = r
      · by_contra h_pref'
        rw [h_eq] at h_pref'
        let ⟨u, hu⟩ := h_pref'
        have : List.isPrefixOf? r.lhs w = some u := by
          exact List.isPrefixOf?_eq_some_iff_append_eq.mpr hu
        unfold Reduce_if_IsPrefix at h_pref
        rw [this] at h_pref
        simp at h_pref
      · have h_mem : r' ∈ R' := by
          have h_mem : r' = r ∨ r' ∈ R' := by exact List.eq_or_mem_of_mem_cons r_mem'
          exact h_mem.resolve_left h_eq
        have : Reduce_if_IsPrefix R' w = none := by exact Reduce_if_IsPrefix_none_succ w R' r h_pref
        have h : _ := ih.1 this
        exact h r' h_mem
    · intro h_pref
      have h1 : ∀ r' ∈ R', ¬ r'.lhs <+: w := by
        intro r' h_mem
        exact h_pref r' (List.mem_cons_of_mem r h_mem)
      have h2 : List.isPrefixOf? r.lhs w  = none := by
        specialize h_pref r (List.mem_cons_self)
        have : ∀ u, List.isPrefixOf? r.lhs w ≠ some u := by
          intro u
          by_contra eq_some
          have :  w = r.lhs ++ u := by exact Eq.symm (List.append_eq_of_isPrefixOf?_eq_some eq_some)
          grind
        exact Option.eq_none_iff_forall_ne_some.mpr this
      unfold Reduce_if_IsPrefix
      rw [h2]
      apply ih.2
      exact h1

-- Reduce_if_IsPrefix returns some iff there is a rule in R whose lhs is a prefix of w
lemma Reduce_if_IsPrefix_some_iff :
    (∃ u, Reduce_if_IsPrefix R w = some u) ↔ ∃ r ∈ R, r.lhs <+: w := by
  have h1 : (∃ u, Reduce_if_IsPrefix R w = some u) ↔ ¬(Reduce_if_IsPrefix R w = none) := by
    exact Iff.symm Option.ne_none_iff_exists'
  have h2 : (∃ r ∈ R, r.lhs <+: w) ↔ ¬(∀ r ∈ R, ¬ r.lhs <+: w) := by
    conv =>
      rhs
      push Not
  have h3 : _ := not_congr (Reduce_if_IsPrefix_none_iff w R)
  rw [h1, h3]
  push Not
  trivial


section
variable {w} {w' : Word A} {R}

-- If Reduce_if_IsPrefix returns some w' then w and w' differ by changing r.lhs to r.rhs
lemma append_eq_of_Reduce_if_IsPrefix_eq_some (h : Reduce_if_IsPrefix R w = some w') :
    ∃ r ∈ R, ∃ u : Word A, w = r.lhs ++ u ∧ w' = r.rhs ++ u := by
  let ⟨r, r_mem, h_pref⟩ := (Reduce_if_IsPrefix_some_iff w R).1 ⟨w', h⟩
  induction R with
  | nil =>
    contradiction
  | cons r' R' ih =>
    by_cases h_pref' : r'.lhs <+: w
    · use r'
      constructor
      · exact List.mem_cons_self
      · obtain ⟨u, hu⟩ := h_pref'
        use u
        constructor
        · exact Eq.symm hu
        · unfold Reduce_if_IsPrefix at h
          have : List.isPrefixOf? r'.lhs w = some u := by
            exact List.isPrefixOf?_eq_some_iff_append_eq.mpr hu
          rw [this] at h
          simp only [Option.some.injEq] at h
          exact Eq.symm h
    · have : List.isPrefixOf? r'.lhs w = none := by
        exact (isPrefixOf?_eq_none_iff r'.lhs w).mpr h_pref'
      unfold Reduce_if_IsPrefix at h
      rw [this] at h
      have r_mem' : r ∈ R' := by
        have h_neq : r ≠ r' := by
          by_contra h_eq
          rw [h_eq] at h_pref
          contradiction
        exact List.mem_of_ne_of_mem h_neq r_mem
      specialize ih h r_mem'
      exact List.exists_mem_cons_of_exists ih


-- If Reduce_if_IsPrefix returns some w' then there is r ∈ R s.t. r.lhs and r.rhs are prefixes of w and w' respectively
lemma rule_prefix_of_Reduce_if_IsPrefix_eq_some (h : Reduce_if_IsPrefix R w = some w') :
    ∃ r ∈ R, r.lhs <+: w ∧ r.rhs <+: w' := by
  obtain ⟨r, r_mem, u, hu⟩ := append_eq_of_Reduce_if_IsPrefix_eq_some h
  use r
  exact ⟨r_mem, ⟨u, Eq.symm hu.1⟩, ⟨u, Eq.symm hu.2⟩⟩

-- The word obtained by Reduce_if_IsPrefix is strictly smaller than w
lemma Reduce_if_IsPrefix_le [ReductionOrder A] (h : Reduce_if_IsPrefix R w = some w') : w' < w := by
  induction R with
  | nil =>
    unfold Reduce_if_IsPrefix at h
    contradiction
  | cons r R' ih =>
    cases Option.eq_none_or_eq_some (List.isPrefixOf? r.lhs w) with
    | inl pref_none =>
      unfold Reduce_if_IsPrefix at h
      rw [pref_none] at h
      exact ih h
    | inr pref_some =>
      unfold Reduce_if_IsPrefix at h
      obtain ⟨v, hv⟩ := pref_some
      have h_append : r.lhs ++ v = w := by exact List.append_eq_of_isPrefixOf?_eq_some hv
      rw [hv] at h
      simp only [Option.some.injEq] at h
      rw [←h, ←h_append]
      exact tir_le r.rhs_lt_lhs

end

--LEMMAS ABOUT "ReduceOnce"
variable {w} {R} {a b : Word A}

lemma ReduceOnce_rec_eq_append (a b : Word A) :
    ReduceOnce_rec a b R = a ++ ReduceOnce_rec [] b R := by
  induction b generalizing a with
  | nil =>
    unfold ReduceOnce_rec
    simp
  | cons x b' ih =>
    let b := x :: b'
    by_cases h_pref : ∃ r ∈ R, r.lhs <+: b
    · have h : ∃ u, Reduce_if_IsPrefix R b = some u := by
        apply (Reduce_if_IsPrefix_some_iff b R).mpr h_pref
      obtain ⟨u, hu⟩ := h
      unfold ReduceOnce_rec
      rw [hu]
      simp
    · have h : Reduce_if_IsPrefix R b = none := by
        push Not at h_pref
        exact (Reduce_if_IsPrefix_none_iff b R).mpr h_pref
      unfold ReduceOnce_rec
      rw [h]
      simp only [List.concat_eq_append, List.nil_append]
      rw [(ih (a ++ [x])), ih [x]]
      simp

-- ReduceOnce_rec returns the same word iff no r.lhs is a subword of w
lemma ReduceOnce_rec_eq_iff [ReductionOrder A] :
  ReduceOnce_rec [] w R = w ↔ ∀ r ∈ R, ¬ r.lhs <:+: w := by
  induction w with
  | nil =>
    constructor
    · intro h r r_mem
      by_contra h_infix
      have h_empty : r.lhs = [] := by exact List.eq_nil_of_infix_nil h_infix
      have h_nonempty : r.lhs ≠ [] := by exact lhsNonempty r
      contradiction
    · intro h
      unfold ReduceOnce_rec
      trivial
  | cons x b' ih =>
    constructor
    · intro h_eq r r_mem
      by_contra h_infix
      by_cases h_pref : ∃r' ∈ R, r'.lhs <+: (x :: b')
      · have : (∃ u, Reduce_if_IsPrefix R (x :: b') = some u) := by
          refine (Reduce_if_IsPrefix_some_iff (x :: b') R).mpr ?_
          obtain ⟨r, hr⟩ := h_pref
          use r
        obtain ⟨u, hu⟩ := this
        have h_le : u < (x :: b') := by
          exact Reduce_if_IsPrefix_le hu
        have h_reduceonce_eq : ReduceOnce_rec [] (x :: b') R = u := by
          unfold ReduceOnce_rec
          rw [hu]
          simp
        rw [h_reduceonce_eq] at h_eq
        simp_all only [lt_self_iff_false]
      · push Not at h_pref
        have h_infix' : r.lhs <:+: b' := by
          specialize h_pref r r_mem
          exact Or.resolve_left (List.infix_cons_iff.mp h_infix) h_pref
        have h_neq : ReduceOnce_rec [] b' R ≠ b' := by
          apply not_congr at ih
          apply ih.2
          push Not
          use r
        have h_calc : ReduceOnce_rec [] (x :: b') R = [x] ++ ReduceOnce_rec [] b' R := by
          have h1 : Reduce_if_IsPrefix R (x :: b') = none := by
            exact (Reduce_if_IsPrefix_none_iff (x :: b') R).mpr h_pref
          calc _ = ReduceOnce_rec ([x]) b' R := by
                conv =>
                  lhs
                  unfold ReduceOnce_rec
                  rw [h1]
                  simp
               _ = [x] ++ ReduceOnce_rec [] b' R := by
                exact ReduceOnce_rec_eq_append [x] b'
        rw [h_calc] at h_eq
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h_eq
        rw [h_eq] at h_neq
        contradiction
    · intro h
      have h1 : Reduce_if_IsPrefix R (x :: b') = none := by
        refine (Reduce_if_IsPrefix_none_iff (x :: b') R).mpr ?_
        intro r r_mem
        by_contra h_pref
        specialize h r r_mem
        have h_infix : r.lhs <:+: x :: b' := by exact List.IsPrefix.isInfix h_pref
        contradiction
      have h2 : ∀ r ∈ R, ¬ r.lhs <:+: b' := by
        intro r r_mem
        specialize h r r_mem
        by_contra h_infix
        have : r.lhs <:+: x :: b' := by exact List.infix_cons h_infix
        contradiction
      have h3 : ReduceOnce_rec [] b' R = b' := ih.2 h2
      calc _ = ReduceOnce_rec [x] b' R := by
            conv =>
              lhs
              unfold ReduceOnce_rec
              rw [h1]
              simp
           _ = [x] ++ ReduceOnce_rec [] b' R := ReduceOnce_rec_eq_append [x] b'
           _ = [x] ++ b' := by exact (List.append_right_inj [x]).mpr h3
           _ = x :: b' := by exact List.singleton_append

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

--
lemma ReduceOnce_rec_step {x : A} {a b : Word A} {R : List (Rule A)}
    (h : ∀ r ∈ R, ¬ r.lhs <+: (x :: b)) :
    ReduceOnce_rec a (x :: b) R = ReduceOnce_rec (a ++ [x]) b R := by
  have : Reduce_if_IsPrefix R (x :: b) = none :=
    (Reduce_if_IsPrefix_none_iff (x :: b) R).mpr h
  conv =>
  lhs
  unfold ReduceOnce_rec
  rw [this]
  simp


lemma rule_infix_ReduceOnce_append_of_lhs_infix [ReductionOrder A] {w : Word A} {R : List (Rule A)}
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
    · obtain ⟨u, hu⟩ := (Reduce_if_IsPrefix_some_iff (x :: w') R).mpr h_pref
      obtain ⟨r',⟨r_mem', ⟨v, hv⟩⟩⟩ := append_eq_of_Reduce_if_IsPrefix_eq_some hu
      have h_eq : ReduceOnce R (x :: w') = u := by
        unfold ReduceOnce
        unfold ReduceOnce_rec
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
            calc _ = ReduceOnce_rec [] (x :: w') R := by unfold ReduceOnce; trivial
                _ = ReduceOnce_rec [x] w' R := by exact ReduceOnce_rec_step h'
                _ = [x] ++ ReduceOnce_rec [] w' R := by exact ReduceOnce_rec_eq_append [x] w'
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
lemma Reduce_if_IsPrefix_leq [ReductionOrder A] :
    Reduce_if_IsPrefix R w ≤ w := by
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
  refine ReductionOrder.tiᵣ r.rhs r.lhs u ?_
  exact Std.le_of_lt r.rhs_lt_lhs

lemma ReduceOnce_rec_leq [ReductionOrder A] :
    ReduceOnce_rec a w R ≤ (a ++ w) := by
  induction w generalizing a with
  | nil => simp only [List.append_nil]; unfold ReduceOnce_rec; exact Std.IsPreorder.le_refl a
  | cons x b' ih =>
    unfold ReduceOnce_rec
    cases hb : Reduce_if_IsPrefix R (x :: b') with
    | none =>
      simp only [List.concat_eq_append]
      specialize ih (a ++ [x])
      have : a ++ x :: b' = a ++ [x] ++ b' := by exact List.append_cons a x b'
      exact le_of_le_of_eq ih (id (Eq.symm this))
    | some b'' =>
      have h := Reduce_if_IsPrefix_leq (x :: b') (R := R)
      rw [hb] at h
      exact ReductionOrder.tiₗ b'' (x :: b') a h

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

variable {w : Word A} {R : List (Rule A)}
variable [ReductionOrder A]

-- REDUCTION BY ITERATION OF REDUCEONCE

--iterates ReduceOnce n times
def ReduceNat (w : Word A) (R : List (Rule A)) (n : Nat) : Word A :=
  Nat.iterate (ReduceOnce R) n w

instance [ReductionOrder A] : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

--iterates ReduceOnce as long as the output is changing
def CanonicalReduction [ReductionOrder A] (R : List (Rule A)) (w : Word A) : Word A :=
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
