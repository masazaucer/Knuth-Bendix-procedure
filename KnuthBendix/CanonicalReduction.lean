module

public import KnuthBendix.basic

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A]

--DEFINITION OF ONE STEP REDUCTION
--if any LHS of a rule in R is a prefix of w returns reduced word otherwise returns none
def Reduce_if_IsPrefix (w : Word A) (R : List (Rule A)) : Option (Word A) :=
  match R with
  | [] => none
  | r :: RS =>
    match List.isPrefixOf? r.lhs w with
    | none => Reduce_if_IsPrefix w RS
    | some w' => some (r.rhs ++ w')


-- if any rule is a prefix of "b" returns reduced word by that rule otherwise makes a recursive call
-- with moving one generator from b to a (returns a if b is empty)
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

--LEMMAS ABOUT "Reduce_if_IsPrefix" AND "ReduceOnce"
/-
lemma Reduce_if_IsPrefix_some_of_rule [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h_pref : ∃ r ∈ R, w = r.lhs ++ w') : ∃ w'', Reduce_if_IsPrefix w R = some w'' := by
  induction R with
  | nil => simp_all
  | cons r' R' ih =>
    by_cases h_head : ∃ u, List.isPrefixOf? r'.lhs w = some u
    · unfold Reduce_if_IsPrefix
      obtain ⟨u, h_prefix⟩ := h_head
      simp only [h_prefix]
      use (r'.rhs ++ u)
    · obtain ⟨r, h_mem, h_eq⟩ := h_pref
      unfold Reduce_if_IsPrefix
      have : List.isPrefixOf? r'.lhs w = none := by
        by_contra h_contra
        have : ∃ x, List.isPrefixOf? r'.lhs w = some x := Option.ne_none_iff_exists'.1 h_contra
        exact h_head this
      simp only [this]
      have h_mem' : r ∈ R' := by
        have h_mem : r = r' ∨ r ∈ R' := by exact List.eq_or_mem_of_mem_cons h_mem
        have h_neq : r ≠ r' := by
          intro h_contra
          rw [h_contra] at h_eq
          have h : List.isPrefixOf? r'.lhs w = some w' := by
            rw [h_eq]
            exact List.isPrefixOf?_eq_some_iff_append_eq.mpr rfl
          rw [h] at this
          contradiction
        exact h_mem.resolve_left h_neq
      exact ih ⟨r, h_mem', h_eq⟩

lemma Reduce_if_IsPrefix_rule_of_some [ReductionOrder A] (w : Word A) (R : List (Rule A)) (h : ∃ u, Reduce_if_IsPrefix w R = some u) : ∃ r ∈ R, w = r.lhs ++ u := by sorry
-/

lemma Reduce_if_IsPrefix_none_succ (w : Word A) (R : List (Rule A)) (r : Rule A) :
  Reduce_if_IsPrefix w (r :: R) = none → Reduce_if_IsPrefix w R = none := by
  intro h
  by_cases h_pref : r.lhs <+: w
  · have : ∃ u, Reduce_if_IsPrefix w (r :: R) = some u := by
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

lemma Reduce_if_IsPrefix_none_iff (w : Word A) (R : List (Rule A)) :
  Reduce_if_IsPrefix w R = none ↔ ∀ r ∈ R, ¬ List.IsPrefix r.lhs w := by
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
        have : Reduce_if_IsPrefix w R' = none := by exact Reduce_if_IsPrefix_none_succ w R' r h_pref
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

lemma Reduce_if_IsPrefix_some_iff (w : Word A) (R : List (Rule A)) :
  (∃ u, Reduce_if_IsPrefix w R = some u) ↔ ∃ r ∈ R, List.IsPrefix r.lhs w := by
  have h1 : (∃ u, Reduce_if_IsPrefix w R = some u) ↔ ¬(Reduce_if_IsPrefix w R = none) := by sorry
  have h2 : ∃ r ∈ R, List.IsPrefix r.lhs w ↔ ¬(∀ r ∈ R, ¬ List.IsPrefix r.lhs w) := by sorry
  have h3 : _ := not_congr (Reduce_if_IsPrefix_none_iff w R)
  rw [h1, h3]
  push Not
  trivial

lemma Reduce_if_IsPrefix_le [ReductionOrder A] {u} (w : Word A) (R : List (Rule A))
(h : Reduce_if_IsPrefix w R = some u) : u < w := by
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
      exact ReductionOrder.tiᵣ r.rhs r.lhs v r.rhs_lt_lhs


lemma ReduceOnce_rec_eq_append (b : Word A) (R : List (Rule A)) :
  ∀ a : Word A, ReduceOnce_rec a b R = a ++ ReduceOnce_rec [] b R := by
  induction b with
  | nil =>
    intro a
    unfold ReduceOnce_rec
    simp
  | cons x b' ih =>
    intro a
    let b := x :: b'
    by_cases h_pref : ∃ r ∈ R, r.lhs <+: (x :: b')
    · have h : ∃ u, Reduce_if_IsPrefix b R = some u := by exact (Reduce_if_IsPrefix_some_iff b R).mpr h_pref
      obtain ⟨u, hu⟩ := h
      unfold ReduceOnce_rec
      rw [hu]
      simp
    · have h : Reduce_if_IsPrefix b R = none := by
        push Not at h_pref
        exact (Reduce_if_IsPrefix_none_iff b R).mpr h_pref
      unfold ReduceOnce_rec
      rw [h]
      simp only [List.concat_eq_append, List.nil_append]
      rw [(ih (a ++ [x])), ih [x]]
      simp

lemma ReduceOnce_rec_eq_iff [ReductionOrder A] (b : Word A) (R : List (Rule A)) :
  ReduceOnce_rec [] b R = b ↔ ∀ r ∈ R, ¬ List.IsInfix r.lhs b := by
  induction b with
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
      · have : (∃ u, Reduce_if_IsPrefix (x :: b') R = some u) := by
          refine (Reduce_if_IsPrefix_some_iff (x :: b') R).mpr ?_
          obtain ⟨r, hr⟩ := h_pref
          use r
        obtain ⟨u, hu⟩ := this
        have h_le : u < (x :: b') := by
          exact Reduce_if_IsPrefix_le (x :: b') R hu
        have h_reduceonce_eq : ReduceOnce_rec [] (x :: b') R = u := by
          unfold ReduceOnce_rec
          rw [hu]
          simp
        rw [h_reduceonce_eq] at h_eq
        simp_all only [lt_self_iff_false]
      · push Not at h_pref
        have h_infix' : r.lhs <:+: b' := by sorry

        have h_neq : ReduceOnce_rec [] b' R ≠ b' := by
          apply not_congr at ih
          apply ih.2
          push Not
          use r
        have h_calc : ReduceOnce_rec [] (x :: b') R = [x] ++ ReduceOnce_rec [] b' R := by
          have h1 : Reduce_if_IsPrefix (x :: b') R = none := by
            exact (Reduce_if_IsPrefix_none_iff (x :: b') R).mpr h_pref
          calc _ = ReduceOnce_rec ([x]) b' R := by
                conv =>
                  lhs
                  unfold ReduceOnce_rec
                  rw [h1]
                  simp
               _ = [x] ++ ReduceOnce_rec [] b' R := by
                exact ReduceOnce_rec_eq_append b' R [x]
        rw [h_calc] at h_eq
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h_eq
        rw [h_eq] at h_neq
        contradiction
    · intro h
      have h1 : Reduce_if_IsPrefix (x :: b') R = none := by
        refine (Reduce_if_IsPrefix_none_iff (x :: b') R).mpr ?_
        intro r r_mem
        by_contra h_pref
        specialize h r r_mem
        have h_infix : r.lhs <:+: x :: b' := by exact List.IsPrefix.isInfix h_pref
        contradiction
      have h2 : ∀ r ∈ R, ¬ List.IsInfix r.lhs b' := by
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
           _ = [x] ++ ReduceOnce_rec [] b' R := ReduceOnce_rec_eq_append b' R [x]
           _ = [x] ++ b' := by exact (List.append_right_inj [x]).mpr h3
           _ = x :: b' := by exact List.singleton_append

lemma ReduceOnce_eq_iff [ReductionOrder A] (w : Word A) (R : List (Rule A)) :
  ReduceOnce w R = w ↔ ∀ r ∈ R, ¬ List.IsInfix r.lhs w := by
  unfold ReduceOnce
  exact ReduceOnce_rec_eq_iff w R


lemma ReduceOnce_neq_of_IsInfix [ReductionOrder A] (w : Word A) (R : List (Rule A))
(h_infix : ∃ r ∈ R, List.IsInfix r.lhs w) : ReduceOnce w R ≠ w := by
  have : ¬ ∀ r ∈ R, ¬List.IsInfix r.lhs w := by grind
  unfold ReduceOnce
  exact (not_congr (ReduceOnce_rec_eq_iff w R)).mpr this



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

lemma CanonicalReduction_leq [ReductionOrder A] (w : Word A) (R : List (Rule A)) :
CanonicalReduction w R ≤ w := by
  let C : Word A → Prop := fun x ↦ CanonicalReduction x R ≤ x
  apply WellFounded.fix (C := C) ReductionOrder.wf.wf
  intro w ih
  unfold C at *
  specialize ih (ReduceOnce w R)
  unfold CanonicalReduction
  by_cases h_reduceonce_eq : ReduceOnce w R = w
  · simp_all
  · have h_reduceonce_lt : ReduceOnce w R < w := ReduceOnce_le w R h_reduceonce_eq
    specialize ih h_reduceonce_lt
    simp_all
    have h_reduceonce_leq : ReduceOnce w R ≤ w := ReduceOnce_leq w R
    exact Std.IsPreorder.le_trans (CanonicalReduction (ReduceOnce w R) R) (ReduceOnce w R) w ih
        h_reduceonce_leq


lemma CR_fix_ReduceOnce [ReductionOrder A] (w : Word A) (R : List (Rule A)) :
  ReduceOnce (CanonicalReduction w R) R = CanonicalReduction w R := by
  let C : Word A → Prop := fun x ↦ ReduceOnce (CanonicalReduction x R) R = CanonicalReduction x R
  apply WellFounded.fix (C := C) ReductionOrder.wf.wf
  intro w ih
  unfold C at *
  unfold CanonicalReduction
  by_cases h_reduceonce_eq : ReduceOnce w R = w
  · simp_all
  · have h_reduceonce_lt : ReduceOnce w R < w := ReduceOnce_le w R h_reduceonce_eq
    specialize ih (ReduceOnce w R) h_reduceonce_lt
    simp_all
