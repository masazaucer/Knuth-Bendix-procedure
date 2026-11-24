    --simp +zetaDelta



/-
lemma IsPrefixDec (w : Word A) (r : Rule A) (h : List.isPrefixOf? r.lhs w = some u) :
  w = r.lhs ++ u := by
  simp only [List.isPrefixOf?_eq_some_iff_append_eq] at h
  exact Eq.symm h

def GratestCommonPrefix_rec (u v w : Word A) : Word A × Word A × Word A :=
  match v, w with
  | [], _ => (u, v, w)
  | _, [] => (u, v, w)
  | a :: v', b :: w' =>
    if a = b then GratestCommonPrefix_rec (List.concat u a) v' w'
    else (u, v, w)

-- Given two words returns gratest common prefix and the rest of both words
def GratestCommonPrefix (v w : Word A) : Word A × Word A × Word A := GratestCommonPrefix_rec [] v w


lemma GratestCommonPrefix_eq (v w : Word A) :
  let (u, v', w') := GratestCommonPrefix v w;
  v = u ++ v' ∧ w = u ++ w' := by sorry


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

/-
lemma technical_lemma {v₁ v₂ u₁ u₂ w v u : Word A} (hv : w = v₁ ++ v ++ v₂) (hu : w = u₁ ++ u ++ u₂)
  (v_nonempty : v ≠ []) (u_nonempty : u ≠ []) :
  (v₁ ++ v) <+: u₁ ∨ (u₁ ++ u) <+: v₁ ∨
  (∃ o : Overlap v u, ∃ w₂ : Word A, w = v₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂)
  ∨ (∃ o : Overlap u v, ∃ w₂ : Word A, w = u₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂) := by
  wlog h_pref : v₁ <+: u₁
  · have : u₁ <+: v₁ := by
      refine Or.resolve_left ?_ h_pref
      have hv : w = v₁ ++ (v ++ v₂) := by grind
      have hu : w = u₁ ++ (u ++ u₂) := by grind
      exact prefix_compare hv hu
    have h : _ := technical_lemma' hu hv v_nonempty this
    grind
  · cases technical_lemma' hv hu u_nonempty h_pref with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (Or.inr (Or.inl h))


lemma technical_lemma' {w v₁ v₂ u₁ u₂ v u : Word A} (hv : w = v₁ ++ v ++ v₂) (hu : w = u₁ ++ u ++ u₂)
  (u_nonempty : u ≠ []) (h_pref : v₁ <+: u₁) :
  (v₁ ++ v) <+: u₁ ∨
  ∃ o : Overlap v u, ∃ w₂ : Word A, w = v₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂ := by
  by_cases h: List.IsPrefix (v₁ ++ v) u₁
  · exact Or.inl h
  · obtain ⟨x₁, hx1⟩ := List.prefix_iff_exists_eq_append.mp h_pref
    cases suffix_compare hv hu with
    | inl h_suf =>
      obtain ⟨x₂, hx2⟩ := List.suffix_iff_exists_eq_append.mp h_suf
      have h_eq : v = x₁ ++ u ++ x₂ ∧ u = u ++ [] := by
        constructor
        · rw [hx1, hx2, hv] at hu
          have : v₁ ++ v ++ v₂ = v₁ ++ (x₁ ++ u ++ x₂) ++ v₂ := by grind
          have : v₁ ++ v = v₁ ++ (x₁ ++ u ++ x₂) := by exact List.append_cancel_right this
          exact List.append_cancel_left this
        · simp
      let o : Overlap v u := MakeOverlap v u u x₁ x₂ [] u_nonempty (by right; trivial) h_eq
      refine Or.inr ?_
      use o
      use v₂
      rw [hv]
      have suf2_empty : o.suffix₂ = [] := by rfl
      have hx1' : o.prefix₁ = x₁ := by rfl
      have hx2' : o.suffix₁ = x₂ := by rfl
      have ho : o.overlap = u := by rfl
      grind
    | inr h_suf =>
      obtain ⟨z, hz⟩ := List.suffix_iff_exists_eq_append.mp h_suf
      have h_pref' : u₁ <+: v₁ ++ v := by
        refine Or.resolve_left ?_ h
        have hv : w = (v₁ ++ v) ++ v₂ := by grind
        have hu : w = u₁ ++ (u ++ u₂) := by grind
        exact prefix_compare hv hu
      obtain ⟨y, hy⟩ := List.prefix_iff_exists_eq_append.mp h_pref'
      have y_nonempty : y ≠ [] := by
        by_contra y_empty
        rw [y_empty] at hy
        simp at hy
        have : v₁ ++ v <+: u₁ := by grind
        trivial
      have h_eq : v = x₁ ++ y ++ [] ∧ u = y ++ z := by
        constructor
        · rw [hx1] at hy
          simp_all
        · rw [hy, hz, hu] at hv
          have : u₁ ++ u ++ u₂ = u₁ ++ (y ++ z) ++ u₂ := by grind
          have : u₁ ++ u = u₁ ++ (y ++ z):= by exact List.append_cancel_right this
          exact List.append_cancel_left this
      let o : Overlap v u := MakeOverlap v u y x₁ [] z y_nonempty (by left; trivial) h_eq
      refine Or.inr ?_
      use o
      use u₂
      rw [h_eq.1, hz] at hv
      have hx1' : o.prefix₁ = x₁ := by rfl
      have hx2' : o.suffix₁ = [] := by rfl
      have ho : o.overlap = y := by rfl
      have hz' : o.suffix₂ = z := by rfl
      grind
-/


KNUTHBENDIX:
def FindOverlaps_rec (a b w : Word A) (S : List (Overlap A v w)) (hv : v = a ++ b): List (Overlap A v w) :=
  match b with
  | [] => S
  | x :: b' =>
    let (u, d, e) := GratestCommonPrefix b w
    have hv' : v = (List.concat a x) ++ b' := by sorry
    match h : u with
    | [] => FindOverlaps_rec (List.concat a x) b' w S
    | y :: u' =>
      let u := y :: u'
      have h_nontriv : u ≠ [] := by
        exact List.cons_ne_nil y u'
      if d = [] then
        have hv' : v = (List.concat a x) ++ b' := by sorry
        FindOverlaps_rec (List.concat a x) b' w
        (List.concat S (MakeOverlap u a [] e h_nontriv (by left; trivial)))
      else if e = [] then
        FindOverlaps_rec (List.concat a x) b' w
        (List.concat S (MakeOverlap u a d [] h_nontriv (by right; trivial)))
      else FindOverlaps_rec (List.concat a x) b' w S

-/


/-
lemma MakeRule_dec {u v : Word A} {r : Rule A} {R : List (Rule A)}
(h : Test_for_rule u v R = some r) :
(r.lhs = max (CanonicalReduction R u) (CanonicalReduction R v)) ∧
(r.rhs = min (CanonicalReduction R u) (CanonicalReduction R v)):= by
unfold Test_for_rule at h
by_cases h_CReq : CanonicalReduction R u = CanonicalReduction R v
· simp_all
· have : MakeRule (CanonicalReduction R u) (CanonicalReduction R v) h_CReq = some r := by
    refine Option.some_inj.mpr ?_
    simp only [h_CReq, ↓reduceDIte, Option.some.injEq] at h
    exact h
  unfold MakeRule at this
  simp_all only [↓reduceDIte, Option.some.injEq]
  rw [←this]
  simp

lemma Test_for_rule_Irreducible {u v : Word A} {r : Rule A} {R : List (Rule A)}
(h : Test_for_rule u v R = some r) : r.lhs ∈ IrrSet R ∧ r.rhs ∈ IrrSet R := by sorry

--CRITICAL PAIRS
import KnuthBendix.reductions

variable {A : Type} [LinearOrder A] [DecidableEq A] [WellFoundedLT A] [ReductionOrder A]

--TODO: double check the function
def Overlaps (w u : Word A) : List (Word A) :=
  match w with
  | [] => []
  | _ :: w' => if List.isPrefixOf w u
  then w :: Overlaps w' u
  else if List.isPrefixOf u w
  then u :: Overlaps w' u
  else Overlaps w' u

-- returns all the possibilities in which given two rules form a critical pair (none if they don't form any)
def CriticalPair (r₁ r₂ : Rule A) : Option (List (Word A)) :=
  let overlaps := Overlaps r₁.lhs r₂.lhs
  if overlaps = [] then none else some overlaps

def CriticalPairsList (r : Rule A) (R : List (Rule A)) : List (Option (List (Word A))) :=
  match R with
  | [] => []
  | r' :: R' => CriticalPair r r' :: CriticalPairsList r R'

-- returns all the critical pairs that can be formed by any two rules in R (none if there are no critical pairs)
def CriticalPairs (R : List (Rule A)) : List (Option (List (Word A))) :=
  match R with
  | [] => []
  | r :: R' => CriticalPairsList r R' ++ (CriticalPairs R')
-/
