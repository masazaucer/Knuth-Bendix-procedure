module

public import KnuthBendix.ReductionRelation

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

-- DEFINITION OF CONFLUENCE AND COMPLETENESS
-- R is confluent if w → v and w → u implies ∃ t, v → t and u → t
def Confluent (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    (Reduction R) w v →
    (Reduction R) w u →
    (Relation.Join (Reduction R)) v u

-- confluence for words of lenght at most k
def k_Confluent (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    w.length ≤ k →
    (Reduction R) w v →
    (Reduction R) w u →
    (Relation.Join (Reduction R)) v u

def k_Complete (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w : Word A, w.length ≤ k → UniqueResidue R w

def Complete (R : List (Rule A)) : Prop :=
  ∀ w : Word A, UniqueResidue R w

def LocallyConfluent (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    (OneStepReduction R) w v →
    (OneStepReduction R) w u →
    (Relation.Join (Reduction R)) v u

def k_LocallyConfluent (k : Nat) (R : List (Rule A)) : Prop :=
  ∀ w v u : Word A,
    w.length ≤ k →
    (OneStepReduction R) w v →
    (OneStepReduction R) w u →
    (Relation.Join (Reduction R)) v u

-- LEMMAS ABOUT CONFLUENCE, LOCAL CONFLUENCE AND COMPLETENESS
lemma Confluent_iff_Complete (R : List (Rule A)) : Confluent R ↔ Complete R := by
  sorry

lemma k_Confluent_iff_k_Complete (k : Nat) (R : List (Rule A)) :
  k_Confluent k R ↔ k_Complete k R := by sorry

lemma k_Complete_of_Complete (k : Nat) (R : List (Rule A)) (h_complete : Complete R) :
  k_Complete k R := by sorry

lemma Complete_of_k_Complete (R : List (Rule A)) (h_k_complete : ∀ k : Nat, k_Complete k R) :
  Complete R := by sorry

lemma k_Confluent_of_Confluent (k : Nat) (R : List (Rule A)) (h_confluent : Confluent R) :
  k_Confluent k R := by sorry

lemma Confluent_of_k_Confluent (R : List (Rule A)) (h_k_confluent : ∀ k : Nat, k_Confluent k R) :
  Confluent R := by sorry

lemma Confluent_iff_LocallyConfluent (R : List (Rule A)) : Confluent R ↔ LocallyConfluent R := by sorry

lemma k_Confluent_iff_k_LocallyConfluent (k : Nat) (R : List (Rule A)) :
  k_Confluent k R ↔ k_LocallyConfluent k R := by sorry


--CONNECTING COMPLETENESS WITH RULES
--The order of the rules matters!
def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap r.lhs r'.lhs,
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

def k_CompleteRules (k : Nat) (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap r.lhs r'.lhs,
  List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)


lemma suffix_compare {w v₁ v₂ u₁ u₂ : Word A}
  (hv : w = v₁ ++ v₂) (hu : w = u₁ ++ u₂) :
  List.IsSuffix v₂ u₂ ∨ List.IsSuffix u₂ v₂ := by
  have h1 : List.IsSuffix v₂ w := by refine List.suffix_iff_exists_eq_append.mpr ?_; use v₁
  have h2 : List.IsSuffix u₂ w := by refine List.suffix_iff_exists_eq_append.mpr ?_; use u₁
  exact List.suffix_or_suffix_of_suffix h1 h2

lemma technical_lemma' {w v₁ v₂ u₁ u₂ v u : Word A} (h1 : w = v₁ ++ v ++ v₂) (h2 : w = u₁ ++ u ++ u₂)
  (u_nonempty : u ≠ []) (h_pref : v₁ <+: u₁) :
  List.IsPrefix (v₁ ++ v) u₁ ∨
  ∃ o : Overlap v u, ∃ w₁ w₂ : Word A, w = w₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂ := by
  by_cases h: List.IsPrefix (v₁ ++ v) u₁
  · exact Or.inl h
  · obtain ⟨x₁, hx1⟩ := List.prefix_iff_exists_eq_append.mp h_pref
    cases suffix_compare h1 h2 with
    | inl h_suf =>
      obtain ⟨x₂, hx2⟩ := List.suffix_iff_exists_eq_append.mp h_suf
      have h_eq : v = x₁ ++ u ++ x₂ ∧ u = u ++ [] := by
        constructor
        · rw [hx1, hx2, h1] at h2
          have : v₁ ++ v ++ v₂ = v₁ ++ (x₁ ++ u ++ x₂) ++ v₂ := by grind
          have : v₁ ++ v = v₁ ++ (x₁ ++ u ++ x₂) := by exact List.append_cancel_right this
          exact List.append_cancel_left this
        · simp
      let o : Overlap v u := MakeOverlap v u u x₁ x₂ [] u_nonempty (by right; trivial) h_eq
      refine Or.inr ?_
      use o
      use v₁
      use v₂
      rw [h1]
      have suf2_empty : o.suffix₂ = [] := by rfl
      have hx1' : o.prefix₁ = x₁ := by rfl
      have hx2' : o.suffix₁ = x₂ := by rfl
      have ho : o.overlap = u := by rfl
      grind
    | inr h_suf =>
      obtain ⟨z, hz⟩ := List.suffix_iff_exists_eq_append.mp h_suf
      have h_pref' : u₁ <+: v₁ ++ v := by sorry
      obtain ⟨y, hy⟩ := List.prefix_iff_exists_eq_append.mp h_pref'
      --
      have y_nonempty : y ≠ [] := by
        by_contra y_empty
        rw [y_empty] at hy
        simp at hy
        have : v₁ ++ v <+: u₁ := by grind
        exact (iff_false_intro h).mp this
      have h_eq : v = x₁ ++ y ++ [] ∧ u = y ++ z := by
        constructor
        · rw [hx1] at hy
          simp_all
        · rw [hy, hz, h2] at h1
          have : u₁ ++ u ++ u₂ = u₁ ++ (y ++ z) ++ u₂ := by grind
          have : u₁ ++ u = u₁ ++ (y ++ z):= by exact List.append_cancel_right this
          exact List.append_cancel_left this
      let o : Overlap v u := MakeOverlap v u y x₁ [] z y_nonempty (by left; trivial) h_eq
      refine Or.inr ?_
      use o
      use v₁
      use u₂
      rw [h_eq.1, hz] at h1
      have hx1' : o.prefix₁ = x₁ := by rfl
      have hx2' : o.suffix₁ = [] := by rfl
      have ho : o.overlap = y := by rfl
      have hz' : o.suffix₂ = z := by rfl
      grind


lemma technical_lemma {v₁ v₂ u₁ u₂ w v u : Word A} (h1 : w = v₁ ++ v ++ v₂) (h2 : w = u₁ ++ u ++ u₂)
  (v_nonempty : v ≠ []) (u_nonempty : u ≠ []) :
  List.IsPrefix (v₁ ++ v) u₁ ∨ List.IsPrefix (u₁ ++ u) v₁ ∨
  (∃ o : Overlap v u, ∃ w₁ w₂ : Word A, w = w₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂)
  ∨ (∃ o : Overlap u v, ∃ w₁ w₂ : Word A, w = w₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂) := by
  wlog h_pref : v₁ <+: u₁
  · have : u₁ <+: v₁ := by sorry
    have h : _ := technical_lemma' h2 h1 v_nonempty this
    grind
  · cases technical_lemma' h1 h2 u_nonempty h_pref with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (Or.inr (Or.inl h))


lemma localConfluence_and_Rules (R : List (Rule A)) :
  LocallyConfluent R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → CompleteRules r r' R := by
  constructor
  · intro h_LocConfluent r r' ⟨hr, hr'⟩ o
    let w := o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂
    let u := r.rhs ++ o.suffix₂
    let v := o.prefix₁ ++ r'.rhs ++ o.suffix₁
    have h_reduces_wv : OneStepReduction R w v := by
      exact overlap_reduces' R r r' o ⟨hr, hr'⟩
    have h_reduces_wu : OneStepReduction R w u := by
      exact overlap_reduces R r r' o ⟨hr, hr'⟩
    specialize h_LocConfluent w u v h_reduces_wu h_reduces_wv
    exact h_LocConfluent
  · intro h_complete_rules w u v h_reduces_wu h_reduces_wv
    let ⟨r, r_mem, ⟨v₁, v₂, hr⟩⟩ := rule_of_OneStepReduction R h_reduces_wv
    let ⟨r', r_mem', ⟨u₁, u₂, hr'⟩⟩ := rule_of_OneStepReduction R h_reduces_wu
    rcases technical_lemma hr.1 hr'.1 (by sorry) (by sorry) with h_pref_v | h_pref_u | h_overlap_vu | h_overlap_uv
    · rcases h_pref_v with ⟨y, rfl⟩
      let t : Word A := v₁ ++ r.rhs ++ y ++ r'.rhs ++ u₂
      have h_reduces_vt : Reduction R v t := by
        refine IsInfix_Reduces R r' v t r_mem' ?_
        use (v₁ ++ r.rhs ++ y)
        use u₂
        constructor
        · have : v₂ = y ++ r'.lhs ++ u₂ := by simp_all
          grind
        · trivial
      have h_reduces_ut : Reduction R u t := by
        refine IsInfix_Reduces R r u t r_mem ?_
        use v₁
        use y ++ r'.rhs ++ u₂
        grind
      use t
    · rcases h_pref_u with ⟨y, rfl⟩
      let t : Word A := u₁ ++ r'.rhs ++ y ++ r.rhs ++ v₂
      have h_reduces_vt : Reduction R v t := by
        refine IsInfix_Reduces R r' v t r_mem' ?_
        use u₁
        use y ++ r.rhs ++ v₂
        grind
      have h_reduces_ut : Reduction R u t := by
        refine IsInfix_Reduces R r u t r_mem ?_
        use u₁ ++ r'.rhs ++ y
        use v₂
        constructor
        · have : u₂ = y ++ r.lhs ++ v₂ := by simp_all
          grind
        · trivial
      use t
    · obtain ⟨o, w₁, w₂, h⟩ := h_overlap_vu
      have h_complete : CompleteRules r r' R := by
        exact h_complete_rules r r' ⟨r_mem, r_mem'⟩
      specialize h_complete o
      have hv : v = w₁ ++ (r.rhs ++ o.suffix₂) ++ w₂ := by sorry
      have hu : u = w₁ ++ (o.prefix₁ ++ r'.rhs ++ o.suffix₁) ++ w₂ := by sorry
      rw [hv, hu]
      refine reduction_relation_ti R ?_
      exact relation_join_symm R h_complete
    · obtain ⟨o, w₁, w₂, h⟩ := h_overlap_uv
      have h_complete : CompleteRules r' r R := by
        exact h_complete_rules r' r ⟨r_mem', r_mem⟩
      specialize h_complete o
      have hu : u = w₁ ++ (r'.rhs ++ o.suffix₂) ++ w₂ := by sorry
      have hv : v = w₁ ++ (o.prefix₁ ++ r.rhs ++ o.suffix₁) ++ w₂ := by sorry
      rw [hv, hu]
      exact reduction_relation_ti R h_complete
