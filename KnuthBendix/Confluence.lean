module

public import KnuthBendix.ReductionRelation

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [ReductionOrder A] [DecidableEq A]

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


lemma Irreducible_fix {w t : Word A} {R : List (Rule A)} (h_irr : w ∈ IrrSet R) (h_reduces : Reduction R w t) : w = t := by
  unfold IrrSet at h_irr
  unfold Irreducible at h_irr
  unfold Reduction at h_reduces
  cases Relation.reflTransGen_iff_eq_or_transGen.mp h_reduces with
  | inl h_eq => simp_all
  | inr h =>
    have : ∃ u, OneStepReduction R w u := by
      obtain ⟨u, hu⟩ := Relation.TransGen.head'_iff.mp h
      exact ⟨u, hu.1⟩
    obtain ⟨w', h_onestep⟩  := this
    obtain ⟨r, r_mem, u, v, h⟩ := rule_of_OneStepReduction R h_onestep
    specialize h_irr r r_mem
    grind

-- LEMMAS ABOUT CONFLUENCE, LOCAL CONFLUENCE AND COMPLETENESS
lemma Confluent_iff_Complete (R : List (Rule A)) : Confluent R ↔ Complete R := by
  constructor
  · intro h_confluent w
    use (CanonicalReduction w R)
    obtain CR_reduct := reduces_to_CanonicalReduction w R
    obtain CR_irr := CR_Irreducible w R
    refine ⟨⟨CR_irr, CR_reduct⟩ , ?_⟩
    intro v ⟨v_irr, v_reduct⟩
    specialize h_confluent w v (CanonicalReduction w R) v_reduct CR_reduct
    obtain ⟨t, h⟩ := h_confluent
    have v_eq_t : v = t := Irreducible_fix v_irr h.1
    have CR_eq_t : (CanonicalReduction w R) = t := Irreducible_fix CR_irr h.2
    rw [v_eq_t, ←CR_eq_t]
  · intro h_complete w u v reduces_wu reduces_wv
    have CR_eq : CanonicalReduction u R = CanonicalReduction v R := by
      have reduces_w_CRu : Reduction R w (CanonicalReduction u R) := by
        unfold Reduction
        exact Relation.ReflTransGen.trans reduces_wu (reduces_to_CanonicalReduction u R)
      have reduces_w_CRv : Reduction R w (CanonicalReduction v R) := by
        unfold Reduction
        exact Relation.ReflTransGen.trans reduces_wv (reduces_to_CanonicalReduction v R)
      specialize h_complete w
      unfold UniqueResidue at h_complete
      obtain ⟨w', ⟨h_irr, h_reduces'⟩, hw⟩ := h_complete
      have CRu_eq_w' : CanonicalReduction u R = w' := by
        exact hw (CanonicalReduction u R) ⟨by exact CR_Irreducible u R, reduces_w_CRu⟩
      have CRv_eq_w' : CanonicalReduction v R = w' := by
        exact hw (CanonicalReduction v R) ⟨by exact CR_Irreducible v R, reduces_w_CRv⟩
      rw [CRu_eq_w', CRv_eq_w']
    use  CanonicalReduction u R
    exact ⟨by exact reduces_to_CanonicalReduction u R,
      by rw [CR_eq]; exact reduces_to_CanonicalReduction v R⟩


lemma k_Confluent_iff_k_Complete (k : Nat) (R : List (Rule A)) :
  k_Confluent k R ↔ k_Complete k R := by
  constructor
  · intro k_confluent w h_len
    use CanonicalReduction w R
    refine ⟨⟨CR_Irreducible w R, reduces_to_CanonicalReduction w R⟩ , ?_⟩
    intro v ⟨v_irr, v_reduct⟩
    specialize k_confluent w v (CanonicalReduction w R) h_len v_reduct (reduces_to_CanonicalReduction w R)
    obtain ⟨t, h⟩ := k_confluent
    have v_eq_t : v = t := Irreducible_fix v_irr h.1
    have CR_eq_t : (CanonicalReduction w R) = t := Irreducible_fix (CR_Irreducible w R) h.2
    rw [v_eq_t, ←CR_eq_t]
  · intro k_complete w v u h_len reduces_wv reduces_wu
    use CanonicalReduction u R
    have CR_eq : CanonicalReduction u R = CanonicalReduction v R := by
      have reduces_CRu : Reduction R w (CanonicalReduction u R) := by
        exact Relation.ReflTransGen.trans reduces_wu (reduces_to_CanonicalReduction u R)
      have reduces_CRv : Reduction R w (CanonicalReduction v R) := by
        exact Relation.ReflTransGen.trans reduces_wv (reduces_to_CanonicalReduction v R)
      specialize k_complete w h_len
      obtain ⟨w', ⟨h_irr, h_reduces'⟩, hw⟩ := k_complete
      have CRu_eq_w' : CanonicalReduction u R = w' := by
        exact hw (CanonicalReduction u R) ⟨by exact CR_Irreducible u R, reduces_CRu⟩
      have CRv_eq_w' : CanonicalReduction v R = w' := by
        exact hw (CanonicalReduction v R) ⟨by exact CR_Irreducible v R, reduces_CRv⟩
      rw [CRu_eq_w', CRv_eq_w']
    exact ⟨by rw [CR_eq]; exact reduces_to_CanonicalReduction v R,
      reduces_to_CanonicalReduction u R⟩

lemma k_Complete_of_Complete (k : Nat) (R : List (Rule A)) (h_complete : Complete R) :
  k_Complete k R := by
  intro w h_len
  exact h_complete w

lemma Complete_of_k_Complete (R : List (Rule A)) (h_k_complete : ∀ k : Nat, k_Complete k R) :
  Complete R := by
  intro w
  exact h_k_complete w.length w (by trivial)

lemma k_Confluent_of_Confluent (k : Nat) (R : List (Rule A)) (h_confluent : Confluent R) :
  k_Confluent k R := by
  intro w u v h_len reduces_wu reduces_wv
  exact h_confluent w u v reduces_wu reduces_wv

lemma Confluent_of_k_Confluent (R : List (Rule A)) (h_k_confluent : ∀ k : Nat, k_Confluent k R) :
  Confluent R := by
  intro w u v reduces_wu reduces_wv
  exact h_k_confluent (w.length) w u v (by trivial) reduces_wu reduces_wv

lemma Confluent_iff_LocallyConfluent (R : List (Rule A)) : Confluent R ↔ LocallyConfluent R := by
  constructor
  · intro h_confluent w u v reduceOS_wu reduceOS_wv
    exact h_confluent w u v (Reduction_of_OneStepReduction w u R reduceOS_wu)
      (Reduction_of_OneStepReduction w v R reduceOS_wv)
  · intro h_loc_conf w u v reduce_wu reduce_wv
    sorry

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

lemma RelationJoin_of_NonOverlap (R : List (Rule A)) (r r' : Rule A) (r_mem : r ∈ R) (r_mem' : r' ∈ R) (hwv : w = v₁ ++ r.lhs ++ v₂) (hv: v = v₁ ++ r.rhs ++ v₂) (hwu : w = u₁ ++ r'.lhs ++ u₂) (hu : u = u₁ ++ r'.rhs ++ u₂) (h_pref : v₁ ++ r.lhs <+: u₁):
Relation.Join (Reduction R) v u := by
  rcases h_pref with ⟨y, rfl⟩
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

lemma RelationJoin_of_Overlap (R : List (Rule A)) (r r' : Rule A) (r_mem : r ∈ R) (r_mem' : r' ∈ R) (h_complete : CompleteRules r r' R) (hwv : w = v₁ ++ r.lhs ++ v₂) (hv: v = v₁ ++ r.rhs ++ v₂) (hwu : w = u₁ ++ r'.lhs ++ u₂) (hu : u = u₁ ++ r'.rhs ++ u₂) (h_overlap :  ∃ o : Overlap r.lhs r'.lhs, ∃ w₁ w₂ : Word A, w = w₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂) :
Relation.Join (Reduction R) v u := by
  obtain ⟨o, w₁, w₂, h⟩ := h_overlap
  specialize h_complete o
  have hv : v = w₁ ++ (r.rhs ++ o.suffix₂) ++ w₂ := by

    sorry
  have hu : u = w₁ ++ (o.prefix₁ ++ r'.rhs ++ o.suffix₁) ++ w₂ := by sorry
  rw [hv, hu]
  refine reduction_relation_ti R ?_
  exact h_complete

lemma RelationJoin_of_kOverlap (k : Nat) (R : List (Rule A)) (r r' : Rule A) (r_mem : r ∈ R) (r_mem' : r' ∈ R) (h_k_complete : k_CompleteRules k r r' R) (h_len : List.length w ≤ k) (hwv : w = v₁ ++ r.lhs ++ v₂) (hv: v = v₁ ++ r.rhs ++ v₂) (hwu : w = u₁ ++ r'.lhs ++ u₂) (hu : u = u₁ ++ r'.rhs ++ u₂) (h_overlap :  ∃ o : Overlap r.lhs r'.lhs, ∃ w₁ w₂ : Word A, w = w₁ ++ o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂ ++ w₂) :
Relation.Join (Reduction R) v u := by
  obtain ⟨o, w₁, w₂, h⟩ := h_overlap
  specialize h_k_complete o
  have hv : v = w₁ ++ (r.rhs ++ o.suffix₂) ++ w₂ := by
    sorry
  have hu : u = w₁ ++ (o.prefix₁ ++ r'.rhs ++ o.suffix₁) ++ w₂ := by sorry
  rw [hv, hu]
  refine reduction_relation_ti R ?_
  have h_len_overlap : List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k := by
    have : List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ List.length w := by
      have hw : w = w₁ ++ (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ++ w₂ := by grind
      rw [hw]
      apply List.IsInfix.length_le
      apply List.infix_append w₁ (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) w₂
    exact Nat.le_trans this h_len
  exact h_k_complete h_len_overlap

lemma localConfluence_and_Rules (R : List (Rule A)) :
  LocallyConfluent R ↔ ∀ r r' : Rule A, r ∈ R → r' ∈ R → CompleteRules r r' R := by
  constructor
  · intro h_LocConfluent r r' hr hr' o
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
    · exact relation_join_symm R
        (RelationJoin_of_NonOverlap R r r' r_mem r_mem' hr.1 hr.2 hr'.1 hr'.2 h_pref_v)
    · exact RelationJoin_of_NonOverlap R r' r r_mem' r_mem hr'.1 hr'.2 hr.1 hr.2 h_pref_u
    · have h_complete : CompleteRules r r' R := by
        exact h_complete_rules r r' r_mem r_mem'
      refine relation_join_symm R ?_
      exact RelationJoin_of_Overlap R r r' r_mem r_mem' h_complete hr.1 hr.2 hr'.1 hr'.2 h_overlap_vu
    · have h_complete : CompleteRules r' r R := by
        exact h_complete_rules r' r r_mem' r_mem
      exact RelationJoin_of_Overlap R r' r r_mem' r_mem h_complete hr'.1 hr'.2 hr.1 hr.2 h_overlap_uv


lemma kLocalConfluence_and_Rules (k : Nat) (R : List (Rule A)) :
  k_LocallyConfluent k R ↔ ∀ r r' : Rule A, r ∈ R ∧ r' ∈ R → k_CompleteRules k r r' R := by

  constructor
  · intro h_LocConfluent r r' ⟨hr, hr'⟩
    unfold k_CompleteRules
    intro o h_len
    unfold k_LocallyConfluent at h_LocConfluent
    let w := o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂
    let v := r.rhs ++ o.suffix₂
    let u := o.prefix₁ ++ r'.rhs ++ o.suffix₁
    specialize h_LocConfluent w v u h_len
    have h_reduces_wv : OneStepReduction R w v := sorry
    have h_reduces_wu : OneStepReduction R w u := sorry
    specialize h_LocConfluent h_reduces_wv h_reduces_wu
    apply h_LocConfluent
  · intro h_complete_rules w v u h_len h_reduces_wv h_reduces_wu
    let ⟨r, r_mem, hr⟩ := rule_of_OneStepReduction R h_reduces_wv
    let ⟨r', r_mem', hr'⟩ := rule_of_OneStepReduction R h_reduces_wu
    specialize h_complete_rules r r' ⟨r_mem, r_mem'⟩
    unfold k_CompleteRules at h_complete_rules
    sorry

lemma kLocalConfluence_and_Rules' (k : Nat) (R : List (Rule A)) :
  k_LocallyConfluent k R ↔ ∀ r r' : Rule A, r ∈ R → r' ∈ R → k_CompleteRules k r r' R := by

  constructor
  · intro h_LocConfluent r r' hr hr' o h_len
    let w := o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂
    let v := r.rhs ++ o.suffix₂
    let u := o.prefix₁ ++ r'.rhs ++ o.suffix₁
    specialize h_LocConfluent w v u h_len
    have h_reduces_wv : OneStepReduction R w v := overlap_reduces R r r' o ⟨hr, hr'⟩
    have h_reduces_wu : OneStepReduction R w u := overlap_reduces' R r r' o ⟨hr, hr'⟩
    specialize h_LocConfluent h_reduces_wv h_reduces_wu
    apply h_LocConfluent
  · intro h_complete_rules w v u h_len h_reduces_wv h_reduces_wu
    let ⟨r, r_mem, ⟨v₁, v₂, hr⟩⟩ := rule_of_OneStepReduction R h_reduces_wv
    let ⟨r', r_mem', ⟨u₁, u₂, hr'⟩⟩ := rule_of_OneStepReduction R h_reduces_wu
    --specialize h_complete_rules r r' r_mem r_mem'
    rcases technical_lemma hr.1 hr'.1 (by sorry) (by sorry) with h_pref_v | h_pref_u | h_overlap_vu | h_overlap_uv
    · exact RelationJoin_of_NonOverlap R r r' r_mem r_mem' hr.1 hr.2 hr'.1 hr'.2 h_pref_v
    · exact relation_join_symm R  (RelationJoin_of_NonOverlap R r' r r_mem' r_mem hr'.1 hr'.2 hr.1 hr.2 h_pref_u)
    ·
      sorry
    · sorry
