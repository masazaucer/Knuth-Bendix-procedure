module

public import KnuthBendix.KnuthBendixDomain
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

--The order of the rules matters!
def CompleteRules (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap r.lhs r'.lhs,
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)

def k_CompleteRules (k : Nat) (r r' : Rule A) (R : List (Rule A)) : Prop :=
  ∀ o : Overlap r.lhs r'.lhs,
  List.length (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) ≤ k →
  Relation.Join (Reduction R) (r.rhs ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)


lemma overlap_reduces (R : List (Rule A)) (r r' : Rule A) (o : Overlap r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (r.rhs ++ o.suffix₂) := by
  cases o.empty with
  |inl suf₁_empty =>
  rw [suf₁_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ []) r.rhs := by
    rw [←suf₁_empty, ←(o.eq).1]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ [] ++ o.suffix₂) (r.rhs ++ o.suffix₂)
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ []) r.rhs [] o.suffix₂ this
  simp_all only [List.append_nil, List.append_assoc]
  exact this
  |inr suf₂_empty =>
  rw [suf₂_empty]
  have : SimpleReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs := by
    rw [← (o.eq).1]
    exact SimpleReduction.mk r h_mem.1
  have : CongruenceClosure (SimpleReduction R) (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ []) (r.rhs ++ [])
  := CongruenceClosure.mk (o.prefix₁ ++ o.overlap ++ o.suffix₁) r.rhs [] [] this
  simp_all only [List.append_assoc, List.append_nil]
  exact this

lemma overlap_reduces'  (R : List (Rule A)) (r r' : Rule A)
  (o : Overlap r.lhs r'.lhs) (h_mem : r ∈ R ∧ r' ∈ R):
  OneStepReduction R (o.prefix₁ ++ o.overlap ++ o.suffix₁ ++ o.suffix₂) (o.prefix₁ ++ r'.rhs ++ o.suffix₁)
  := by
  cases o.empty with
    | inl v2_empty =>
      rw [v2_empty]
      have : SimpleReduction R (o.overlap ++ o.suffix₂) r'.rhs := by
        rw [←(o.eq).2]
        exact SimpleReduction.mk r' h_mem.2
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ (o.overlap ++ o.suffix₂) ++ []) (o.prefix₁ ++ r'.rhs ++ []) :=
        CongruenceClosure.mk (o.overlap ++ o.suffix₂) r'.rhs o.prefix₁ [] this
      simp_all only [List.append_nil, List.append_assoc]
      exact this
    | inr u2_empty =>
      rw [u2_empty]
      have : SimpleReduction R o.overlap r'.rhs := by
        have : o.overlap ++ [] = r'.lhs := by
          rw [←u2_empty, ←(o.eq).2]
        simp only [List.append_nil] at this
        rw [this]
        exact SimpleReduction.mk r' h_mem.2
      have : CongruenceClosure (SimpleReduction R)
        (o.prefix₁ ++ o.overlap ++ o.suffix₁) (o.prefix₁ ++ r'.rhs ++ o.suffix₁) :=
        CongruenceClosure.mk o.overlap r'.rhs o.prefix₁ o.suffix₁ this
      simp_all only [List.append_assoc, List.append_nil]
      exact this

lemma IsInfix_Reduces (R : List (Rule A)) (r : Rule A) (w u : Word A) (r_mem : r ∈ R) :
  (∃ u₁ u₂ : Word A, w = u₁ ++ r.lhs ++ u₂ ∧ u = u₁ ++ r.rhs ++ u₂) → Reduction R w u := by
  intro ⟨u₁, u₂, ⟨h_eq1, h_eq2⟩⟩
  refine Relation.ReflTransGen.single ?_
  have : CongruenceClosure (SimpleReduction R) (u₁ ++ r.lhs ++ u₂) (u₁ ++ r.rhs ++ u₂) :=
    CongruenceClosure.mk r.lhs r.rhs u₁ u₂ (SimpleReduction.mk r r_mem)
  rw [h_eq1, h_eq2]
  exact this


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

lemma reduction_ti {v u w₁ w₂: Word A} (R : List (Rule A)) (h : Relation.Join (Reduction R) v u) :
  Relation.Join (Reduction R) (w₁ ++ v ++ w₂) (w₁ ++ u ++ w₂) := by sorry

lemma relation_join_symm {v u: Word A} (RandomGen : List ( Rule A)) (h : Relation.Join (Reduction R) v u) :
  Relation.Join (Reduction R) u v := by sorry

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
      refine reduction_ti R ?_
      exact relation_join_symm R h_complete
    · obtain ⟨o, w₁, w₂, h⟩ := h_overlap_uv
      have h_complete : CompleteRules r' r R := by
        exact h_complete_rules r' r ⟨r_mem', r_mem⟩
      specialize h_complete o
      have hu : u = w₁ ++ (r'.rhs ++ o.suffix₂) ++ w₂ := by sorry
      have hv : v = w₁ ++ (o.prefix₁ ++ r.rhs ++ o.suffix₁) ++ w₂ := by sorry
      rw [hv, hu]
      exact reduction_ti R h_complete

/-
    by_cases h : List.IsPrefix (v₁ ++ r.lhs ) u₁ ∨ List.IsPrefix (u₁ ++ r'.lhs) v₁
    · cases h with
      |inl h_prefix_u =>
      rcases h_prefix_u with ⟨y, rfl⟩
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
      |inr h_prefix_v =>
        rcases h_prefix_v with ⟨y, rfl⟩
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
    · by_cases h_left : List.length v₁ ≤ List.length u₁
      · by_cases h_right : List.length v₂ ≤ List.length u₂
        · match List.getRest u₁ v₁ with
          | some w1 => sorry
          | none => sorry
        · sorry
      · sorry
-/
lemma lemma1 (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  ∀ r ∈ R, CheckOverlaps r R = [] := by
  intro r hr
  by_contra h_neq
  have h1 : List.flatMap (fun r ↦ CheckOverlaps r R) R ≠ [] := by
    have : ∃ R₁ R₂ : List (Rule A), R = R₁ ++ [r] ++ R₂ := by
      sorry
    obtain ⟨R₁, R₂, h_eq⟩ := this
    have : List.flatMap (fun r ↦ CheckOverlaps r R) R =
    List.flatMap (fun r ↦ CheckOverlaps r R) R₁ ++ List.flatMap (fun r ↦ CheckOverlaps r R) [r] ++
    List.flatMap (fun r ↦ CheckOverlaps r R) R₂ := by sorry
    rw [this]
    have : List.flatMap (fun r ↦ CheckOverlaps r R) [r] = CheckOverlaps r R := by
      simp
    rw [this]
    have : CheckOverlaps r R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R₂ ≠ [] := by
      exact List.append_ne_nil_of_left_ne_nil h_neq (List.flatMap (fun r ↦ CheckOverlaps r R) R₂)
    have := List.append_ne_nil_of_right_ne_nil (List.flatMap (fun r ↦ CheckOverlaps r R) R₁) this
    simp_all

  have h2 : List.length (List.flatMap (fun r ↦ CheckOverlaps r R) R) > 0 := by
    exact List.length_pos_of_ne_nil h1
  have h3 : List.length (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R) > List.length R := by
    rw [List.length_append]
    exact Nat.lt_add_of_pos_right h2
  have h4: List.length (SortRules (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R)) ≠ List.length R
    := by
    have (R' : List (Rule A)): List.length (SortRules R') = List.length R' := by
      unfold SortRules
      exact List.length_mergeSort R'
    rw [this]
    exact Nat.ne_of_lt' h3

  have h5: SortRules (R ++ List.flatMap (fun r ↦ CheckOverlaps r R) R) ≠ R := by
    exact Ne.symm fun a ↦ h4 (congrArg List.length h_fix)
  have : OneStepKnuthBendix R ≠ R := by
    unfold OneStepKnuthBendix
    exact h5
  contradiction


lemma lemma2 (r : Rule A) (R : List (Rule A)) (h : CheckOverlaps r R = []) :
  ∀ r' ∈ R, CheckOverlaps_rules r r' R = [] := by
  intro r' hr'
  by_contra h_neq
  sorry

lemma lemma3 (r₁ r₂ : Rule A) (R : List (Rule A)) (h : CheckOverlaps_rules r₁ r₂ R = []) :
  ∀ o : Overlap r₁.lhs r₂.lhs,
  Test_for_rule (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R = none := by sorry

lemma lemma4 (w u : Word A) (R : List (Rule A)) (h_test_eq_none : Test_for_rule w u R = none) :
  Reduce w R = Reduce u R := by sorry

lemma lemma5 (w : Word A) (R : List (Rule A)) : Reduction R w (Reduce w R) := by sorry

lemma locallyConfluent_of_fixpoint (R : List (Rule A)) (h_fix : OneStepKnuthBendix R = R) :
  LocallyConfluent R := by
  refine (localConfluence_and_Rules R).mpr ?_
  intro r₁ r₂ ⟨h₁, h₂⟩ o
  have h : Reduce (r₁.rhs ++ o.suffix₂) R = Reduce (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R := by
    refine lemma4 (r₁.rhs ++ o.suffix₂) (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R ?_
    refine lemma3 r₁ r₂ R ?_ o
    refine lemma2 r₁ R ?_ r₂ h₂
    refine lemma1 R h_fix r₁ h₁
  use Reduce (r₁.rhs ++ o.suffix₂) R
  constructor
  · exact lemma5 (r₁.rhs ++ o.suffix₂) R
  · rw [h]
    exact lemma5 (o.prefix₁ ++ r₂.rhs ++ o.suffix₁) R



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



lemma IrrSet_sub (R : List (Rule A)) :
  IrrSet (OneStepKnuthBendix R) ⊆ IrrSet R := by
  exact IrrSet_sub_of_sub R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma kIrrSet_sub (k : Nat) (R : List (Rule A)) :
  kIrrSet k (OneStepKnuthBendix R) ⊆ kIrrSet k R := by
  exact kIrrSet_sub_of_sub k R (OneStepKnuthBendix R) (R_sub_OneStepKB R)

lemma k_Complete_of_kIrrSet_eq_succ (k : Nat) (R : List (Rule A)) :
  kIrrSet k R = kIrrSet k (OneStepKnuthBendix R) → k_Complete k R := by
  sorry

/-
lemma k_Complete_iff_kIrrSet_eq (k : Nat) (R : List (Rule A)) :
  k_Complete k R ↔ ∀ i : Nat, kIrrSet k R = kIrrSet k (OneStepKnuthBendix^[i] R) := by
  sorry
-/
lemma kIrrSet_fin (k : Nat) (R : List (Rule A)) : Set.Finite (kIrrSet k R) := by
  have len_fin : {w : Word A | w.length ≤ k}.Finite := by sorry
  exact Set.Finite.inter_of_left len_fin {w | Irreducible R w}


lemma kIrrSet_stabilizes (k : Nat) (R : List (Rule A)) : ∃ n : Nat, ∀ i : Nat, i ≥ n → kIrrSet k
  (OneStepKnuthBendix^[i] R) = kIrrSet k (OneStepKnuthBendix^[n] R) := by
  sorry


lemma k_ResiduesCoincide (k : Nat) (R R' : List (Rule A))
  (hR : k_Complete k R) (hR' : k_Complete k R')
  (h_irr : kIrrSet k R = kIrrSet k R') (h_sub : R ⊆ R') :
  ∀ w : Word A, w.length ≤ k → Reduce w R = Reduce w R' := by sorry

lemma k_Completeness (R : List (Rule A)) :
  ∀ k : Nat, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  k_Complete k (OneStepKnuthBendix^[i] R) ∧
  (∀ w : Word A, w.length ≤ k →
  Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R)) :=
  by
  intro k
  obtain ⟨n, h⟩ := kIrrSet_stabilizes k R
  use n
  intro i i_ge_n
  have k_complete : ∀ j : Nat, j ≥ n → k_Complete k (OneStepKnuthBendix^[j] R) := by
    intro j j_ge_n
    have hj : kIrrSet k (OneStepKnuthBendix^[j] R) = kIrrSet k (OneStepKnuthBendix^[n] R) :=
      h j j_ge_n
    have hj_succ : kIrrSet k (OneStepKnuthBendix^[j + 1] R) = kIrrSet k (OneStepKnuthBendix^[n] R)
      := h (j + 1) (Nat.le_add_right_of_le j_ge_n)
    rw [Eq.symm hj_succ] at hj
    have h_succ : OneStepKnuthBendix^[j + 1] R = OneStepKnuthBendix (OneStepKnuthBendix^[j] R) :=
      OneStepKnuthBendix_eq_NatIterate R j
    rw [h_succ] at hj
    exact (k_Complete_of_kIrrSet_eq_succ k (OneStepKnuthBendix^[j] R)) hj
  have residues_coincide : ∀ w : Word A, w.length ≤ k →
  Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R) :=
  by
    intro w w_le_k
    apply Eq.symm
    refine k_ResiduesCoincide k
      (OneStepKnuthBendix^[n] R) (OneStepKnuthBendix^[i] R) ?_ ?_ ?_ ?_ w w_le_k
    · exact k_complete n (Nat.le_refl n)
    · exact k_complete i i_ge_n
    · exact Eq.symm (h i i_ge_n)
    · exact OneStepKnuthBendix_sub_of_leq R n i i_ge_n
  exact ⟨k_complete i i_ge_n, residues_coincide⟩



--- MAIN THEOREM: Knuth-Bendix algorithm produces a complete rewriting system (if it terminates)
theorem KnuthBendix_Complete (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  refine Complete_of_k_Complete (KnuthBendix R) ?_
  intro k
  have ⟨m, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  have k_complete := k_Completeness R
  specialize k_complete k
  obtain ⟨n, hn⟩ := k_complete
  rw [h_eq]
  by_cases h_n_leq_m : n ≤ m
  · specialize hn m h_n_leq_m
    exact hn.1
  · have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
      specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
      exact Eq.symm h_pow
    rw [h_En_eq_Em]
    specialize hn n (Nat.le_refl n)
    exact hn.1


theorem ResiduesCoincide (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∀ w : Word A, ∃ n : Nat, ∀ i : Nat, i ≥ n →
  Reduce w (KnuthBendix R) = Reduce w (OneStepKnuthBendix^[i] R) := by
  intro w
  have ⟨m, h_eq, h_pow⟩ := KnuthBendixDomain R h_dom
  rw [h_eq]
  have ⟨n, hn⟩ := k_Completeness R w.length
  use n
  intro i h_i_geq_n
  by_cases h_n_leq_m : n ≤ m
  · have h1 : Reduce w (OneStepKnuthBendix^[m] R) = Reduce w (OneStepKnuthBendix^[n] R) := by
      specialize hn m h_n_leq_m
      have h : ∀ (v : Word A),
      List.length v ≤ List.length w →
      Reduce v (OneStepKnuthBendix^[m] R) = Reduce v (OneStepKnuthBendix^[n] R) :=
      hn.2
      specialize h w (by exact Nat.le_refl (List.length w))
      exact h
    have h2 : Reduce w (OneStepKnuthBendix^[i] R) = Reduce w (OneStepKnuthBendix^[n] R) := by
      specialize hn i h_i_geq_n
      have h : ∀ (v : Word A),
      List.length v ≤ List.length w →
      Reduce v (OneStepKnuthBendix^[i] R) = Reduce v (OneStepKnuthBendix^[n] R) :=
      hn.2
      specialize h w (by exact Nat.le_refl (List.length w))
      exact h
    rw [h1]
    exact Eq.symm h2
  · have h_En_eq_Em : OneStepKnuthBendix^[m] R = OneStepKnuthBendix^[n] R := by
      specialize h_pow n (by exact Nat.le_of_not_le h_n_leq_m)
      exact Eq.symm h_pow
    rw [h_En_eq_Em]
    specialize hn i h_i_geq_n
    obtain ⟨h1, h2⟩ := hn
    specialize h2 w (by exact Nat.le_refl (List.length w))
    exact Eq.symm h2


theorem KnuthBendix_confluent (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  exact (Confluent_iff_Complete (KnuthBendix R)).mpr (KnuthBendix_Complete R h_dom)

theorem KnuthBendixConfluent' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Confluent (KnuthBendix R) := by
  refine (Confluent_iff_LocallyConfluent (KnuthBendix R)).mpr ?_
  refine locallyConfluent_of_fixpoint (KnuthBendix R) ?_
  exact KnuthBendixDomain_Fixpoint R h_dom

theorem KnuthBendix_Complete' (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  Complete (KnuthBendix R) := by
  exact (Confluent_iff_Complete (KnuthBendix R)).mp (KnuthBendixConfluent' R h_dom)
