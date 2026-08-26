module

public import Mathlib.Data.List.Shortlex
public import KnuthBendix.confluence

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

-- reduces given words using rules from R. If the reduced words are distinct returns the rule they form, otherwise returns none
def Test_for_rule (w u : Word A) (R : List (Rule A)) : Option (Rule A) :=
  let w' := CanonicalReduction w R
  let u' := CanonicalReduction u R
  if h : w' = u' then none
  else some (MakeRule w' u' h)

def FindOverlap (v a b w : Word A) (b_nontriv : b ≠ []) (w_nontriv : w ≠ []) (hv : v = a ++ b) :
  Option (Overlap v w) :=
  match h : List.getRest w b with
  | some w' =>
    have hw : w = b ++ w' := by exact ListGetRestDec.mp h
    MakeOverlap v w b a [] w' b_nontriv (by left; trivial) (by grind)
  | none =>
    match h' : List.getRest b w with
    | some b' =>
      have hb : b = w ++ b' := by exact ListGetRestDec.mp h'
      MakeOverlap v w w a b' [] w_nontriv (by right; trivial) (by grind)
    | none => none

def FindOverlaps_rec (v a b w : Word A) (S : List (Overlap v w)) (hv : v = a ++ b)
(w_nontriv : w ≠ []) :
  List (Overlap v w) :=
  match b with
  | [] => S
  | x :: b' =>
    let b := x :: b'
    have hv' : v = (List.concat a x) ++ b' := by grind
    have b_nontriv : b ≠ [] := by exact List.cons_ne_nil x b'
    match FindOverlap v a b w b_nontriv w_nontriv hv with
    | none =>
      FindOverlaps_rec v (List.concat a x) b' w S hv' w_nontriv
    | some o =>
      FindOverlaps_rec v (List.concat a x) b' w (List.concat S o) hv' w_nontriv


-- returns all possible overlaps of w and v
--order matters! (v can be subword of w but not the other way around)
def FindOverlaps (v w : Word A) (w_nontriv : w ≠ []) : List (Overlap v w) :=
  FindOverlaps_rec v [] v w [] (by simp) w_nontriv

/-
--not used for now
def ReduceRules_rec (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r :: RS =>
  match Test_for_rule r.lhs r.rhs R' with
    | none => ReduceRules_rec RS R'
    | some r' => ReduceRules_rec RS (List.concat R' r')

-- keeps only important rules from R and reduces them using previous ones if possible
def ReduceRules (R : List (Rule A)) : List (Rule A) := ReduceRules_rec R []
-/

--finds all overlaps of rules r₁ and r₂ and returns only the new rules coming from overlaps
def CheckOverlaps_rules (r₁ r₂ : Rule A) (R : List (Rule A)) : List (Rule A) := do
  let overlaps := FindOverlaps r₁.lhs r₂.lhs (by exact lhsNonempty r₂)
  let mut R' := []
  for ⟨_, w, w', v',_ , _, _⟩ in overlaps do
    match Test_for_rule (w ++ r₂.rhs ++ w') (r₁.rhs ++ v') R with
    | none => continue
    | some r => R' := R' ++ [r]
  R'

def CheckOverlaps_rec (r : Rule A) (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r' :: RS =>
    let R'' := CheckOverlaps_rules r r' R
    CheckOverlaps_rec r RS (R' ++ R'')

-- finds all overlaps of rule r with rules from R and returns only the new rules (coming from overlaps)
def CheckOverlaps (r : Rule A) (R : List (Rule A)) : List (Rule A) := CheckOverlaps_rec r R []

-- checks all overlaps of rules in R and returns R together with new rules coming from overlaps
-- (produces E_{i+1} from E_{i} as in Word processing in groups)
-- the returned list of rules is sorted based on OrderOnRules (see basic)
def OneStepKnuthBendix (R : List (Rule A)) : List (Rule A) :=
  SortRules (R ++ List.flatMap (fun r => CheckOverlaps r R) R)

def KnuthBendix (R : List (Rule A)) : List (Rule A) :=
  let R' := OneStepKnuthBendix R
  if R' = R then R else KnuthBendix R'
partial_fixpoint

#check KnuthBendix


--LEMMAS ABOUT ONE STEP KB

lemma OneStepKnuthBendix_eq_NatIterate (R : List (Rule A)) (i : Nat) :
OneStepKnuthBendix^[i + 1] R = OneStepKnuthBendix (OneStepKnuthBendix^[i] R) := by
  have h : OneStepKnuthBendix^[i + 1] R = OneStepKnuthBendix^[1] (OneStepKnuthBendix^[i] R) := by
    have hi : i + 1 = 1 + i := by grind
    rw [hi]
    exact Function.iterate_add_apply OneStepKnuthBendix 1 i R
  rw [h]
  simp

lemma R_sub_OneStepKB (R : List (Rule A)) :
  R ⊆ OneStepKnuthBendix R := by
  intro r h_mem
  unfold OneStepKnuthBendix
  unfold SortRules
  apply List.mem_mergeSort.mpr
  exact List.mem_append_left (List.flatMap (fun r ↦ CheckOverlaps r R) R) h_mem


lemma R_sub_OneStepKB_Nat (R : List (Rule A)) :
  ∀ n : Nat, R ⊆ OneStepKnuthBendix^[n] R := by
  intro n
  induction n with
  | zero => simp
  | succ n hn =>
  rw [OneStepKnuthBendix_eq_NatIterate]
  have : OneStepKnuthBendix^[n] R ⊆ OneStepKnuthBendix (OneStepKnuthBendix^[n] R) := by
    exact R_sub_OneStepKB (OneStepKnuthBendix^[n] R)
  exact List.Subset.trans hn this

lemma OneStepKB_sub_of_succ (R : List (Rule A)) (i : Nat) :
  OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[i + 1] R := by
  rw [OneStepKnuthBendix_eq_NatIterate]
  exact R_sub_OneStepKB (OneStepKnuthBendix^[i] R)

lemma OneStepKnuthBendix_sub_of_leq (R : List (Rule A)) (i j : Nat) (h_leq : i ≤ j) :
  OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[j] R := by
  have h : ∀ n : Nat, OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[i + n] R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
    have : OneStepKnuthBendix^[i + n] R ⊆ OneStepKnuthBendix^[i + (n + 1)] R := by
      apply OneStepKB_sub_of_succ R (i + n)
    exact List.Subset.trans ih this
  specialize h (j - i)
  simp_all
