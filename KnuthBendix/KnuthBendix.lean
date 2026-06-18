module

public import Mathlib.Data.List.Shortlex
public import KnuthBendix.confluence

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

def GratestCommonPrefix_rec (u v w : Word A) : Word A × Word A × Word A :=
  match v, w with
  | [], _ => (u, v, w)
  | _, [] => (u, v, w)
  | a :: v', b :: w' =>
    if a = b then GratestCommonPrefix_rec (List.concat u a) v' w'
    else (u, v, w)

-- Given two words returns gratest common prefix and the rest of both words
def GratestCommonPrefix (v w : Word A) : Word A × Word A × Word A := GratestCommonPrefix_rec [] v w

-- reduces given words using rules from R. If the reduced words are distinct returns the rule they form, otherwise returns none
def Test (w u : Word A) (R : List (Rule A)) : Option (Rule A) :=
  let w' := Reduce w R
  let u' := Reduce u R
  if h : w' = u' then none
  else some (MakeRule w' u' h)

def FindOverlaps_rec (a b w : Word A) (S : List (Overlap A)) : List (Overlap A) :=
  match b with
  | [] => S
  | x :: b' =>
    let (u, d, e) := GratestCommonPrefix b w
    match h : u with
    | [] => FindOverlaps_rec (List.concat a x) b' w S
    | y :: u' =>
      let u := y :: u'
      have h_nontriv : u ≠ [] := by
        exact List.cons_ne_nil y u'
      if d = [] then
        FindOverlaps_rec (List.concat a x) b' w
        (List.concat S (MakeOverlap u a [] e h_nontriv (by left; trivial)))
      else if e = [] then
        FindOverlaps_rec (List.concat a x) b' w
        (List.concat S (MakeOverlap u a d [] h_nontriv (by right; trivial)))
      else FindOverlaps_rec (List.concat a x) b' w S

-- returns all possible overlaps of w and v
--order matters! (v can be subword of w but not the other way around)
def FindOverlaps (w v : Word A) : List (Overlap A) := FindOverlaps_rec [] w v []

--not used for now
def ReduceRules_rec (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r :: RS =>
  match Test r.lhs r.rhs R' with
    | none => ReduceRules_rec RS R'
    | some r' => ReduceRules_rec RS (List.concat R' r')

-- keeps only important rules from R and reduces them using previous ones if possible
def ReduceRules (R : List (Rule A)) : List (Rule A) := ReduceRules_rec R []


--finds all overlaps of rules r₁ and r₂ and returns only the new rules coming from overlaps
def CheckOverlaps_rules (r₁ r₂ : Rule A) (R : List (Rule A)) : List (Rule A) := do
  let overlaps := FindOverlaps r₁.lhs r₂.lhs
  let mut R' := []
  for ⟨_, w, w', v',_ , _⟩ in overlaps do
    match Test (w ++ r₂.rhs ++ w') (r₁.rhs ++ v') R with
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
  sorry

lemma OneStepKnuthBendix_sub_of_leq (R : List (Rule A)) (i j : Nat) (h_leq : i ≤ j) :
OneStepKnuthBendix^[i] R ⊆ OneStepKnuthBendix^[j] R := by sorry


--TERMINATION CONDITION

-- R is in the domain of KnuthBendix if after some number of iterations we get a fixpoint (i.e. no new rules are added)
def KnuthBendix_dom (R : List (Rule A)) : Prop :=
  ∃ n : Nat, (OneStepKnuthBendix^[n] R) = (OneStepKnuthBendix^[n + 1] R)

-- if R is in the domain of KnuthBendix then from some n on iterating OneStepKnuthBendix returns does nothing
lemma KnuthBendix_dom_fixpoint (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, ∀ i : Nat, i ≥ n →
  (OneStepKnuthBendix^[i] R) = (OneStepKnuthBendix^[n] R) := by
  sorry

lemma KnuthBendixDomain (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, KnuthBendix R = (OneStepKnuthBendix^[n] R) := by
  obtain ⟨n, h⟩ := h_dom
  use n
  rw [KnuthBendix]

  sorry

lemma Ei_sub_KB (R : List (Rule A)) (i : Nat) (h_dom : KnuthBendix_dom R) :
  OneStepKnuthBendix^[i] R ⊆ KnuthBendix R := by
  sorry
