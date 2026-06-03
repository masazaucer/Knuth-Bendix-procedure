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
    if d = [] then
      FindOverlaps_rec (List.concat a x) b' w
      (List.concat S (MakeOverlap u a [] [] e (by left; trivial)))
    else if e = [] then
      FindOverlaps_rec (List.concat a x) b' w
      (List.concat S (MakeOverlap u a d [] [] (by right; trivial)))
    else FindOverlaps_rec (List.concat a x) b' w S

def FindOverlaps (w v : Word A) : List (Overlap A) := FindOverlaps_rec [] w v []


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
def CheckOverlaps (r₁ r₂ : Rule A) (R : List (Rule A)) : List (Rule A) := do
  let overlaps := FindOverlaps r₁.lhs r₂.lhs
  let mut R' := []
  for ⟨u, w, w', v, v', _⟩ in overlaps do
    match Test (w ++ r₂.rhs ++ w') (r₁.rhs ++ v') R with
    | none => continue
    | some r => R' := R' ++ [r]
  R'

def Overlaps_rec (r : Rule A) (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r' :: RS =>
    let R'' := CheckOverlaps r r' R
    Overlaps_rec r RS (R' ++ R'')

-- finds all overlaps of rule r with rules from R and returns only the new rules (coming from overlaps)
def Overlaps (r : Rule A) (R : List (Rule A)) : List (Rule A) := Overlaps_rec r R []

-- checks all overlaps of rules in R and returns R together with new rules coming from overlaps
-- (produces E_{i+1} from E_{i} as in Word processing in groups)
def OneStepKnuthBendix (R : List (Rule A)) : List (Rule A) :=
  R ++ List.flatMap (fun r => Overlaps r R) R

def KnuthBendix (R : List (Rule A)) : List (Rule A) :=
  let R' := OneStepKnuthBendix R
  if R' = R then R else KnuthBendix R'
partial_fixpoint

#check KnuthBendix


--TERMINATION CONDITION

def KnuthBendix_dom (R : List (Rule A)) : Prop :=
  ∃ n : Nat, (Nat.iterate OneStepKnuthBendix n R) = (Nat.iterate OneStepKnuthBendix (n + 1) R)

lemma KnuthBendix_dom_fixpoint (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, ∀ i : Nat, i ≥ n →
  (Nat.iterate OneStepKnuthBendix i R) = (Nat.iterate OneStepKnuthBendix n R) := by
  sorry

lemma KnuthBendixDomain (R : List (Rule A)) (h_dom : KnuthBendix_dom R) :
  ∃ n : Nat, KnuthBendix R = (Nat.iterate OneStepKnuthBendix n R) := by
  sorry

lemma Ei_sub_KB (R : List (Rule A)) (i : Nat) :
  Nat.iterate OneStepKnuthBendix i R ⊆ KnuthBendix R := by
  sorry


/-
partial def KnuthBendix' (R : List (Rule A)) : List (Rule A) :=
  let R' := OneStepKnuthBendix R
  if R' = R then R else KnuthBendix' R


R = rules we still need to process
R' = rules we already processed
terminates if we process all rules

partial def KnuthBendix_rec (R R' : List (Rule A)) : List (Rule A) := do
  match R with
  | [] => R'
  | r :: RS =>
  let mut R'' := []
  for r' in R' do
    R'' := R'' ++ (Overlap r r' R')
  --R'' := R'' ++ (Overlap r r R')
  KnuthBendix_rec (RS ++ R'') (R' ++ R'')

partial def KnuthBendix (R : List (Rule A)) : List (Rule A) := KnuthBendix_rec R R


def KnuthBendix (R : List (Rule A)) : List (Rule A) := Id.run do
--  let mut R := ReduceRules R
  let mut R := R
  let mut i := 0
  while h : i < R.length do
    let ri := List.get R ⟨i, h⟩

    for j in List.finRange i do
      --have hi : i < R.length := by sorry
      --have hj : (j : Nat) < R.length := Nat.lt_trans j.isLt hi
      if let some rj := R[j]? then
        let R₁ := Overlap ri rj R
        let R₂ := Overlap rj ri R
        R := R ++ R₁ ++ R₂
      else
        return []

    R := R ++ (Overlap ri ri R)
    i := i + 1
  return R



  /-
R = all rules (including added), R' = all rules we have added so far
does not consider the added rules in the following overlaps
returns only the rules coming from overlaps
-/
def Overlaps_rec (a b : Word A) (r₁ r₂ : Rule A) (R R' : List (Rule A)) :
List (Rule A) :=
  match b with
  | [] => R'
  | x :: b' =>
  let (u, d, e) := GratestCommonPrefix b r₂.lhs
  if d = [] ∨ e = [] then -- in this case we have an overlap
    match Test (a ++ r₂.rhs ++ d) (r₁.rhs ++ e) R with
    | none => Overlaps_rec (List.concat a x) b' r₁ r₂ R R'
    --if the words reduce to the same word we leave the rules as they are
    | some r' =>  Overlaps_rec (List.concat a x) b' r₁ r₂ R (List.concat R' r')
    -- if the words reduce to different words we add the rule they form to R' and continue looking for overlaps
  else Overlaps_rec (List.concat a x) b' r₁ r₂ R R'
  -- if we don't have an overlap move another generator to a and check again

-- finds all possible overlaps of lhs of given two rules (where order matters) and for each overlap found calls Test on the two possible reductions coming from the overlap; Return only new rules (coming from overlaps)
def Overlaps (r₁ r₂ : Rule A) (R : List (Rule A)) : List (Rule A) :=
  Overlaps_rec [] r₁.lhs r₁ r₂ R []

-/
