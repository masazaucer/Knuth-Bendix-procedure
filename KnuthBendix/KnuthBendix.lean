module

public import Mathlib.Data.List.Shortlex
public import KnuthBendix.Confluence

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]

instance : WellFoundedRelation (Word A) where
  rel := (· < ·)
  wf := ReductionOrder.wf.wf

-- Reduces given words using rules from R.
-- If the reduced words are distinct returns the rule they form, otherwise returns none
def Test_for_rule (w u : Word A) (R : Array (Rule A)) : Option (Rule A) :=
  let w' := CanonicalReduction R w
  let u' := CanonicalReduction R u
  if h : w' = u' then none
  else some (MakeRule w' u' h)

-- Returns an overlap of u and v starting at b (if it exists, otherwise none)
-- (I put u as explicit in order to be able to let lean sythesize hv)
def FindOverlap (u a b v : Word A) (hu : u = a.reverse ++ b) :
  Option (Overlap u v) :=
  if hbv : b ≠ [] ∧ v ≠ [] then
    match h : List.getRest v b with
    | some v' =>
      have hw : v = b ++ v' := by exact ListGetRestDec.mp h
      MakeOverlap (u := u) (v := v) b a.reverse [] v' hbv.1 (by left; trivial) (by grind)
    | none =>
      match h' : List.getRest b v with
      | some b' =>
        have hb : b = v ++ b' := by exact ListGetRestDec.mp h'
        MakeOverlap (u := u) (v := v) v a.reverse b' [] hbv.2 (by right; trivial) (by grind)
      | none => none
  else none

-- TODO: ineficient if w = []
def FindOverlaps_rec {v : Word A} (a b w : Word A) (S : Array (Overlap v w)) (hv : v = a.reverse ++ b) :
    Array (Overlap v w) :=
  match b with
  | [] => S
  | x :: b' =>
    have hv' : v = (x :: a).reverse ++ b' := by grind
    match FindOverlap v a (x :: b') w hv with
    | none =>
      FindOverlaps_rec (x :: a) b' w S hv'
    | some o =>
      FindOverlaps_rec (x :: a) b' w (S.push o) hv'

-- returns all possible overlaps of w and v
--order matters! (v can be subword of w but not the other way around)
def FindOverlaps (v w : Word A) : Array (Overlap v w) :=
  FindOverlaps_rec [] v w #[] (by simp)

/-
--not used for now
def ReduceRules_rec (R R' : Array (Rule A)) : Array (Rule A) :=
  match R with
  | [] => R'
  | r :: RS =>
  match Test_for_rule r.lhs r.rhs R' with
    | none => ReduceRules_rec RS R'
    | some r' => ReduceRules_rec RS (List.concat R' r')

-- keeps only important rules from R and reduces them using previous ones if possible
def ReduceRules (R : Array (Rule A)) : Array (Rule A) := ReduceRules_rec R []
-/

-- Returns all rules coming from overlaps of r₁.lhs and r₂.lhs
def CheckOverlaps_rules (r₁ r₂ : Rule A) (R : Array (Rule A)) : Array (Rule A) := Id.run do
  let overlaps := FindOverlaps r₁.lhs r₂.lhs
  overlaps.filterMap
    (fun  ⟨_, w, w', v',_ , _, _⟩ => Test_for_rule (w ++ r₂.rhs ++ w') (r₁.rhs ++ v') R)

/-
--finds all overlaps of rules r₁ and r₂ and returns only the new rules coming from overlaps
def CheckOverlaps_rules' (r₁ r₂ : Rule A) (R : Array (Rule A)) : Array (Rule A) := do
  let overlaps := FindOverlaps r₁.lhs r₂.lhs
  let mut R' := []
  for ⟨_, w, w', v',_ , _, _⟩ in overlaps do
    match Test_for_rule (w ++ r₂.rhs ++ w') (r₁.rhs ++ v') R with
    | none => continue
    | some r => R' := r :: R'
  R'
-/

-- finds all overlaps of rule r with rules from R and returns only the new rules
-- (coming from overlaps)
def CheckOverlaps (r : Rule A) (R : Array (Rule A)) : Array (Rule A) :=
  Array.flatMap (fun r' ↦ CheckOverlaps_rules r r' R) R


-- checks all overlaps of rules in R and returns R together with new rules coming from overlaps
-- (produces E_{i+1} from E_{i} as in Word processing in groups)
-- the returned list of rules is sorted based on OrderOnRules (see basic)
-- We consider all rules on both sides of the tuple checked (assure symmetry!)
def OneStepKnuthBendix (R : Array (Rule A)) : Array (Rule A) :=
  R ++ Array.flatMap (fun r => CheckOverlaps r R) R

def KnuthBendix (R : Array (Rule A)) : Array (Rule A) :=
  let R' := OneStepKnuthBendix R
  if R' = R then R else KnuthBendix R'
partial_fixpoint
