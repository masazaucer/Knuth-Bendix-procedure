module

public import KnuthBendix.reductions

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

-- reduces given words using rules from R. If the reduced words are distinct adds the rule they form to R and returns it
def Test (w u : Word A) (R : List (Rule A)) : Option (Rule A) :=
  let w' := NormalForm w R
  let u' := NormalForm u R
  if h : w' = u' then none
  else some (MakeRule w' u' h)

-- R = all rules (including added), R' = all rules we have added so far
def Overlap_rec (a b : Word A) (r₁ r₂ : Rule A) (R R' : List (Rule A)) : List (Rule A) :=
  match b with
  | [] => R'
  | x :: b' =>
  let (u, d, e) := GratestCommonPrefix b r₂.lhs
  if d = [] ∨ e = [] then -- in this case we have an overlap
    match Test (a ++ r₂.rhs ++ d) (r₁.rhs ++ e) R with
    | none => Overlap_rec (List.concat a x) b' r₁ r₂ R R'  --if the words reduce to the same word we leave the rules as they are
    | some r' =>  Overlap_rec (List.concat a x) b' r₁ r₂ (List.concat R r') (List.concat R' r') -- if the words reduce to different words we add the rule they form to R and R' and continue looking for overlaps
  else Overlap_rec (List.concat a x) b' r₁ r₂ R R' -- if we don't have an overlap move another generator to a and check again

-- finds all possible overlaps of lhs of given rules (where order matters) and for each overlap found calls Test on the two possible reductions coming from the overlap; Return only new rules (coming from overlaps)
def Overlap (r₁ r₂ : Rule A) (R : List (Rule A)) : List (Rule A) := Overlap_rec [] r₁.lhs r₁ r₂ R []

def ReduceRules_rec (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r :: RS =>
  match Test r.lhs r.rhs R' with
    | none => ReduceRules_rec RS R'
    | some r' => ReduceRules_rec RS (List.concat R' r')

-- keeps only important rules from R and reduces them using previous ones if possible
def ReduceRules (R : List (Rule A)) : List (Rule A) := ReduceRules_rec R []

/-
def CheckOverlaps_rec (R R' : List (Rule A)) : List (Rule A) :=
  match R with
  | [] => R'
  | r :: RS =>
  let R'' := [r]
  for r' in R', do
    let R₁ := Overlap r r' R'
    let R₂ := Overlap r' r R'
    let R₃ := Overlap r r R'
    R'' := List.concat R'' (R₁ ++ R₂ ++ R₃)
  sorry
-/

def KnuthBendix (R : List (Rule A)) : List (Rule A) := Id.run do
  let mut R := ReduceRules R
  let mut i := 0
  while h : i < R.length do
    let ri := List.get R ⟨i, h⟩
    for j in List.finRange i do
      have hi : i < R.length := by sorry
      have hj : (j : Nat) < R.length := Nat.lt_trans j.isLt hi
      let rj := R.get ⟨j, hj⟩
      let R₁ := Overlap ri rj R
      let R₂ := Overlap rj ri R
      let R₃ := Overlap ri ri R

      R := R ++ R₁ ++ R₂ ++ R₃

    i := i + 1
  return R
