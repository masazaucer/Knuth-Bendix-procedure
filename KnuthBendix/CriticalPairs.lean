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
