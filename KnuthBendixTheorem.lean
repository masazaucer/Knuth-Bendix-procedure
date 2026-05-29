module

public import KnuthBendix.KnuthBendix

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A]


theorem KnuthBendix_confluent
  (R : List (Rule A))
  (h : R ∈ PFun.Dom KnuthBendix) :
  Confluent (PFun.fn KnuthBendix R h) := by sorry
