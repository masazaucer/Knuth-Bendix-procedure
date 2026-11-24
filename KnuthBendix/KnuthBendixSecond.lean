module

public import KnuthBendix.KnuthBendix

@[expose] public section

variable {A : Type} [LinearOrder (Word A)] [DecidableEq A] [ReductionOrder A] [Nonempty A]
variable {rules : Array (Rule A × Bool)}

open Array

instance : Inhabited (Rule A) := sorry


-- WITHOUT DELETING RULES




def CanonicalReduction' [ReductionOrder A] (R : Array (Rule A × Bool)) (w : Word A) : Word A := sorry

lemma CanonicalReduction_leq' :
CanonicalReduction' rules w ≤ w := by
sorry

def Test_for_rule' (w u : Word A) (rules : Array (Rule A × Bool)) : Option (Rule A) :=
  let w' := CanonicalReduction' rules w
  let u' := CanonicalReduction' rules u
  if h : w' = u' then none
  else some (MakeRule w' u' h)

def Test (rules : Array (Rule A × Bool)) (S : Array ((Word A) × (Word A))) :
    Array (Rule A × Bool) := Id.run do
    let mut rules := rules
    let mut S := S
    while h : 0 < S.size do
      let (u, v) := S.back h
      S := S.pop
      match Test_for_rule' u v rules with --fix to only use active rules
      | none => continue
      | some r =>
        for h' : ((r', flag), i) in zipIdx rules do
          if flag then
            if r.lhs <:+: r'.lhs then
                rules := rules.set! i (r', False)
                S := S.push (r'.lhs, r'.rhs)
              else
                if r.lhs <:+: r'.rhs then
                  rules := rules.set! i ((MakeRule r'.lhs (CanonicalReduction' rules r'.rhs)
                  (by apply Ne.symm; apply ne_of_lt; apply lt_of_le_of_lt (b := r'.rhs) CanonicalReduction_leq' r'.rhs_lt_lhs)), True)
    return rules

def CriticalPair (r₁ r₂ : Rule A) (o : ProperOverlap r₁.lhs r₂.lhs) : Word A × Word A :=
  (r₁.rhs ++ o.suf, o.pref ++ r₂.rhs)

def FindCriticalPairs (r₁ r₂ : Rule A) : Array (Word A × Word A) := sorry

def ReduceRedundant (rules : Array (Rule A × Bool)) : Array (Rule A × Bool) :=
  Array.filter (Prod.snd) rules

def ExtractRules (rules : Array (Rule A × Bool)) : Array (Rule A) :=
  rules.map (Prod.fst)

/-
def KnuthBendix_idx (rules : Array (Rule A × Bool)) (m : Nat) : Array (Rule A) := Id.run do
  let mut rules := rules
  if m < rules.size then
    for i in range (m) do
      if rules[m]!.2 ∧ rules[i]!.2 then
        let critical_pairs : Array (Word A × Word A) := FindCriticalPairs rules[m]!.1 rules[i]!.1
        rules := Test rules critical_pairs
    let critical_pairs := FindCriticalPairs rules[m]!.1 rules[m]!.1
    rules := Test rules critical_pairs
    KnuthBendix_idx (ReduceRedundant rules) (m + 1)
  else ExtractRules (rules)
partial_fixpoint
-/



/-
        let reduce : Rule A → Rule A → Bool → Bool :=
          fun r r' flag ↦ if r.lhs <:+: r'.lhs then False else flag
        let shorten : Rule A → Rule A → Rule A :=
          fun r r' ↦ if r.lhs <:+: r'.rhs then
          (MakeRule r'.lhs (CanonicalReduction (by sorry) r'.rhs) (by sorry)) else r'
        let active


def FindProperOverlap (u a b v : Word A) (hu : u = a ++ b) :
  Option (Overlap u v) :=
  if hbv : b ≠ [] ∧ v ≠ [] then
    match h : List.getRest v b with
    | some c =>
      have hv : v = b ++ c := by exact ListGetRestDec.mp h
      MakeOverlap (u := u) (v := v) b a [] c hbv.1 (by left; trivial) (by grind)
    | none => none
  else none
-/

def FindProperOverlap (u a b v : Word A) {hu : u = a.reverse ++ b} :
  Option (Overlap u v) :=
  if hbv : b ≠ [] ∧ v ≠ [] then
    match h : List.getRest v b with
    | some c =>
      have hv : v = b ++ c := by exact ListGetRestDec.mp h
      MakeOverlap (u := u) (v := v) b a.reverse [] c hbv.1 (by left; trivial) (by grind)
    | none => none
  else none


def CheckProperOverlaps_rec {v : Word A} (i j : Nat) (a b w : Word A)
    (rules : Array (Rule A × Bool)) (hv : v = a.reverse ++ b) :
    Array (Rule A × Bool) :=
  if rules[i]!.2 ∧ rules[j]!.2 then
    match b with
    | [] => rules
    | x :: b' =>
      have hv' : v = (x :: a).reverse ++ b' := by grind
      match FindProperOverlap v a (x :: b') w (hu := hv) with
      | none =>
        CheckProperOverlaps_rec i j (x :: a) b' w rules hv'
      | some o =>
        let new_rules := Test rules
          #[(o.prefix₁ ++ o.overlap ++ o.suffix₁, o.overlap ++ o.suffix₂)]
        CheckProperOverlaps_rec i j (x :: a) b' w new_rules hv'
  else rules

-- returns all possible overlaps of w and v
--order matters! (v can be subword of w but not the other way around)
def CheckProperOverlaps (i j : Nat) (rules : Array (Rule A × Bool)) :
    Array (Rule A × Bool) :=
  if h : i < rules.size ∧ j < rules.size then
    CheckProperOverlaps_rec (v := rules[i].1.lhs) i j [] rules[i].1.lhs rules[j].1.lhs
      rules (by simp)
  else rules

def KnuthBendix2 (R : Array (Word A × Word A)) : Array (Rule A × Bool) := Id.run do
  let mut rules := Test #[] R
  let mut i := 0
  while i < rules.size do
    let mut j := 0
    while j ≤ i do
      if rules[i]!.2 ∧ rules[j]!.2 then
        rules := CheckProperOverlaps i j rules
      if j ≠ i ∧ rules[i]!.2 ∧ rules[j]!.2 then
        rules := CheckProperOverlaps j i rules
      j := j + 1
    i := i + 1
  return rules


-- WITH DELETING RULES

def Test_with_deleting (R : Array (Rule A)) (S : Array (Word A × Word A)) :
    Array (Rule A) := Id.run do
  let mut rules := R
  let mut S := S
  while h : 0 < S.size do
    let (u, v) := S.back h
    S := S.pop
    match Test_for_rule u v rules with
    | none => continue
    | some r =>
      let mut (reprocess, keep) := Array.partition (fun r' ↦ r.lhs <:+: r'.lhs) rules
      S := S ++ map (fun r ↦ (r.lhs, r.rhs)) reprocess
      rules := keep.push r
      let f := fun r' ↦ if r.lhs <:+: r'.rhs then
        (MakeRule r'.lhs (CanonicalReduction rules r'.rhs)
        (by apply Ne.symm; apply ne_of_lt;
            exact lt_of_le_of_lt CanonicalReduction_leq r'.rhs_lt_lhs))
        else r'
      rules := map f rules
  return rules

-- returns the first rule with lhs w, if it exists, otherwise none
def find_rule (w : Word A) (rules : Array (Rule A)) : Option (Rule A) :=
    Array.find? (fun r ↦ r.lhs = w) rules

lemma find_rule_eq {r : Rule A} {w : Word A} {rules : Array (Rule A)} (h : find_rule w rules = some r) :
    r.lhs = w := by
  unfold find_rule at h
  grind

def CheckOverlaps_rec' (r₁ r₂ : Rule A) (a b : Word A) (rules : Array (Rule A))
    (h : r₁.lhs = a.reverse ++ b) : Array (Rule A) :=
  match b with
  | [] => rules
  | x :: b' =>
    have h' : r₁.lhs = (x :: a).reverse ++ b' := by
      rw [List.reverse_cons]
      simp_all only [List.append_assoc, List.cons_append, List.nil_append]
    match FindProperOverlap r₁.lhs a (x :: b') r₂.lhs (hu := h) with
    | none =>
      CheckOverlaps_rec' r₁ r₂ (x :: a) b' rules h'
    | some o =>
      let new_rules : Array (Rule A) :=
        Test_with_deleting rules #[(o.prefix₁ ++ r₂.rhs ++ o.suffix₁, r₁.rhs ++ o.suffix₂)]
      match h : (find_rule r₁.lhs rules), (find_rule r₂.lhs rules) with
      | some r₁', some r₂' =>
        have h_eq : r₁'.lhs = r₁.lhs := by
          apply find_rule_eq
          exact Option.mem_def.mp h
        CheckOverlaps_rec' r₁' r₂' (x :: a) b' rules (by rw[h_eq]; exact h')
      | _ , _ => rules

def KnuthBendix2' (R : Array (Word A × Word A)) : Array (Rule A) := Id.run do
  let mut rules := Test_with_deleting #[] R
  sorry




--software foundations
