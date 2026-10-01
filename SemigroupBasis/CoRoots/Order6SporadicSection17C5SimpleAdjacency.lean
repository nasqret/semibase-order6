import SemigroupBasis.CoRoots.Order6SporadicSection17C5SimpleBoundaries

/-! The arbitrary-list F_SS observation. A six-state recognizer remembers
both marked letters; two count-one guards eliminate the C6 single-marker
collisions. Every finite transition is checked in both literal tables. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def CleanAdjacent (x y : Nat) (letters : List Nat) : Prop :=
  ∃ before after, letters = before ++ x :: y :: after ∧
    x ∉ before ∧ y ∉ before ∧ x ∉ after ∧ y ∉ after

def SimpleAdjacent (x y : Nat) (letters : List Nat) : Prop :=
  x ≠ y ∧ CleanAdjacent x y letters

theorem cleanAdjacent_nil (x y : Nat) : ¬ CleanAdjacent x y [] := by
  rintro ⟨before,after,shape,_,_,_,_⟩
  have length := congrArg List.length shape
  simp at length
  omega

theorem cleanAdjacent_cons_first (x y : Nat) (letters : List Nat) :
    CleanAdjacent x y (x :: letters) ↔ ∃ after, letters = y :: after ∧ x ∉ after ∧ y ∉ after := by
  constructor
  · rintro ⟨before,after,shape,absentX,_,afterX,afterY⟩
    cases before with
    | nil => exact ⟨after,(List.cons.inj shape).2,afterX,afterY⟩
    | cons z zs =>
        have equal : x = z := (List.cons.inj shape).1
        subst z
        exact False.elim (absentX List.mem_cons_self)
  · rintro ⟨after,shape,afterX,afterY⟩
    exact ⟨[],after,by simp [shape],by simp,by simp,afterX,afterY⟩

theorem cleanAdjacent_cons_second (x y : Nat) (letters : List Nat) (different : x ≠ y) :
    ¬ CleanAdjacent x y (y :: letters) := by
  rintro ⟨before,after,shape,_,absentY,_,_⟩
  cases before with
  | nil => exact different (List.cons.inj shape).1.symm
  | cons z zs =>
      have equal : y = z := (List.cons.inj shape).1
      subst z
      exact absentY List.mem_cons_self

theorem cleanAdjacent_cons_other (x y z : Nat) (letters : List Nat)
    (notX : z ≠ x) (notY : z ≠ y) :
    CleanAdjacent x y (z :: letters) ↔ CleanAdjacent x y letters := by
  constructor
  · rintro ⟨before,after,shape,beforeX,beforeY,afterX,afterY⟩
    cases before with
    | nil => exact False.elim (notX (List.cons.inj shape).1)
    | cons a rest =>
        exact ⟨rest,after,(List.cons.inj shape).2,
          fun member => beforeX (List.mem_cons.mpr (Or.inr member)),
          fun member => beforeY (List.mem_cons.mpr (Or.inr member)),afterX,afterY⟩
  · rintro ⟨before,after,shape,beforeX,beforeY,afterX,afterY⟩
    refine ⟨z :: before,after,?_,?_,?_,afterX,afterY⟩
    · simpa using congrArg (List.cons z) shape
    · simp [notX,Ne.symm notX,beforeX]
    · simp [notY,Ne.symm notY,beforeY]

theorem CleanAdjacent.counts {x y : Nat} {letters : List Nat}
    (adjacent : CleanAdjacent x y letters) (different : x ≠ y) :
    letters.count x = 1 ∧ letters.count y = 1 := by
  rcases adjacent with ⟨before,after,shape,beforeX,beforeY,afterX,afterY⟩
  have bx := List.count_eq_zero.mpr beforeX
  have byCount := List.count_eq_zero.mpr beforeY
  have ax := List.count_eq_zero.mpr afterX
  have ay := List.count_eq_zero.mpr afterY
  constructor
  · simp [shape,List.count_append,List.count_cons_self,List.count_cons_of_ne (Ne.symm different),bx,ax]
  · simp [shape,List.count_append,List.count_cons_self,List.count_cons_of_ne different,byCount,ay]

theorem cleanAdjacent_of_count_one (x y : Nat) (letters : List Nat) (different : x ≠ y)
    (onceX : letters.count x = 1) (onceY : letters.count y = 1)
    (adjacent : ∃ before after, letters = before ++ x :: y :: after) :
    CleanAdjacent x y letters := by
  rcases adjacent with ⟨before,after,shape⟩
  have countX := onceX
  have countY := onceY
  rw [shape] at countX countY
  simp only [List.count_append,List.count_cons_self,List.count_cons_of_ne different,
    List.count_cons_of_ne (Ne.symm different)] at countX countY
  exact ⟨before,after,shape,List.count_eq_zero.mp (by omega),List.count_eq_zero.mp (by omega),
    List.count_eq_zero.mp (by omega),List.count_eq_zero.mp (by omega)⟩

theorem simpleAdjacent_iff (x y : Nat) (letters : List Nat) (different : x ≠ y) :
    SimpleAdjacent x y letters ↔ letters.count x = 1 ∧ letters.count y = 1 ∧
      ∃ before after, letters = before ++ x :: y :: after := by
  constructor
  · rintro ⟨_,adjacent⟩
    have counts := adjacent.counts different
    rcases adjacent with ⟨before,after,shape,_,_,_,_⟩
    exact ⟨counts.1,counts.2,before,after,shape⟩
  · rintro ⟨onceX,onceY,adjacent⟩
    exact ⟨different,cleanAdjacent_of_count_one x y letters different onceX onceY adjacent⟩

inductive PairLetter where
  | first | second | other
  deriving DecidableEq, Repr

inductive PairState where
  | fresh | firstX | gapX | firstY | paired | dead
  deriving DecidableEq, Repr

def pairClass (x y z : Nat) : PairLetter :=
  if z = x then .first else if z = y then .second else .other

def pairStep (kind : PairLetter) : PairState → PairState
  | .fresh => match kind with
      | .first => .firstX
      | .second => .firstY
      | .other => .fresh
  | .firstX => match kind with
      | .first => .dead
      | .second => .paired
      | .other => .gapX
  | .gapX => match kind with
      | .other => .gapX
      | _ => .dead
  | .firstY => match kind with
      | .other => .firstY
      | _ => .dead
  | .paired => match kind with
      | .other => .paired
      | _ => .dead
  | .dead => .dead

def pairScan (x y : Nat) (state : PairState) : List Nat → PairState
  | [] => state
  | z :: zs => pairScan x y (pairStep (pairClass x y z) state) zs

theorem pairScan_dead (x y : Nat) (letters : List Nat) : pairScan x y .dead letters = .dead := by
  induction letters with
  | nil => rfl
  | cons z zs ih => exact ih

theorem pairScan_gapX (x y : Nat) (letters : List Nat) :
    pairScan x y .gapX letters = if x ∈ letters ∨ y ∈ letters then .dead else .gapX := by
  induction letters with
  | nil => rfl
  | cons z zs ih =>
      by_cases first : z = x
      · subst z; simp [pairScan,pairStep,pairClass,pairScan_dead]
      · by_cases second : z = y
        · subst z; simp [pairScan,pairStep,pairClass,first,pairScan_dead]
        · simp [pairScan,pairStep,pairClass,first,second,Ne.symm first,Ne.symm second,ih]

theorem pairScan_firstY (x y : Nat) (letters : List Nat) :
    pairScan x y .firstY letters = if x ∈ letters ∨ y ∈ letters then .dead else .firstY := by
  induction letters with
  | nil => rfl
  | cons z zs ih =>
      by_cases first : z = x
      · subst z; simp [pairScan,pairStep,pairClass,pairScan_dead]
      · by_cases second : z = y
        · subst z; simp [pairScan,pairStep,pairClass,first,pairScan_dead]
        · simp [pairScan,pairStep,pairClass,first,second,Ne.symm first,Ne.symm second,ih]

theorem pairScan_paired (x y : Nat) (letters : List Nat) :
    pairScan x y .paired letters = if x ∈ letters ∨ y ∈ letters then .dead else .paired := by
  induction letters with
  | nil => rfl
  | cons z zs ih =>
      by_cases first : z = x
      · subst z; simp [pairScan,pairStep,pairClass,pairScan_dead]
      · by_cases second : z = y
        · subst z; simp [pairScan,pairStep,pairClass,first,pairScan_dead]
        · simp [pairScan,pairStep,pairClass,first,second,Ne.symm first,Ne.symm second,ih]

theorem pairScan_fresh_paired (x y : Nat) (letters : List Nat) (different : x ≠ y) :
    pairScan x y .fresh letters = .paired ↔ CleanAdjacent x y letters := by
  induction letters with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; exact False.elim (cleanAdjacent_nil x y impossible)
  | cons z zs ih =>
      by_cases first : z = x
      · subst z
        rw [cleanAdjacent_cons_first]
        cases zs with
        | nil => simp [pairScan,pairStep,pairClass]
        | cons a rest =>
            by_cases next : a = y
            · subst a
              by_cases foundX : x ∈ rest <;> by_cases foundY : y ∈ rest <;>
                simp [pairScan,pairStep,pairClass,different,Ne.symm different,pairScan_paired,foundX,foundY]
            · by_cases again : a = x
              · subst a
                simp [pairScan,pairStep,pairClass,pairScan_dead,different]
              · by_cases foundX : x ∈ rest <;> by_cases foundY : y ∈ rest <;>
                  simp [pairScan,pairStep,pairClass,again,next,pairScan_gapX,foundX,foundY]
      · by_cases second : z = y
        · subst z
          have impossible := cleanAdjacent_cons_second x y zs different
          by_cases found : x ∈ zs ∨ y ∈ zs <;>
            simp [pairScan,pairStep,pairClass,first,pairScan_firstY,found,impossible]
        · rw [cleanAdjacent_cons_other x y z zs first second]
          simpa [pairScan,pairStep,pairClass,first,second] using ih

def PairCount (nx ny : Nat) : PairState → Prop
  | .fresh => nx = 0 ∧ ny = 0
  | .firstX => nx = 1 ∧ ny = 0
  | .gapX => nx = 1 ∧ ny = 0
  | .firstY => nx = 0 ∧ ny = 1
  | .paired => nx = 1 ∧ ny = 1
  | .dead => True

theorem pairStep_count (kind : PairLetter) (state : PairState) (nx ny : Nat)
    (invariant : PairCount nx ny state) :
    PairCount (nx + if kind = .first then 1 else 0) (ny + if kind = .second then 1 else 0)
      (pairStep kind state) := by
  cases state <;> cases kind <;> simp_all [PairCount,pairStep] <;> omega

theorem pairScan_count (x y : Nat) (different : x ≠ y) (letters : List Nat)
    (state : PairState) (nx ny : Nat) (invariant : PairCount nx ny state) :
    PairCount (nx + letters.count x) (ny + letters.count y) (pairScan x y state letters) := by
  induction letters generalizing state nx ny with
  | nil => simpa [pairScan] using invariant
  | cons z zs ih =>
      have next := pairStep_count (pairClass x y z) state nx ny invariant
      have rest := ih (pairStep (pairClass x y z) state)
        (nx + if pairClass x y z = .first then 1 else 0)
        (ny + if pairClass x y z = .second then 1 else 0) next
      by_cases first : z = x
      · subst z
        simpa [pairScan,pairClass,different,List.count_cons_self,List.count_cons_of_ne different,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
      · by_cases second : z = y
        · subst z
          simpa [pairScan,pairClass,first,List.count_cons_self,List.count_cons_of_ne first,
            Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
        · simpa [pairScan,pairClass,first,second,List.count_cons_of_ne first,List.count_cons_of_ne second] using rest

namespace Semantics

def pairVal (x y z : Nat) : Fin 6 :=
  match pairClass x y z with
  | .first => 3
  | .second => 2
  | .other => 5

def pairValue (which : Bool) : PairState → Fin 6
  | .fresh => 5
  | .firstX => 3
  | .gapX => boundaryDrop which
  | .firstY => boundaryDrop which
  | .paired => 1
  | .dead => 0

theorem pairValue_step (which : Bool) (state : PairState) (kind : PairLetter) :
    mul which (pairValue which state) (match kind with | .first => 3 | .second => 2 | .other => 5) =
      pairValue which (pairStep kind state) := by
  cases which <;> cases state <;> cases kind <;> decide

theorem pairVal_run (which : Bool) (x y : Nat) (letters : List Nat) (state : PairState) :
    run which (pairVal x y) (pairValue which state) letters =
      pairValue which (pairScan x y state letters) := by
  induction letters generalizing state with
  | nil => rfl
  | cons z zs ih =>
      rw [run_cons,pairVal,pairValue_step,ih]
      rfl

theorem pair_probe (which : Bool) (x y : Nat) (letters : List Nat) (different : x ≠ y)
    (onceX : letters.count x = 1) (onceY : letters.count y = 1) :
    run which (pairVal x y) 5 letters = 1 ↔ CleanAdjacent x y letters := by
  have probe := pairVal_run which x y letters .fresh
  change run which (pairVal x y) 5 letters = _ at probe
  rw [probe,← pairScan_fresh_paired x y letters different]
  have invariant := pairScan_count x y different letters .fresh 0 0 ⟨rfl,rfl⟩
  cases result : pairScan x y .fresh letters with
  | fresh => cases which <;> decide
  | firstX => cases which <;> decide
  | paired => cases which <;> decide
  | dead => cases which <;> decide
  | gapX =>
      rw [result] at invariant
      have numbers : letters.count x = 1 ∧ letters.count y = 0 := by simpa [PairCount] using invariant
      exact False.elim (by omega)
  | firstY =>
      rw [result] at invariant
      have numbers : letters.count x = 0 ∧ letters.count y = 1 := by simpa [PairCount] using invariant
      exact False.elim (by omega)

theorem SameEval.cleanAdjacent_forward {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x y : Nat) (different : x ≠ y)
    (adjacent : CleanAdjacent x y left) : CleanAdjacent x y right := by
  have counts := adjacent.counts different
  have rightX := (same.countOne x).mp counts.1
  have rightY := (same.countOne y).mp counts.2
  apply (pair_probe which x y right different rightX rightY).mp
  rw [← same.runEq (pairVal x y) 5]
  exact (pair_probe which x y left different counts.1 counts.2).mpr adjacent

theorem SameEval.cleanAdjacent {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x y : Nat) (different : x ≠ y) :
    CleanAdjacent x y left ↔ CleanAdjacent x y right :=
  ⟨same.cleanAdjacent_forward x y different,same.symm.cleanAdjacent_forward x y different⟩

theorem SameEval.simpleAdjacent {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x y : Nat) : SimpleAdjacent x y left ↔ SimpleAdjacent x y right := by
  constructor
  · rintro ⟨different,adjacent⟩
    exact ⟨different,(same.cleanAdjacent x y different).mp adjacent⟩
  · rintro ⟨different,adjacent⟩
    exact ⟨different,(same.symm.cleanAdjacent x y different).mp adjacent⟩

end Semantics

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.CleanAdjacent.counts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cleanAdjacent_of_count_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.simpleAdjacent_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.pairScan_fresh_paired
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.pairStep_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.pairScan_count
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.pairValue_step
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.pairVal_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.pair_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.cleanAdjacent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.simpleAdjacent

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
