import SemigroupBasis.Examples.SymmetricThreeCompletenessScanInvariant

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

/-- Boolean vectors used by the finite Walsh separator. -/
abbrev BitState (width : Nat) := Fin width → Fin 2

def bitTail {width : Nat} (state : BitState (width + 1)) :
    BitState width :=
  fun index => state index.succ

def bitCons {width : Nat} (head : Fin 2) (tail : BitState width) :
    BitState (width + 1) :=
  Fin.cases head tail

@[simp]
theorem bitCons_zero {width : Nat} (head : Fin 2) (tail : BitState width) :
    bitCons head tail 0 = head :=
  rfl

@[simp]
theorem bitCons_succ {width : Nat} (head : Fin 2) (tail : BitState width)
    (index : Fin width) :
    bitCons head tail index.succ = tail index :=
  rfl

@[simp]
theorem bitTail_bitCons {width : Nat} (head : Fin 2)
    (tail : BitState width) :
    bitTail (bitCons head tail) = tail := by
  funext index
  rfl

/-- Constructive equality for finite Boolean vectors. -/
def bitStateDecidableEq : (width : Nat) → DecidableEq (BitState width)
  | 0 => fun left right =>
      isTrue (by
        funext impossible
        exact Fin.elim0 impossible)
  | width + 1 => fun left right =>
      match decEq (left 0) (right 0) with
      | isFalse headDifferent =>
          isFalse (fun same => headDifferent (congrFun same 0))
      | isTrue headSame =>
          match bitStateDecidableEq width (bitTail left) (bitTail right) with
          | isFalse tailDifferent =>
              isFalse (fun same => tailDifferent (congrArg bitTail same))
          | isTrue tailSame =>
              isTrue (by
                funext index
                refine Fin.cases headSame (fun smaller => ?_) index
                exact congrFun tailSame smaller)

instance bitStateInstDecidableEq (width : Nat) :
    DecidableEq (BitState width) :=
  bitStateDecidableEq width

private theorem finThreeVector_add_assoc
    (first second third : Fin 3) :
    (first + second) + third = first + (second + third) := by
  decide +revert

private theorem finThreeVector_add_left_comm
    (first second third : Fin 3) :
    first + (second + third) = second + (first + third) := by
  decide +revert

private theorem finTwo_nonzero_eq_one (value : Fin 2)
    (nonzero : value ≠ 0) : value = 1 := by
  apply Fin.ext
  omega

private theorem finTwoVector_zero_mul (value : Fin 2) : 0 * value = 0 := by
  decide +revert

private theorem finTwoVector_mul_zero (value : Fin 2) : value * 0 = 0 := by
  decide +revert

private theorem finTwoVector_one_mul (value : Fin 2) : 1 * value = value := by
  decide +revert

private theorem finTwoVector_zero_add (value : Fin 2) : 0 + value = value := by
  decide +revert

private theorem finThreeVector_val_add (first second : Fin 3) :
    (first + second).val = (first.val + second.val) % 3 := by
  decide +revert

/-- Additive inverse in `Fin 3`, kept concrete so this module needs no
abstract group interface. -/
def negateThree : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | _ => 1

private theorem negateThree_add (left right : Fin 3) :
    negateThree (left + right) = negateThree left + negateThree right := by
  decide +revert

private theorem walshSign_toggle (value : Fin 2) :
    walshSign (1 + value) = negateThree (walshSign value) := by
  decide +revert

private theorem finThree_split_injective
    (leftZero leftOne rightZero rightOne : Fin 3)
    (positive : leftZero + leftOne = rightZero + rightOne)
    (negative : leftZero + negateThree leftOne =
      rightZero + negateThree rightOne) :
    leftZero = rightZero ∧ leftOne = rightOne := by
  decide +revert

/-- Dot product of two Boolean vectors. -/
def bitDot : {width : Nat} → BitState width → BitState width → Fin 2
  | 0, _, _ => 0
  | _ + 1, assignment, state =>
      assignment 0 * state 0 +
        bitDot (bitTail assignment) (bitTail state)

def bitWalshSign {width : Nat}
    (assignment state : BitState width) : Fin 3 :=
  walshSign (bitDot assignment state)

def bitWalshSum {width : Nat} (assignment : BitState width) :
    List (BitState width) → Fin 3
  | [] => 0
  | state :: rest =>
      bitWalshSign assignment state + bitWalshSum assignment rest

@[simp]
theorem bitWalshSum_nil {width : Nat} (assignment : BitState width) :
    bitWalshSum assignment [] = 0 :=
  rfl

@[simp]
theorem bitWalshSum_cons {width : Nat} (assignment : BitState width)
    (state : BitState width) (rest : List (BitState width)) :
    bitWalshSum assignment (state :: rest) =
      bitWalshSign assignment state + bitWalshSum assignment rest :=
  rfl

private theorem bitWalshSign_head_zero {width : Nat}
    (assignment : BitState width) (state : BitState (width + 1)) :
    bitWalshSign (bitCons 0 assignment) state =
      bitWalshSign assignment (bitTail state) := by
  unfold bitWalshSign
  simp only [bitDot, bitCons_zero, bitTail_bitCons,
    finTwoVector_zero_mul, finTwoVector_zero_add]

private theorem bitWalshSign_head_one_of_zero {width : Nat}
    (assignment : BitState width) (state : BitState (width + 1))
    (zero : state 0 = 0) :
    bitWalshSign (bitCons 1 assignment) state =
      bitWalshSign assignment (bitTail state) := by
  unfold bitWalshSign
  simp only [bitDot, bitCons_zero, bitTail_bitCons, zero,
    finTwoVector_mul_zero, finTwoVector_zero_add]

private theorem bitWalshSign_head_one_of_nonzero {width : Nat}
    (assignment : BitState width) (state : BitState (width + 1))
    (nonzero : state 0 ≠ 0) :
    bitWalshSign (bitCons 1 assignment) state =
      negateThree (bitWalshSign assignment (bitTail state)) := by
  have one := finTwo_nonzero_eq_one (state 0) nonzero
  unfold bitWalshSign
  simp only [bitDot, bitCons_zero, bitTail_bitCons, one,
    finTwoVector_one_mul]
  exact walshSign_toggle _

/-- Tails of the vectors whose leading bit is zero. -/
def zeroTails {width : Nat} :
    List (BitState (width + 1)) → List (BitState width)
  | [] => []
  | state :: rest =>
      if state 0 = 0 then bitTail state :: zeroTails rest
      else zeroTails rest

/-- Tails of the vectors whose leading bit is one. -/
def oneTails {width : Nat} :
    List (BitState (width + 1)) → List (BitState width)
  | [] => []
  | state :: rest =>
      if state 0 = 0 then oneTails rest
      else bitTail state :: oneTails rest

private theorem bitWalshSum_head_zero_split {width : Nat}
    (assignment : BitState width) :
    ∀ states : List (BitState (width + 1)),
      bitWalshSum (bitCons 0 assignment) states =
        bitWalshSum assignment (zeroTails states) +
          bitWalshSum assignment (oneTails states)
  | [] => rfl
  | state :: rest => by
      rw [bitWalshSum_cons, bitWalshSign_head_zero,
        bitWalshSum_head_zero_split assignment rest]
      by_cases zero : state 0 = 0
      · simp only [zeroTails, oneTails, zero, if_pos,
          bitWalshSum_cons]
        exact (finThreeVector_add_assoc _ _ _).symm
      · simp only [zeroTails, oneTails, zero]
        exact finThreeVector_add_left_comm _ _ _

private theorem bitWalshSum_head_one_split {width : Nat}
    (assignment : BitState width) :
    ∀ states : List (BitState (width + 1)),
      bitWalshSum (bitCons 1 assignment) states =
        bitWalshSum assignment (zeroTails states) +
          negateThree (bitWalshSum assignment (oneTails states))
  | [] => rfl
  | state :: rest => by
      rw [bitWalshSum_cons,
        bitWalshSum_head_one_split assignment rest]
      by_cases zero : state 0 = 0
      · rw [bitWalshSign_head_one_of_zero assignment state zero]
        simp only [zeroTails, oneTails, zero, if_pos,
          bitWalshSum_cons]
        exact (finThreeVector_add_assoc _ _ _).symm
      · rw [bitWalshSign_head_one_of_nonzero assignment state zero]
        rw [zeroTails, oneTails, if_neg zero, if_neg zero,
          bitWalshSum_cons, negateThree_add]
        exact finThreeVector_add_left_comm _ _ _

private theorem bitState_eq_of_head_tail {width : Nat}
    {left right : BitState (width + 1)}
    (head : left 0 = right 0) (tail : bitTail left = bitTail right) :
    left = right := by
  funext index
  refine Fin.cases ?_ (fun smaller => ?_) index
  · exact head
  · exact congrFun tail smaller

private theorem count_eq_zeroTails_of_head_zero {width : Nat}
    (target : BitState (width + 1)) (targetZero : target 0 = 0) :
    ∀ states : List (BitState (width + 1)),
      states.count target = (zeroTails states).count (bitTail target)
  | [] => rfl
  | state :: rest => by
      by_cases stateZero : state 0 = 0
      · by_cases sameTail : bitTail state = bitTail target
        · have same : state = target := bitState_eq_of_head_tail
            (stateZero.trans targetZero.symm) sameTail
          subst state
          simp [zeroTails, targetZero,
            count_eq_zeroTails_of_head_zero target targetZero rest]
        · have different : state ≠ target := by
            intro same
            exact sameTail (congrArg bitTail same)
          simp [zeroTails, stateZero, different, sameTail,
            count_eq_zeroTails_of_head_zero target targetZero rest]
      · have different : state ≠ target := by
          intro same
          apply stateZero
          rw [same, targetZero]
        simp [zeroTails, stateZero, different,
          count_eq_zeroTails_of_head_zero target targetZero rest]

private theorem count_eq_oneTails_of_head_nonzero {width : Nat}
    (target : BitState (width + 1)) (targetNonzero : target 0 ≠ 0) :
    ∀ states : List (BitState (width + 1)),
      states.count target = (oneTails states).count (bitTail target)
  | [] => rfl
  | state :: rest => by
      by_cases stateZero : state 0 = 0
      · have different : state ≠ target := by
          intro same
          apply targetNonzero
          rw [← same, stateZero]
        simp [oneTails, stateZero, different,
          count_eq_oneTails_of_head_nonzero target targetNonzero rest]
      · have heads : state 0 = target 0 :=
          (finTwo_nonzero_eq_one (state 0) stateZero).trans
            (finTwo_nonzero_eq_one (target 0) targetNonzero).symm
        by_cases sameTail : bitTail state = bitTail target
        · have same : state = target :=
            bitState_eq_of_head_tail heads sameTail
          subst state
          simp [oneTails, targetNonzero,
            count_eq_oneTails_of_head_nonzero target targetNonzero rest]
        · have different : state ≠ target := by
            intro same
            exact sameTail (congrArg bitTail same)
          simp [oneTails, stateZero, different, sameTail,
            count_eq_oneTails_of_head_nonzero target targetNonzero rest]

def residueThree (count : Nat) : Fin 3 :=
  ⟨count % 3, Nat.mod_lt _ (by decide)⟩

private theorem residueThree_succ (count : Nat) :
    1 + residueThree count = residueThree (count + 1) := by
  apply Fin.ext
  rw [finThreeVector_val_add]
  simp only [residueThree]
  omega

private theorem bitState_zero_unique (left right : BitState 0) :
    left = right := by
  funext impossible
  exact Fin.elim0 impossible

private theorem count_width_zero (target : BitState 0) :
    ∀ states : List (BitState 0), states.count target = states.length
  | [] => rfl
  | state :: rest => by
      have same := bitState_zero_unique state target
      subst state
      simp [count_width_zero target rest]

private theorem bitWalshSum_width_zero (assignment : BitState 0) :
    ∀ states : List (BitState 0),
      bitWalshSum assignment states = residueThree states.length
  | [] => rfl
  | state :: rest => by
      rw [bitWalshSum_cons, bitWalshSum_width_zero assignment rest]
      have same := bitState_zero_unique state assignment
      subst state
      change 1 + residueThree rest.length = residueThree (rest.length + 1)
      exact residueThree_succ rest.length

/-- Finite Walsh injectivity over `Fin 3`.  Equality under every Boolean
character determines every vector multiplicity modulo three. -/
theorem bitWalshSum_modCounts :
    ∀ (width : Nat) (left right : List (BitState width)),
      (∀ assignment : BitState width,
        bitWalshSum assignment left = bitWalshSum assignment right) →
      ∀ target : BitState width,
        left.count target % 3 = right.count target % 3
  | 0, left, right, transforms, target => by
      have equality := transforms target
      rw [bitWalshSum_width_zero, bitWalshSum_width_zero] at equality
      have values := congrArg Fin.val equality
      simp only [residueThree] at values
      rw [count_width_zero target left, count_width_zero target right]
      exact values
  | width + 1, left, right, transforms, target => by
      have zeroTransforms :
          ∀ assignment : BitState width,
            bitWalshSum assignment (zeroTails left) =
              bitWalshSum assignment (zeroTails right) := by
        intro assignment
        have positive := transforms (bitCons 0 assignment)
        have negative := transforms (bitCons 1 assignment)
        rw [bitWalshSum_head_zero_split,
          bitWalshSum_head_zero_split] at positive
        rw [bitWalshSum_head_one_split,
          bitWalshSum_head_one_split] at negative
        exact (finThree_split_injective _ _ _ _ positive negative).1
      have oneTransforms :
          ∀ assignment : BitState width,
            bitWalshSum assignment (oneTails left) =
              bitWalshSum assignment (oneTails right) := by
        intro assignment
        have positive := transforms (bitCons 0 assignment)
        have negative := transforms (bitCons 1 assignment)
        rw [bitWalshSum_head_zero_split,
          bitWalshSum_head_zero_split] at positive
        rw [bitWalshSum_head_one_split,
          bitWalshSum_head_one_split] at negative
        exact (finThree_split_injective _ _ _ _ positive negative).2
      by_cases targetZero : target 0 = 0
      · rw [count_eq_zeroTails_of_head_zero target targetZero left,
          count_eq_zeroTails_of_head_zero target targetZero right]
        exact bitWalshSum_modCounts width (zeroTails left)
          (zeroTails right) zeroTransforms (bitTail target)
      · rw [count_eq_oneTails_of_head_nonzero target targetZero left,
          count_eq_oneTails_of_head_nonzero target targetZero right]
        exact bitWalshSum_modCounts width (oneTails left)
          (oneTails right) oneTransforms (bitTail target)

end SemigroupBasis.Examples.SymmetricThreeCompleteness
