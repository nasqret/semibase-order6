import SemigroupBasis.CoRoots.S5_107Syntax
import SemigroupBasis.CoRoots.S5_793Factors
import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.S3_15

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_793Invariant

private def blockListEval
    (valuation : Nat → Fin 4) (letters : List Nat) : Fin 4 :=
  letters.foldl
    (fun value letter =>
      Generated.S4_71.table.mul value (valuation letter))
    (3 : Fin 4)

private theorem s4_71_left_identity (value : Fin 4) :
    Generated.S4_71.table.mul (3 : Fin 4) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem s4_71_right_identity (value : Fin 4) :
    Generated.S4_71.table.mul value (3 : Fin 4) = value := by
  apply Fin.ext
  revert value
  decide

private theorem block_eval_eq_listEval
    (valuation : Nat → Fin 4) (word : Word Nat) :
    Generated.S4_71.table.semigroup.eval valuation word =
      blockListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              Generated.S4_71.table.mul value (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              Generated.S4_71.table.mul value (valuation letter))
            (Generated.S4_71.table.mul (3 : Fin 4) (valuation head))
      rw [s4_71_left_identity]

private def multiplicityValuation
    (selected : Nat) : Nat → Fin 4 :=
  fun letter => if letter = selected then 1 else 3

private def multiplicityCode (count : Nat) : Fin 4 :=
  if count = 0 then 3 else if count = 1 then 1 else 0

private theorem multiplicityCode_selected (count : Nat) :
    Generated.S4_71.table.mul (multiplicityCode count) (1 : Fin 4) =
      multiplicityCode (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · have successorZero : count + 1 ≠ 0 := by omega
      have successorOne : count + 1 ≠ 1 := by omega
      simp [multiplicityCode, zero, one, successorZero, successorOne,
        Generated.S4_71.table, edmundsFourSeventyOneMul,
        edmundsFourSeventyOneOppositeMul]

private theorem multiplicityFold
    (selected : Nat) :
    ∀ (letters : List Nat) (initialCount : Nat),
      letters.foldl
          (fun value letter =>
            Generated.S4_71.table.mul value
              (multiplicityValuation selected letter))
          (multiplicityCode initialCount) =
        multiplicityCode
          (initialCount + letters.count selected)
  | [], initialCount => by
      simp
  | letter :: rest, initialCount => by
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [show multiplicityValuation selected selected = (1 : Fin 4) by
          simp [multiplicityValuation]]
        rw [multiplicityCode_selected]
        rw [multiplicityFold selected rest (initialCount + 1)]
        congr 1
        simp
        omega
      · rw [show multiplicityValuation selected letter = (3 : Fin 4) by
          simp [multiplicityValuation, equal]]
        rw [s4_71_right_identity]
        rw [multiplicityFold selected rest initialCount]
        simp [equal]

private theorem block_eval_multiplicity
    (word : Word Nat) (selected : Nat) :
    Generated.S4_71.table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityCode (word.toList.count selected) := by
  rw [block_eval_eq_listEval]
  unfold blockListEval
  simpa [multiplicityCode] using
    multiplicityFold selected word.toList 0

private theorem multiplicityCode_reflects_cap
    {leftCount rightCount : Nat}
    (equal :
      multiplicityCode leftCount =
        multiplicityCode rightCount) :
    Nat.min 2 leftCount = Nat.min 2 rightCount := by
  by_cases leftZero : leftCount = 0
  · subst leftCount
    by_cases rightZero : rightCount = 0
    · subst rightCount
      rfl
    · by_cases rightOne : rightCount = 1
      · subst rightCount
        simp [multiplicityCode] at equal
      · simp [multiplicityCode, rightZero, rightOne] at equal
  · by_cases leftOne : leftCount = 1
    · subst leftCount
      by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          rfl
        · simp [multiplicityCode, rightZero, rightOne] at equal
    · by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode, leftZero, leftOne] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          simp [multiplicityCode, leftZero, leftOne] at equal
        · simp only [Nat.min_def]
          split <;> split <;> omega

/-- The three-valued content invariant: absent, simple, or multiple. -/
theorem s4_71Valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (letter : Nat) :
    S5_107.cappedMultiplicity identity.lhs letter =
      S5_107.cappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [block_eval_multiplicity, block_eval_multiplicity] at evaluated
  exact multiplicityCode_reflects_cap evaluated

/-- Symbols consumed by the exact two-letter order scanner. -/
inductive OrderSymbol where
  | other
  | x
  | y
deriving DecidableEq

/-- Reachable states of the finite scanner used by the exact `S4_71`
order-and-gap marker. Besides capped counts, the state records which of
`x,y` occurred first and whether an `x` occurred after the first `y`. -/
inductive OrderGapState where
  | empty
  | onlyYOne
  | onlyYMany
  | onlyXOne
  | onlyXMany
  | simpleXY
  | simpleYX
  | xOneYManyXFirst
  | xOneYManyYFirst
  | xManyYOneBefore
  | xManyYOneAfterXFirst
  | xManyYOneAfterYFirst
  | xManyYManyBefore
  | xManyYManyAfterXFirst
  | xManyYManyAfterYFirst
deriving DecidableEq

def orderStep :
    OrderGapState → OrderSymbol → OrderGapState
  | state, .other => state
  | .empty, .x => .onlyXOne
  | .onlyYOne, .x => .simpleYX
  | .onlyYMany, .x => .xOneYManyYFirst
  | .onlyXOne, .x => .onlyXMany
  | .onlyXMany, .x => .onlyXMany
  | .simpleXY, .x => .xManyYOneAfterXFirst
  | .simpleYX, .x => .xManyYOneAfterYFirst
  | .xOneYManyXFirst, .x => .xManyYManyAfterXFirst
  | .xOneYManyYFirst, .x => .xManyYManyAfterYFirst
  | .xManyYOneBefore, .x => .xManyYOneAfterXFirst
  | .xManyYOneAfterXFirst, .x => .xManyYOneAfterXFirst
  | .xManyYOneAfterYFirst, .x => .xManyYOneAfterYFirst
  | .xManyYManyBefore, .x => .xManyYManyAfterXFirst
  | .xManyYManyAfterXFirst, .x => .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst, .x => .xManyYManyAfterYFirst
  | .empty, .y => .onlyYOne
  | .onlyYOne, .y => .onlyYMany
  | .onlyYMany, .y => .onlyYMany
  | .onlyXOne, .y => .simpleXY
  | .onlyXMany, .y => .xManyYOneBefore
  | .simpleXY, .y => .xOneYManyXFirst
  | .simpleYX, .y => .xOneYManyYFirst
  | .xOneYManyXFirst, .y => .xOneYManyXFirst
  | .xOneYManyYFirst, .y => .xOneYManyYFirst
  | .xManyYOneBefore, .y => .xManyYManyBefore
  | .xManyYOneAfterXFirst, .y => .xManyYManyAfterXFirst
  | .xManyYOneAfterYFirst, .y => .xManyYManyAfterYFirst
  | .xManyYManyBefore, .y => .xManyYManyBefore
  | .xManyYManyAfterXFirst, .y => .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst, .y => .xManyYManyAfterYFirst

private def orderStateValue : OrderGapState → Fin 4
  | .empty => 3
  | .onlyYOne => 1
  | .onlyYMany => 0
  | .onlyXOne => 2
  | .onlyXMany => 2
  | .simpleXY => 1
  | .simpleYX => 0
  | .xOneYManyXFirst => 0
  | .xOneYManyYFirst => 0
  | .xManyYOneBefore => 1
  | .xManyYOneAfterXFirst => 0
  | .xManyYOneAfterYFirst => 0
  | .xManyYManyBefore => 0
  | .xManyYManyAfterXFirst => 0
  | .xManyYManyAfterYFirst => 0

private def OrderGapState.xCount : OrderGapState → Nat
  | .empty | .onlyYOne | .onlyYMany => 0
  | .onlyXOne | .simpleXY | .simpleYX
  | .xOneYManyXFirst | .xOneYManyYFirst => 1
  | .onlyXMany | .xManyYOneBefore
  | .xManyYOneAfterXFirst | .xManyYOneAfterYFirst
  | .xManyYManyBefore | .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst => 2

private def OrderGapState.yCount : OrderGapState → Nat
  | .empty | .onlyXOne | .onlyXMany => 0
  | .onlyYOne | .simpleXY | .simpleYX
  | .xManyYOneBefore | .xManyYOneAfterXFirst
  | .xManyYOneAfterYFirst => 1
  | .onlyYMany | .xOneYManyXFirst | .xOneYManyYFirst
  | .xManyYManyBefore | .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst => 2

def orderSymbol (x y letter : Nat) : OrderSymbol :=
  if letter = x then .x else if letter = y then .y else .other

private def orderSymbolValue : OrderSymbol → Fin 4
  | .other => 3
  | .x => 2
  | .y => 1

private def orderValuation (x y : Nat) : Nat → Fin 4 :=
  fun letter => orderSymbolValue (orderSymbol x y letter)

def orderGapScan (word : Word Nat) (x y : Nat) : OrderGapState :=
  word.toList.foldl
    (fun state letter => orderStep state (orderSymbol x y letter))
    .empty

private theorem orderStep_value
    (state : OrderGapState) (symbol : OrderSymbol) :
    Generated.S4_71.table.mul
        (orderStateValue state) (orderSymbolValue symbol) =
      orderStateValue (orderStep state symbol) := by
  cases state <;> cases symbol <;> decide

private theorem orderStep_xCount
    (state : OrderGapState) (symbol : OrderSymbol) :
    (orderStep state symbol).xCount =
      Nat.min 2
        (state.xCount + if symbol = .x then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem orderStep_yCount
    (state : OrderGapState) (symbol : OrderSymbol) :
    (orderStep state symbol).yCount =
      Nat.min 2
        (state.yCount + if symbol = .y then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem orderState_xCount_le_two (state : OrderGapState) :
    state.xCount ≤ 2 := by
  cases state <;> decide

private theorem orderState_yCount_le_two (state : OrderGapState) :
    state.yCount ≤ 2 := by
  cases state <;> decide

private theorem cap_two_cap_add (left right : Nat) :
    Nat.min 2 (Nat.min 2 left + right) =
      Nat.min 2 (left + right) := by
  by_cases capped : 2 ≤ left
  · have inner : Nat.min 2 left = 2 :=
      Nat.min_eq_left capped
    calc
      Nat.min 2 (Nat.min 2 left + right) =
          Nat.min 2 (2 + right) := by rw [inner]
      _ = 2 := Nat.min_eq_left (by omega)
      _ = Nat.min 2 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 2 := by omega
    have inner : Nat.min 2 left = left :=
      Nat.min_eq_right below
    rw [inner]

private theorem orderFold_value (x y : Nat) :
    ∀ (letters : List Nat) (initial : OrderGapState),
      letters.foldl
          (fun value letter =>
            Generated.S4_71.table.mul value
              (orderValuation x y letter))
          (orderStateValue initial) =
        orderStateValue
          (letters.foldl
            (fun state letter =>
              orderStep state (orderSymbol x y letter))
            initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons, orderValuation]
      rw [orderStep_value]
      exact orderFold_value x y rest
        (orderStep initial (orderSymbol x y letter))

private theorem orderFold_xCount (x y : Nat) :
    ∀ (letters : List Nat) (initial : OrderGapState),
      (letters.foldl
          (fun state letter =>
            orderStep state (orderSymbol x y letter))
          initial).xCount =
        Nat.min 2 (initial.xCount + letters.count x)
  | [], initial => by
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact
        (Nat.min_eq_right (orderState_xCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [orderFold_xCount x y rest]
      rw [orderStep_xCount]
      by_cases equal : letter = x
      · subst letter
        simp only [orderSymbol, if_pos, List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotX : orderSymbol x y letter ≠ .x := by
          unfold orderSymbol
          rw [if_neg equal]
          split <;> decide
        rw [if_neg symbolNotX]
        rw [cap_two_cap_add]
        simp [equal]

private theorem orderFold_yCount (x y : Nat) (different : x ≠ y) :
    ∀ (letters : List Nat) (initial : OrderGapState),
      (letters.foldl
          (fun state letter =>
            orderStep state (orderSymbol x y letter))
          initial).yCount =
        Nat.min 2 (initial.yCount + letters.count y)
  | [], initial => by
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact
        (Nat.min_eq_right (orderState_yCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [orderFold_yCount x y different rest]
      rw [orderStep_yCount]
      by_cases isY : letter = y
      · subst letter
        have notX : y ≠ x := Ne.symm different
        simp only [orderSymbol, if_neg notX, if_pos,
          List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotY : orderSymbol x y letter ≠ .y := by
          unfold orderSymbol
          split <;> decide
        rw [if_neg symbolNotY]
        rw [cap_two_cap_add]
        simp [isY]

private theorem block_eval_order
    (word : Word Nat) (x y : Nat) :
    Generated.S4_71.table.semigroup.eval
        (orderValuation x y) word =
      orderStateValue (orderGapScan word x y) := by
  rw [block_eval_eq_listEval]
  unfold blockListEval orderGapScan
  simpa [orderStateValue] using
    orderFold_value x y word.toList .empty

private theorem orderGapScan_xCount
    (word : Word Nat) (x y : Nat) :
    (orderGapScan word x y).xCount =
      S5_107.cappedMultiplicity word x := by
  unfold orderGapScan S5_107.cappedMultiplicity
  simpa [OrderGapState.xCount] using
    orderFold_xCount x y word.toList .empty

private theorem orderGapScan_yCount
    (word : Word Nat) {x y : Nat} (different : x ≠ y) :
    (orderGapScan word x y).yCount =
      S5_107.cappedMultiplicity word y := by
  unfold orderGapScan S5_107.cappedMultiplicity
  simpa [OrderGapState.yCount] using
    orderFold_yCount x y different word.toList .empty

/-- Two globally simple variables occur in this order. The scanner ignores
all other variables, so this pairwise relation is exactly the ordered
simple-variable sequence invariant. -/
def SimplePrecedes (word : Word Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ orderGapScan word x y = .simpleXY

/-- `x` is multiple, `y` is simple, and the last occurrence of `x` lies
before `y`. The truth vector over the ordered simple variables identifies
the unique simple-variable gap containing the last occurrence of `x`. -/
def MultipleLastBeforeSimple
    (word : Word Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ orderGapScan word x y = .xManyYOneBefore

private theorem state_eq_simpleXY_of_counts_value
    (state : OrderGapState)
    (xCount : state.xCount = 1)
    (yCount : state.yCount = 1)
    (value : orderStateValue state = 1) :
    state = .simpleXY := by
  cases state <;>
    simp_all [OrderGapState.xCount, OrderGapState.yCount,
      orderStateValue]

private theorem state_eq_xManyYOneBefore_of_counts_value
    (state : OrderGapState)
    (xCount : state.xCount = 2)
    (yCount : state.yCount = 1)
    (value : orderStateValue state = 1) :
    state = .xManyYOneBefore := by
  cases state <;>
    simp_all [OrderGapState.xCount, OrderGapState.yCount,
      orderStateValue]

private theorem simplePrecedes_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      orderStateValue (orderGapScan left x y) =
        orderStateValue (orderGapScan right x y))
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter)
    (precedes : SimplePrecedes left x y) :
    SimplePrecedes right x y := by
  rcases precedes with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount :
      (orderGapScan right x y).xCount = 1 := by
    calc
      (orderGapScan right x y).xCount =
          S5_107.cappedMultiplicity right x :=
        orderGapScan_xCount right x y
      _ = S5_107.cappedMultiplicity left x :=
        (capped x).symm
      _ = (orderGapScan left x y).xCount :=
        (orderGapScan_xCount left x y).symm
      _ = 1 := by rw [leftState]; rfl
  have rightYCount :
      (orderGapScan right x y).yCount = 1 := by
    calc
      (orderGapScan right x y).yCount =
          S5_107.cappedMultiplicity right y :=
        orderGapScan_yCount right different
      _ = S5_107.cappedMultiplicity left y :=
        (capped y).symm
      _ = (orderGapScan left x y).yCount :=
        (orderGapScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      orderStateValue (orderGapScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact state_eq_simpleXY_of_counts_value
    (orderGapScan right x y)
    rightXCount rightYCount rightValue

private theorem lastBefore_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      orderStateValue (orderGapScan left x y) =
        orderStateValue (orderGapScan right x y))
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity left letter =
          S5_107.cappedMultiplicity right letter)
    (before : MultipleLastBeforeSimple left x y) :
    MultipleLastBeforeSimple right x y := by
  rcases before with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount :
      (orderGapScan right x y).xCount = 2 := by
    calc
      (orderGapScan right x y).xCount =
          S5_107.cappedMultiplicity right x :=
        orderGapScan_xCount right x y
      _ = S5_107.cappedMultiplicity left x :=
        (capped x).symm
      _ = (orderGapScan left x y).xCount :=
        (orderGapScan_xCount left x y).symm
      _ = 2 := by rw [leftState]; rfl
  have rightYCount :
      (orderGapScan right x y).yCount = 1 := by
    calc
      (orderGapScan right x y).yCount =
          S5_107.cappedMultiplicity right y :=
        orderGapScan_yCount right different
      _ = S5_107.cappedMultiplicity left y :=
        (capped y).symm
      _ = (orderGapScan left x y).yCount :=
        (orderGapScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      orderStateValue (orderGapScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact state_eq_xManyYOneBefore_of_counts_value
    (orderGapScan right x y)
    rightXCount rightYCount rightValue

theorem s4_71Valid_simplePrecedes
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    SimplePrecedes identity.lhs x y ↔
      SimplePrecedes identity.rhs x y := by
  have evaluated := valid (orderValuation x y)
  rw [block_eval_order, block_eval_order] at evaluated
  constructor
  · exact simplePrecedes_forward evaluated capped
  · exact simplePrecedes_forward evaluated.symm
      (fun letter => (capped letter).symm)

theorem s4_71Valid_multipleLastBeforeSimple
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    MultipleLastBeforeSimple identity.lhs x y ↔
      MultipleLastBeforeSimple identity.rhs x y := by
  have evaluated := valid (orderValuation x y)
  rw [block_eval_order, block_eval_order] at evaluated
  constructor
  · exact lastBefore_forward evaluated capped
  · exact lastBefore_forward evaluated.symm
      (fun letter => (capped letter).symm)

/-- The exact invariant advertised for the family. `simpleSequence` is the
pairwise order relation of all simple variables; `lastGap` is the cut vector
of each multiple variable against that ordered sequence. `blockTheory` keeps
the exact `S4_71` semantic certificate used by the normalization replay. -/
structure SameFirstSimpleLastGapSignature
    (left right : Word Nat) : Prop where
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup
  first : left.head = right.head
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleSequence :
    ∀ x y,
      SimplePrecedes left x y ↔ SimplePrecedes right x y
  lastGap :
    ∀ x y,
      MultipleLastBeforeSimple left x y ↔
        MultipleLastBeforeSimple right x y

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameFirstSimpleLastGapSignature left right

theorem sameSignature_of_s4_71_valid_head_eq
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (headEqual : identity.lhs.head = identity.rhs.head) :
    SameFirstSimpleLastGapSignature identity.lhs identity.rhs := by
  have capped :
      ∀ letter,
        S5_107.cappedMultiplicity identity.lhs letter =
          S5_107.cappedMultiplicity identity.rhs letter :=
    fun letter =>
      s4_71Valid_cappedMultiplicity identity blockValid letter
  exact
    ⟨blockValid, headEqual, capped,
      fun x y =>
        s4_71Valid_simplePrecedes identity blockValid capped x y,
      fun x y =>
        s4_71Valid_multipleLastBeforeSimple
          identity blockValid capped x y⟩

namespace SameFirstSimpleLastGapSignature

theorem refl (word : Word Nat) :
    SameFirstSimpleLastGapSignature word word :=
  sameSignature_of_s4_71_valid_head_eq
    ⟨word, word⟩ (fun _ => rfl) rfl

theorem symm {left right : Word Nat}
    (same : SameFirstSimpleLastGapSignature left right) :
    SameFirstSimpleLastGapSignature right left :=
  ⟨fun valuation => (same.blockTheory valuation).symm,
    same.first.symm,
    fun letter => (same.capped letter).symm,
    fun x y => (same.simpleSequence x y).symm,
    fun x y => (same.lastGap x y).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameFirstSimpleLastGapSignature left middle)
    (second : SameFirstSimpleLastGapSignature middle right) :
    SameFirstSimpleLastGapSignature left right :=
  ⟨fun valuation =>
      (first.blockTheory valuation).trans
        (second.blockTheory valuation),
    first.first.trans second.first,
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.simpleSequence x y).trans
        (second.simpleSequence x y),
    fun x y =>
      (first.lastGap x y).trans (second.lastGap x y)⟩

theorem absent {left right : Word Nat}
    (same : SameFirstSimpleLastGapSignature left right)
    (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same : SameFirstSimpleLastGapSignature left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameFirstSimpleLastGapSignature left right)
    (letter : Nat) :
    S5_107.SimpleIn left letter ↔
      S5_107.SimpleIn right letter := by
  unfold S5_107.SimpleIn
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff,
    same.capped letter]

end SameFirstSimpleLastGapSignature

theorem catalogueS2_4_table_eq_leftZeroTwo :
    Generated.Catalogue.S2_4.table = leftZeroTwo := by
  unfold Generated.Catalogue.S2_4.table
    Generated.Catalogue.S2_4.mul leftZeroTwo
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun z => if z = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

end S5_793Invariant

namespace S5_793

/-- Every derivation from the eight laws preserves the complete
first/simple-sequence/last-gap signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_793Invariant.SameFirstSimpleLastGapSignature left right := by
  have blockModels :
      Models Generated.S4_71.table.semigroup basis :=
    models_of_finite_checks Generated.S4_71.table (by decide)
  have firstModels :
      Models leftZeroTwo.semigroup basis :=
    models_of_finite_checks leftZeroTwo (by decide)
  exact S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
    ⟨left, right⟩
    (fun valuation => derivation.sound blockModels valuation)
    (S5_793Invariant.leftZeroValid_head_eq
      ⟨left, right⟩
      (fun valuation => derivation.sound firstModels valuation))

end S5_793

namespace S5_793FamilyInvariant

namespace S5_793

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_793.table.semigroup) :
    S5_793Invariant.SameFirstSimpleLastGapSignature
      identity.lhs identity.rhs := by
  have markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    rw [← S5_793Invariant.catalogueS2_4_table_eq_leftZeroTwo]
    exact S5_793Factors.S5_793.valid_s2_4 identity valid
  exact S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
    identity
    (S5_793Factors.S5_793.valid_s4_71 identity valid)
    (S5_793Invariant.leftZeroValid_head_eq identity markerValid)

end S5_793

namespace S5_801

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_801.table.semigroup) :
    S5_793Invariant.SameFirstSimpleLastGapSignature
      identity.lhs identity.rhs := by
  have markerValid :
      identity.SatisfiedBy leftNormalBandFifteen.semigroup := by
    have factorValid :=
      S5_793Factors.S5_801.valid_s3_15 identity valid
    rw [← Generated.S3_15.table_eq_canonical_catalogue,
      Generated.S3_15.table_eq_catalogue_model] at factorValid
    exact factorValid
  exact S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
    identity
    (S5_793Factors.S5_801.valid_s4_71 identity valid)
    (leftNormalBandFifteenValid_head_eq identity markerValid)

end S5_801

namespace S5_843

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_843.table.semigroup) :
    S5_793Invariant.SameFirstSimpleLastGapSignature
      identity.lhs identity.rhs := by
  have markerValid :
      identity.SatisfiedBy leftNormalBandFifteen.semigroup := by
    have factorValid :=
      S5_793Factors.S5_843.valid_s3_15 identity valid
    rw [← Generated.S3_15.table_eq_canonical_catalogue,
      Generated.S3_15.table_eq_catalogue_model] at factorValid
    exact factorValid
  exact S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
    identity
    (S5_793Factors.S5_843.valid_s4_71 identity valid)
    (leftNormalBandFifteenValid_head_eq identity markerValid)

end S5_843

end S5_793FamilyInvariant

end SemigroupBasis.CoRoots
