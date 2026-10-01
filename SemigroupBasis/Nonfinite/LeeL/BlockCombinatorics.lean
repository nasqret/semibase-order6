import SemigroupBasis.Nonfinite.LeeL.Context

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

namespace BlockCombinatorics

/-- The two values used in the proof of Zhang--Luo Lemma 5:
`false` is the idempotent `e`, and `true` is the idempotent `d`. -/
def colorValue : Bool → Fin 6
  | false => 5
  | true => 4

private def colorRun (initial : Fin 6) : List Bool → Fin 6
  | [] => initial
  | color :: rest => colorRun (mul initial (colorValue color)) rest

def colorEval : List Bool → Fin 6
  | [] => 0
  | color :: rest => colorRun (colorValue color) rest

private theorem colorRun_zero_ne_one (colors : List Bool) :
    colorRun 0 colors ≠ 1 := by
  induction colors with
  | nil => decide
  | cons color rest ih =>
      cases color <;> simpa [colorRun, colorValue, mul] using ih

private theorem colorRun_one_eq_one_iff (colors : List Bool) :
    colorRun 1 colors = 1 ↔ ∀ color ∈ colors, color = false := by
  induction colors with
  | nil => simp [colorRun]
  | cons color rest ih =>
      cases color <;>
        simp [colorRun, colorValue, mul, ih, colorRun_zero_ne_one]

private theorem colorRun_two_ne_one (colors : List Bool) :
    colorRun 2 colors ≠ 1 := by
  induction colors with
  | nil => decide
  | cons color rest ih =>
      cases color <;>
        simp [colorRun, colorValue, mul, ih, colorRun_zero_ne_one]

private theorem colorRun_four_ne_one (colors : List Bool) :
    colorRun 4 colors ≠ 1 := by
  induction colors with
  | nil => decide
  | cons color rest ih =>
      cases color <;>
        simp [colorRun, colorValue, mul, ih, colorRun_two_ne_one]

private theorem eq_replicate_false_of_all_false
    (colors : List Bool)
    (allFalse : ∀ color ∈ colors, color = false) :
    colors = List.replicate colors.length false := by
  induction colors with
  | nil => rfl
  | cons color rest ih =>
      have colorFalse := allFalse color (List.Mem.head rest)
      subst color
      have restFalse : ∀ value ∈ rest, value = false := by
        intro value member
        exact allFalse value (List.Mem.tail false member)
      change false :: rest =
        List.replicate (Nat.succ rest.length) false
      rw [List.replicate_succ]
      exact congrArg (List.cons false) (ih restFalse)

private theorem colorRun_three_eq_one_iff (colors : List Bool) :
    colorRun 3 colors = 1 ↔
      ∃ trueCount falseCount,
        colors =
          List.replicate trueCount true ++
            List.replicate (falseCount + 1) false := by
  induction colors with
  | nil =>
      simp [colorRun]
  | cons color rest ih =>
      cases color
      · simp only [colorRun]
        change colorRun 1 rest = 1 ↔ _
        constructor
        · intro allFalse
          refine ⟨0, rest.length, ?_⟩
          simp only [List.replicate_zero, List.nil_append]
          have restShape :
              rest = List.replicate rest.length false := by
            exact eq_replicate_false_of_all_false rest
              ((colorRun_one_eq_one_iff rest).mp allFalse)
          rw [restShape]
          simp [List.replicate_succ]
        · rintro ⟨trueCount, falseCount, shape⟩
          have trueCountZero : trueCount = 0 := by
            cases trueCount with
            | zero => rfl
            | succ trueCount =>
                change false :: rest =
                  true ::
                    (List.replicate trueCount true ++
                      List.replicate (falseCount + 1) false) at shape
                exact Bool.noConfusion (List.cons.inj shape).1
          subst trueCount
          simp only [List.replicate_zero, List.nil_append] at shape
          apply (colorRun_one_eq_one_iff rest).mpr
          intro value member
          have restShape : rest = List.replicate falseCount false := by
            have tails := congrArg List.tail shape
            simpa [List.replicate_succ, Nat.add_comm] using tails
          rw [restShape] at member
          exact List.eq_of_mem_replicate member
      · simp only [colorRun]
        change colorRun 3 rest = 1 ↔ _
        rw [ih]
        constructor
        · rintro ⟨trueCount, falseCount, shape⟩
          exact ⟨trueCount + 1, falseCount, by
            simp [shape, List.replicate_succ]⟩
        · rintro ⟨trueCount, falseCount, shape⟩
          cases trueCount with
          | zero =>
              change true :: rest =
                false :: List.replicate falseCount false at shape
              exact Bool.noConfusion (List.cons.inj shape).1
          | succ trueCount =>
              have tails := congrArg List.tail shape
              exact ⟨trueCount, falseCount, by
                simpa [List.replicate_succ] using tails⟩

private theorem colorRun_five_eq_one_iff (colors : List Bool) :
    colorRun 5 colors = 1 ↔
      ∃ falsePrefix trueTail falseTail,
        colors =
          List.replicate falsePrefix false ++
            List.replicate (trueTail + 1) true ++
            List.replicate (falseTail + 1) false := by
  induction colors with
  | nil =>
      simp [colorRun]
  | cons color rest ih =>
      cases color
      · simp only [colorRun]
        change colorRun 5 rest = 1 ↔ _
        rw [ih]
        constructor
        · rintro ⟨falsePrefix, trueTail, falseTail, shape⟩
          exact ⟨falsePrefix + 1, trueTail, falseTail, by
            simp [shape, List.replicate_succ]⟩
        · rintro ⟨falsePrefix, trueTail, falseTail, shape⟩
          cases falsePrefix with
          | zero =>
              change false :: rest =
                true ::
                  (List.replicate trueTail true ++
                    List.replicate (falseTail + 1) false) at shape
              exact Bool.noConfusion (List.cons.inj shape).1
          | succ falsePrefix =>
              have tails := congrArg List.tail shape
              exact ⟨falsePrefix, trueTail, falseTail, by
                simpa [List.replicate_succ] using tails⟩
      · simp only [colorRun]
        change colorRun 3 rest = 1 ↔ _
        rw [colorRun_three_eq_one_iff]
        constructor
        · rintro ⟨trueTail, falseTail, shape⟩
          exact ⟨0, trueTail, falseTail, by
            simp [shape, List.replicate_succ]⟩
        · rintro ⟨falsePrefix, trueTail, falseTail, shape⟩
          have falsePrefixZero : falsePrefix = 0 := by
            cases falsePrefix with
            | zero => rfl
            | succ falsePrefix =>
                change true :: rest =
                  false ::
                    (List.replicate falsePrefix false ++
                      List.replicate (trueTail + 1) true ++
                      List.replicate (falseTail + 1) false) at shape
                exact Bool.noConfusion (List.cons.inj shape).1
          subst falsePrefix
          have tails := congrArg List.tail shape
          exact ⟨trueTail, falseTail, by
            simpa [List.replicate_succ] using tails⟩

/-- A Boolean projection has exactly three nonempty runs:
`false⁺ true⁺ false⁺`. -/
def Sandwich (colors : List Bool) : Prop :=
  ∃ leftCount middleCount rightCount,
    1 ≤ leftCount ∧
    1 ≤ middleCount ∧
    1 ≤ rightCount ∧
    colors =
      List.replicate leftCount false ++
        List.replicate middleCount true ++
        List.replicate rightCount false

private theorem sandwich_position_iff
    {letters : List Nat} {predicate : Nat → Bool}
    (sandwich : Sandwich (letters.map predicate)) :
    ∃ start width,
      1 ≤ start ∧
      1 ≤ width ∧
      start + width < letters.length ∧
      ∀ position (small : position < letters.length),
        predicate letters[position] = true ↔
          start ≤ position ∧ position < start + width := by
  rcases sandwich with
    ⟨leftCount, middleCount, rightCount,
      leftPositive, middlePositive, rightPositive, shape⟩
  have shape' :
      letters.map predicate =
        List.replicate leftCount false ++
          (List.replicate middleCount true ++
            List.replicate rightCount false) := by
    simpa [List.append_assoc] using shape
  have lengthShape :
      letters.length = leftCount + (middleCount + rightCount) := by
    have mappedLength := congrArg List.length shape'
    simpa using mappedLength
  refine ⟨leftCount, middleCount, leftPositive, middlePositive, by omega, ?_⟩
  intro position small
  have shapeAt :=
    congrArg (fun values : List Bool => values[position]?) shape'
  change
    (letters.map predicate)[position]? =
      (List.replicate leftCount false ++
        (List.replicate middleCount true ++
          List.replicate rightCount false))[position]? at shapeAt
  rw [List.getElem?_map, List.getElem?_eq_getElem small] at shapeAt
  simp only [Option.map_some] at shapeAt
  by_cases before : position < leftCount
  · have valueFalse : predicate letters[position] = false := by
      simpa [List.getElem?_append, List.getElem?_replicate, before]
        using shapeAt
    rw [valueFalse]
    simp only [Bool.false_eq_true, false_iff]
    omega
  · have afterLeft : leftCount ≤ position := by omega
    by_cases middle : position < leftCount + middleCount
    · have middleIndex : position - leftCount < middleCount := by omega
      have valueTrue : predicate letters[position] = true := by
        simpa [List.getElem?_append, List.getElem?_replicate, before,
          middleIndex] using shapeAt
      rw [valueTrue]
      simp
      omega
    · have afterMiddle : leftCount + middleCount ≤ position := by omega
      have shiftedAfter : middleCount ≤ position - leftCount := by omega
      have rightIndex :
          position - leftCount - middleCount < rightCount := by
        omega
      have valueFalse : predicate letters[position] = false := by
        simpa [List.getElem?_append, List.getElem?_replicate, before,
          shiftedAfter, rightIndex] using shapeAt
      rw [valueFalse]
      simp only [Bool.false_eq_true, false_iff]
      omega

private def ValueInterval
    (letters : List Nat) (value start width : Nat) : Prop :=
  1 ≤ start ∧
    1 ≤ width ∧
    start + width < letters.length ∧
    ∀ position (small : position < letters.length),
      letters[position] = value ↔
        start ≤ position ∧ position < start + width

private theorem valueInterval_of_sandwich
    {letters : List Nat} {value : Nat}
    (sandwich :
      Sandwich (letters.map fun letter => decide (letter = value))) :
    ∃ start width, ValueInterval letters value start width := by
  rcases sandwich_position_iff sandwich with
    ⟨start, width, startPositive, widthPositive, endBefore, holds⟩
  refine ⟨start, width, startPositive, widthPositive, endBefore, ?_⟩
  intro position small
  simpa using holds position small

private theorem distinct_value_intervals_disjoint
    {letters : List Nat} {leftValue rightValue : Nat}
    {leftStart leftWidth rightStart rightWidth : Nat}
    (different : leftValue ≠ rightValue)
    (left :
      ValueInterval letters leftValue leftStart leftWidth)
    (right :
      ValueInterval letters rightValue rightStart rightWidth) :
    leftStart + leftWidth ≤ rightStart ∨
      rightStart + rightWidth ≤ leftStart := by
  rcases left with ⟨_, leftWidthPositive, leftEndBefore, leftAt⟩
  rcases right with ⟨_, rightWidthPositive, rightEndBefore, rightAt⟩
  by_cases order : leftStart ≤ rightStart
  · apply Or.inl
    by_cases separated : leftStart + leftWidth ≤ rightStart
    · exact separated
    · have rightSmall : rightStart < letters.length := by omega
      have leftEquals :
          letters[rightStart] = leftValue :=
        (leftAt rightStart rightSmall).mpr (by omega)
      have rightEquals :
          letters[rightStart] = rightValue :=
        (rightAt rightStart rightSmall).mpr (by omega)
      exact False.elim (different (leftEquals.symm.trans rightEquals))
  · apply Or.inr
    have reverseOrder : rightStart ≤ leftStart := by omega
    by_cases separated : rightStart + rightWidth ≤ leftStart
    · exact separated
    · have leftSmall : leftStart < letters.length := by omega
      have rightEquals :
          letters[leftStart] = rightValue :=
        (rightAt leftStart leftSmall).mpr (by omega)
      have leftEquals :
          letters[leftStart] = leftValue :=
        (leftAt leftStart leftSmall).mpr (by omega)
      exact False.elim (different (leftEquals.symm.trans rightEquals))

private theorem value_intervals_adjacent_of_pair_sandwich
    {letters : List Nat} {leftValue rightValue : Nat}
    {leftStart leftWidth rightStart rightWidth : Nat}
    (different : leftValue ≠ rightValue)
    (left :
      ValueInterval letters leftValue leftStart leftWidth)
    (right :
      ValueInterval letters rightValue rightStart rightWidth)
    (pair :
      Sandwich (letters.map fun letter =>
        decide (letter = leftValue ∨ letter = rightValue))) :
    leftStart + leftWidth = rightStart ∨
      rightStart + rightWidth = leftStart := by
  rcases left with
    ⟨leftStartPositive, leftWidthPositive, leftEndBefore, leftAt⟩
  rcases right with
    ⟨rightStartPositive, rightWidthPositive, rightEndBefore, rightAt⟩
  rcases sandwich_position_iff pair with
    ⟨pairStart, pairWidth, _, _, pairEndBefore, pairAt⟩
  rcases distinct_value_intervals_disjoint different
      ⟨leftStartPositive, leftWidthPositive, leftEndBefore, leftAt⟩
      ⟨rightStartPositive, rightWidthPositive, rightEndBefore, rightAt⟩ with
    leftBefore | rightBefore
  · apply Or.inl
    apply Nat.le_antisymm leftBefore
    by_cases noGap : rightStart ≤ leftStart + leftWidth
    · exact noGap
    have leftStartSmall : leftStart < letters.length := by omega
    have rightStartSmall : rightStart < letters.length := by omega
    have leftSelected :
        (decide
          (letters[leftStart] = leftValue ∨
            letters[leftStart] = rightValue) : Bool) = true := by
      have equals :
          letters[leftStart] = leftValue :=
        (leftAt leftStart leftStartSmall).mpr (by omega)
      simp [equals]
    have rightSelected :
        (decide
          (letters[rightStart] = leftValue ∨
            letters[rightStart] = rightValue) : Bool) = true := by
      have equals :
          letters[rightStart] = rightValue :=
        (rightAt rightStart rightStartSmall).mpr (by omega)
      simp [equals]
    have leftPairBounds :=
      (pairAt leftStart leftStartSmall).mp leftSelected
    have rightPairBounds :=
      (pairAt rightStart rightStartSmall).mp rightSelected
    have boundarySmall :
        leftStart + leftWidth < letters.length := leftEndBefore
    have boundarySelected :
        (decide
          (letters[leftStart + leftWidth] = leftValue ∨
            letters[leftStart + leftWidth] = rightValue) : Bool) = true :=
      (pairAt (leftStart + leftWidth) boundarySmall).mpr (by omega)
    have notLeft :
        letters[leftStart + leftWidth] ≠ leftValue := by
      intro equals
      have bounds :=
        (leftAt (leftStart + leftWidth) boundarySmall).mp equals
      omega
    have notRight :
        letters[leftStart + leftWidth] ≠ rightValue := by
      intro equals
      have bounds :=
        (rightAt (leftStart + leftWidth) boundarySmall).mp equals
      omega
    simp [notLeft, notRight] at boundarySelected
  · apply Or.inr
    apply Nat.le_antisymm rightBefore
    by_cases noGap : leftStart ≤ rightStart + rightWidth
    · exact noGap
    have leftStartSmall : leftStart < letters.length := by omega
    have rightStartSmall : rightStart < letters.length := by omega
    have leftSelected :
        (decide
          (letters[leftStart] = leftValue ∨
            letters[leftStart] = rightValue) : Bool) = true := by
      have equals :
          letters[leftStart] = leftValue :=
        (leftAt leftStart leftStartSmall).mpr (by omega)
      simp [equals]
    have rightSelected :
        (decide
          (letters[rightStart] = leftValue ∨
            letters[rightStart] = rightValue) : Bool) = true := by
      have equals :
          letters[rightStart] = rightValue :=
        (rightAt rightStart rightStartSmall).mpr (by omega)
      simp [equals]
    have leftPairBounds :=
      (pairAt leftStart leftStartSmall).mp leftSelected
    have rightPairBounds :=
      (pairAt rightStart rightStartSmall).mp rightSelected
    have boundarySmall :
        rightStart + rightWidth < letters.length := rightEndBefore
    have boundarySelected :
        (decide
          (letters[rightStart + rightWidth] = leftValue ∨
            letters[rightStart + rightWidth] = rightValue) : Bool) = true :=
      (pairAt (rightStart + rightWidth) boundarySmall).mpr (by omega)
    have notLeft :
        letters[rightStart + rightWidth] ≠ leftValue := by
      intro equals
      have bounds :=
        (leftAt (rightStart + rightWidth) boundarySmall).mp equals
      omega
    have notRight :
        letters[rightStart + rightWidth] ≠ rightValue := by
      intro equals
      have bounds :=
        (rightAt (rightStart + rightWidth) boundarySmall).mp equals
      omega
    simp [notLeft, notRight] at boundarySelected

private theorem valueInterval_count_eq
    {letters : List Nat} {value start width : Nat}
    (interval : ValueInterval letters value start width) :
    letters.count value = width := by
  rcases interval with
    ⟨_, widthPositive, endBefore, atPosition⟩
  have segmentLength :
      (List.take width (List.drop start letters)).length = width := by
    simp only [List.length_take, List.length_drop]
    omega
  have segment :
      List.take width (List.drop start letters) =
        List.replicate width value := by
    apply List.eq_replicate_iff.mpr
    refine ⟨segmentLength, ?_⟩
    intro entry member
    rcases List.mem_iff_getElem.mp member with
      ⟨position, small, equals⟩
    have dropSmall :
        position < (List.drop start letters).length := by
      simp only [List.length_take] at small
      omega
    have dropped :
        (List.drop start letters)[position]'dropSmall =
          letters[start + position] :=
      List.getElem_drop
    have sourceSmall : start + position < letters.length := by
      have positionBound :
          position < width := by
        simpa [segmentLength] using small
      omega
    have sourceEquals :
        letters[start + position] = value :=
      (atPosition (start + position) sourceSmall).mpr (by
        have positionBound : position < width := by
          simpa [segmentLength] using small
        omega)
    rw [List.getElem_take, dropped, sourceEquals] at equals
    exact equals.symm
  have decomposition :
      letters =
        List.take start letters ++
          List.replicate width value ++
          List.drop (start + width) letters := by
    calc
      letters =
          List.take (start + width) letters ++
            List.drop (start + width) letters :=
        (List.take_append_drop (start + width) letters).symm
      _ =
          (List.take start letters ++
            List.take width (List.drop start letters)) ++
            List.drop (start + width) letters := by
        rw [List.take_add]
      _ =
          List.take start letters ++
            List.replicate width value ++
            List.drop (start + width) letters := by
        rw [segment]
  have prefixZero : (List.take start letters).count value = 0 := by
    apply List.count_eq_zero.mpr
    intro member
    rcases List.mem_iff_getElem.mp member with
      ⟨position, small, equals⟩
    have sourceSmall : position < letters.length := by
      have takenLength : (List.take start letters).length = start := by
        simp only [List.length_take]
        omega
      have : position < start := by simpa [takenLength] using small
      omega
    have sourceEquals : letters[position] = value := by
      rw [← List.getElem_take (xs := letters) (j := start) (i := position)]
      exact equals
    have bounds := (atPosition position sourceSmall).mp sourceEquals
    have takenLength : (List.take start letters).length = start := by
      simp only [List.length_take]
      omega
    have : position < start := by simpa [takenLength] using small
    omega
  have suffixZero :
      (List.drop (start + width) letters).count value = 0 := by
    apply List.count_eq_zero.mpr
    intro member
    rcases List.mem_iff_getElem.mp member with
      ⟨position, small, equals⟩
    have sourceSmall :
        start + width + position < letters.length := by
      have droppedLength :
          (List.drop (start + width) letters).length =
            letters.length - (start + width) :=
        List.length_drop
      rw [droppedLength] at small
      omega
    have sourceEquals :
        letters[start + width + position] = value := by
      have dropped :
          (List.drop (start + width) letters)[position] =
            letters[start + width + position] :=
        List.getElem_drop
      rw [dropped] at equals
      exact equals
    have bounds :=
      (atPosition (start + width + position) sourceSmall).mp sourceEquals
    omega
  rw [decomposition, List.count_append, List.count_append,
    prefixZero, suffixZero, List.count_replicate_self]
  omega

private theorem adjacency_chain_orientation
    {n : Nat} {letters : List Nat}
    (atLeastTwo : 2 ≤ n)
    (start width : Nat → Nat)
    (intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i))
    (adjacent :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1) ∨
          start (i + 1) + width (i + 1) = start i) :
    (∀ i, i + 1 < n →
        start i + width i = start (i + 1)) ∨
      (∀ i, i + 1 < n →
        start (i + 1) + width (i + 1) = start i) := by
  rcases adjacent 0 (by omega) with firstForward | firstReverse
  · apply Or.inl
    intro i pairSmall
    induction i with
    | zero => exact firstForward
    | succ i ih =>
        have previousSmall : i + 1 < n := by omega
        have previousForward := ih (by omega)
        rcases adjacent (i + 1) pairSmall with forward | reverse
        · exact forward
        · have disjoint :=
            distinct_value_intervals_disjoint
              (letters := letters)
              (leftValue := i + 1) (rightValue := i + 3)
              (leftStart := start i) (leftWidth := width i)
              (rightStart := start (i + 2)) (rightWidth := width (i + 2))
              (by omega)
              (intervals i (by omega))
              (intervals (i + 2) (by omega))
          have previousForward' :
              start i + width i = start (i + 1) :=
            previousForward
          have reverse' :
              start (i + 2) + width (i + 2) = start (i + 1) := by
            simpa [Nat.add_assoc] using reverse
          rcases disjoint with before | after <;>
            have leftWidthPositive :=
              (intervals i (by omega)).2.1 <;>
            have rightWidthPositive :=
              (intervals (i + 2) (by omega)).2.1 <;>
            omega
  · apply Or.inr
    intro i pairSmall
    induction i with
    | zero => exact firstReverse
    | succ i ih =>
        have previousSmall : i + 1 < n := by omega
        have previousReverse := ih (by omega)
        rcases adjacent (i + 1) pairSmall with forward | reverse
        · have disjoint :=
            distinct_value_intervals_disjoint
              (letters := letters)
              (leftValue := i + 1) (rightValue := i + 3)
              (leftStart := start i) (leftWidth := width i)
              (rightStart := start (i + 2)) (rightWidth := width (i + 2))
              (by omega)
              (intervals i (by omega))
              (intervals (i + 2) (by omega))
          have previousReverse' :
              start (i + 1) + width (i + 1) = start i :=
            previousReverse
          have forward' :
              start (i + 1) + width (i + 1) = start (i + 2) := by
            simpa [Nat.add_assoc] using forward
          rcases disjoint with before | after <;>
            have leftWidthPositive :=
              (intervals i (by omega)).2.1 <;>
            have rightWidthPositive :=
              (intervals (i + 2) (by omega)).2.1 <;>
            omega
        · exact reverse

private theorem take_eq_replicate_of_getElem
    {letters : List Nat} {count value : Nat}
    (countBound : count ≤ letters.length)
    (constant :
      ∀ position (small : position < count),
        letters[position]'(Nat.lt_of_lt_of_le small countBound) = value) :
    List.take count letters = List.replicate count value := by
  apply List.eq_replicate_iff.mpr
  refine ⟨List.length_take_of_le countBound, ?_⟩
  intro entry member
  rcases List.mem_iff_getElem.mp member with
    ⟨position, small, equals⟩
  have positionSmall : position < count := by
    simpa [List.length_take_of_le countBound] using small
  have sourceEquals : letters[position] = value :=
    constant position positionSmall
  rw [List.getElem_take, sourceEquals] at equals
  exact equals.symm

private theorem drop_eq_replicate_of_getElem
    {letters : List Nat} {start value : Nat}
    (startBound : start ≤ letters.length)
    (constant :
      ∀ position (after : start ≤ position)
          (small : position < letters.length),
        letters[position]'small = value) :
    List.drop start letters =
      List.replicate (letters.length - start) value := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, ?_⟩
  intro entry member
  rcases List.mem_iff_getElem.mp member with
    ⟨position, small, equals⟩
  have sourceSmall : start + position < letters.length := by
    have droppedLength :
        (List.drop start letters).length = letters.length - start :=
      List.length_drop
    rw [droppedLength] at small
    omega
  have sourceEquals : letters[start + position] = value :=
    constant (start + position) (by omega) sourceSmall
  have dropped :
      (List.drop start letters)[position] =
        letters[start + position] :=
    List.getElem_drop
  rw [dropped, sourceEquals] at equals
  exact equals.symm

private theorem interval_segment_eq_replicate
    {letters : List Nat} {value start width : Nat}
    (interval : ValueInterval letters value start width) :
    List.take width (List.drop start letters) =
      List.replicate width value := by
  rcases interval with ⟨_, widthPositive, endBefore, atPosition⟩
  apply List.eq_replicate_iff.mpr
  have segmentLength :
      (List.take width (List.drop start letters)).length = width := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨segmentLength, ?_⟩
  intro entry member
  rcases List.mem_iff_getElem.mp member with
    ⟨position, small, equals⟩
  have dropSmall :
      position < (List.drop start letters).length := by
    simp only [List.length_take] at small
    omega
  have positionBound : position < width := by
    simpa [segmentLength] using small
  have sourceSmall : start + position < letters.length := by omega
  have sourceEquals :
      letters[start + position] = value :=
    (atPosition (start + position) sourceSmall).mpr (by omega)
  have dropped :
      (List.drop start letters)[position]'dropSmall =
        letters[start + position] :=
    List.getElem_drop
  rw [List.getElem_take, dropped, sourceEquals] at equals
  exact equals.symm

private theorem take_forward_blocks
    {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n)
    (start width : Nat → Nat)
    (prefixEq :
      List.take (start 0) letters =
        List.replicate (start 0) 0)
    (intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i))
    (forward :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1)) :
    ∀ i, i < n →
      List.take (start i + width i) letters =
        List.replicate (start 0) 0 ++
          orderedBlocks (List.range (i + 1)) width := by
  intro i iSmall
  induction i with
  | zero =>
      rw [List.take_add, prefixEq,
        interval_segment_eq_replicate (intervals 0 (by omega))]
      simp [orderedBlocks, powerBlock]
  | succ i ih =>
      have previousSmall : i < n := by omega
      have previous := ih previousSmall
      have touches : start i + width i = start (i + 1) :=
        forward i (by omega)
      rw [List.take_add,
        interval_segment_eq_replicate (intervals (i + 1) iSmall),
        ← touches, previous]
      simp [orderedBlocks, powerBlock, List.range_succ,
        List.append_assoc]

private theorem listInP_of_forward_intervals
    {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n)
    (domain :
      ∀ letter, letter ∈ letters ↔
        letter = 0 ∨ ∃ i, i < n ∧ letter = i + 1)
    (large : ∀ letter, letter ∈ letters → 2 ≤ letters.count letter)
    (nonzero :
      Sandwich (letters.map fun letter => decide (letter ≠ 0)))
    (start width : Nat → Nat)
    (intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i))
    (forward :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1)) :
    ListInP n letters := by
  rcases sandwich_position_iff nonzero with
    ⟨nonzeroStart, nonzeroWidth, nonzeroStartPositive,
      nonzeroWidthPositive, nonzeroEndBefore, nonzeroAt⟩
  have intervalInside :
      ∀ i, i < n →
        nonzeroStart ≤ start i ∧
          start i + width i ≤ nonzeroStart + nonzeroWidth := by
    intro i iSmall
    rcases intervals i iSmall with
      ⟨_, widthPositive, endBefore, atPosition⟩
    have startSmall : start i < letters.length := by omega
    have startValue :
        letters[start i] = i + 1 :=
      (atPosition (start i) startSmall).mpr (by omega)
    have startNonzero :
        (decide (letters[start i] ≠ 0) : Bool) = true := by
      simp [startValue]
    have startBounds := (nonzeroAt (start i) startSmall).mp startNonzero
    have lastSmall : start i + width i - 1 < letters.length := by omega
    have lastValue :
        letters[start i + width i - 1] = i + 1 :=
      (atPosition (start i + width i - 1) lastSmall).mpr (by omega)
    have lastNonzero :
        (decide (letters[start i + width i - 1] ≠ 0) : Bool) = true := by
      simp [lastValue]
    have lastBounds :=
      (nonzeroAt (start i + width i - 1) lastSmall).mp lastNonzero
    omega
  have startMono :
      ∀ j, j < n → ∀ i, i ≤ j → start i ≤ start j := by
    intro j jSmall
    induction j with
    | zero =>
        intro i iLe
        have : i = 0 := by omega
        subst i
        exact Nat.le_refl _
    | succ j ih =>
        intro i iLe
        by_cases equal : i = j + 1
        · subst i
          exact Nat.le_refl _
        · have iLeJ : i ≤ j := by omega
          have previous := ih (by omega) i iLeJ
          have touches := forward j (by omega)
          have widthPositive := (intervals j (by omega)).2.1
          omega
  have firstStart : start 0 = nonzeroStart := by
    have zeroInside := (intervalInside 0 (by omega)).1
    have nonzeroStartSmall : nonzeroStart < letters.length := by omega
    have selected :
        (decide (letters[nonzeroStart] ≠ 0) : Bool) = true :=
      (nonzeroAt nonzeroStart nonzeroStartSmall).mpr (by omega)
    have nonzeroValue : letters[nonzeroStart] ≠ 0 := by
      simpa using selected
    have member : letters[nonzeroStart] ∈ letters :=
      List.getElem_mem nonzeroStartSmall
    rcases (domain letters[nonzeroStart]).mp member with
      equalsZero | ⟨i, iSmall, equals⟩
    · exact False.elim (nonzeroValue equalsZero)
    · have inInterval :
          start i ≤ nonzeroStart :=
        ((intervals i iSmall).2.2.2 nonzeroStart nonzeroStartSmall).mp
          equals |>.1
      have firstLe := startMono i iSmall 0 (by omega)
      omega
  let last := n - 1
  have lastSmall : last < n := by
    dsimp [last]
    omega
  have endMono :
      ∀ i, i < n →
        start i + width i ≤ start last + width last := by
    intro i iSmall
    by_cases equal : i = last
    · subst i
      exact Nat.le_refl _
    · have beforeLast : i < last := by
        dsimp [last] at *
        omega
      have touches := forward i (by omega)
      have startsLe := startMono last lastSmall (i + 1) (by omega)
      omega
  have lastEnd :
      start last + width last = nonzeroStart + nonzeroWidth := by
    have inside := (intervalInside last lastSmall).2
    have endPositionSmall :
        nonzeroStart + nonzeroWidth - 1 < letters.length := by omega
    have selected :
        (decide
          (letters[nonzeroStart + nonzeroWidth - 1] ≠ 0) : Bool) = true :=
      (nonzeroAt (nonzeroStart + nonzeroWidth - 1) endPositionSmall).mpr
        (by omega)
    have nonzeroValue :
        letters[nonzeroStart + nonzeroWidth - 1] ≠ 0 := by
      simpa using selected
    have member :
        letters[nonzeroStart + nonzeroWidth - 1] ∈ letters :=
      List.getElem_mem endPositionSmall
    rcases
        (domain letters[nonzeroStart + nonzeroWidth - 1]).mp member with
      equalsZero | ⟨i, iSmall, equals⟩
    · exact False.elim (nonzeroValue equalsZero)
    · have inInterval :=
        ((intervals i iSmall).2.2.2
          (nonzeroStart + nonzeroWidth - 1) endPositionSmall).mp equals
      have endLe := endMono i iSmall
      omega
  have prefixEq :
      List.take (start 0) letters =
        List.replicate (start 0) 0 := by
    have countBound : start 0 ≤ letters.length :=
      Nat.le_trans (Nat.le_add_right (start 0) (width 0))
        (Nat.le_of_lt (intervals 0 (by omega)).2.2.1)
    apply take_eq_replicate_of_getElem countBound
    intro position positionSmall
    have sourceSmall : position < letters.length := by
      have := (intervals 0 (by omega)).2.2.1
      omega
    have outside :
        (decide (letters[position] ≠ 0) : Bool) = false := by
      apply Bool.eq_false_iff.mpr
      intro selected
      have bounds := (nonzeroAt position sourceSmall).mp selected
      omega
    simpa using outside
  have suffix :
      List.drop (start last + width last) letters =
        List.replicate
          (letters.length - (start last + width last)) 0 := by
    apply drop_eq_replicate_of_getElem
    · omega
    · intro position positionAfter positionSmall
      have outside :
          (decide (letters[position] ≠ 0) : Bool) = false := by
        apply Bool.eq_false_iff.mpr
        intro selected
        have bounds := (nonzeroAt position positionSmall).mp selected
        omega
      simpa using outside
  have prefixBlocks :=
    take_forward_blocks positive start width prefixEq intervals forward
      last lastSmall
  have shape :
      letters =
        List.replicate (start 0) 0 ++
          orderedBlocks (List.range n) width ++
          List.replicate
            (letters.length - (start last + width last)) 0 := by
    calc
      letters =
          List.take (start last + width last) letters ++
            List.drop (start last + width last) letters :=
        (List.take_append_drop (start last + width last) letters).symm
      _ =
          (List.replicate (start 0) 0 ++
            orderedBlocks (List.range (last + 1)) width) ++
            List.replicate
              (letters.length - (start last + width last)) 0 := by
        rw [prefixBlocks, suffix]
      _ =
          List.replicate (start 0) 0 ++
            orderedBlocks (List.range n) width ++
            List.replicate
              (letters.length - (start last + width last)) 0 := by
        dsimp [last]
        have : n - 1 + 1 = n := by omega
        rw [this, List.append_assoc]
  refine
    ⟨start 0, letters.length - (start last + width last), width,
      ?_, ?_, ?_, shape⟩
  · exact (intervals 0 (by omega)).1
  · omega
  · intro i iSmall
    have startSmall : start i < letters.length := by
      have := (intervals i iSmall).2.2.1
      omega
    have member : i + 1 ∈ letters := by
      have equals :
          letters[start i] = i + 1 :=
        ((intervals i iSmall).2.2.2 (start i) startSmall).mpr (by
          have widthPositive := (intervals i iSmall).2.1
          omega)
      rw [← equals]
      exact List.getElem_mem startSmall
    have countLarge := large (i + 1) member
    rw [valueInterval_count_eq (intervals i iSmall)] at countLarge
    exact countLarge

private theorem sandwich_reverse {colors : List Bool}
    (sandwich : Sandwich colors) :
    Sandwich colors.reverse := by
  rcases sandwich with
    ⟨leftCount, middleCount, rightCount,
      leftPositive, middlePositive, rightPositive, shape⟩
  refine
    ⟨rightCount, middleCount, leftCount,
      rightPositive, middlePositive, leftPositive, ?_⟩
  rw [shape]
  simp [List.reverse_append, List.append_assoc]

private theorem valueInterval_reverse
    {letters : List Nat} {value start width : Nat}
    (interval : ValueInterval letters value start width) :
    ValueInterval letters.reverse value
      (letters.length - (start + width)) width := by
  rcases interval with
    ⟨startPositive, widthPositive, endBefore, atPosition⟩
  refine ⟨by omega, widthPositive, by simp; omega, ?_⟩
  intro position small
  have originalSmall :
      letters.length - 1 - position < letters.length := by
    have positionSmall : position < letters.length := by
      simpa using small
    omega
  rw [List.getElem_reverse]
  have original :=
    atPosition (letters.length - 1 - position) originalSmall
  rw [original]
  constructor <;> intro bounds <;> omega

private theorem listInQ_of_reverse_intervals
    {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n)
    (domain :
      ∀ letter, letter ∈ letters ↔
        letter = 0 ∨ ∃ i, i < n ∧ letter = i + 1)
    (large : ∀ letter, letter ∈ letters → 2 ≤ letters.count letter)
    (nonzero :
      Sandwich (letters.map fun letter => decide (letter ≠ 0)))
    (start width : Nat → Nat)
    (intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i))
    (reverse :
      ∀ i, i + 1 < n →
        start (i + 1) + width (i + 1) = start i) :
    ListInQ n letters := by
  let reverseStart := fun i =>
    letters.length - (start i + width i)
  have reverseDomain :
      ∀ letter, letter ∈ letters.reverse ↔
        letter = 0 ∨ ∃ i, i < n ∧ letter = i + 1 := by
    intro letter
    rw [List.mem_reverse, domain]
  have reverseLarge :
      ∀ letter, letter ∈ letters.reverse →
        2 ≤ letters.reverse.count letter := by
    intro letter member
    rw [List.count_reverse]
    exact large letter (List.mem_reverse.mp member)
  have reverseNonzero :
      Sandwich
        (letters.reverse.map fun letter => decide (letter ≠ 0)) := by
    rw [List.map_reverse]
    exact sandwich_reverse nonzero
  have reverseIntervals :
      ∀ i, i < n →
        ValueInterval letters.reverse (i + 1)
          (reverseStart i) (width i) := by
    intro i iSmall
    exact valueInterval_reverse (intervals i iSmall)
  have reverseForward :
      ∀ i, i + 1 < n →
        reverseStart i + width i = reverseStart (i + 1) := by
    intro i pairSmall
    have currentEnd := (intervals i (by omega)).2.2.1
    have nextEnd := (intervals (i + 1) (by omega)).2.2.1
    have touches := reverse i pairSmall
    dsimp [reverseStart]
    omega
  exact
    listInP_of_forward_intervals positive reverseDomain reverseLarge
      reverseNonzero reverseStart width reverseIntervals reverseForward
theorem colorEval_eq_one_iff {colors : List Bool} :
    colorEval colors = 1 ↔ Sandwich colors := by
  constructor
  · intro evaluates
    cases colors with
    | nil => simp [colorEval] at evaluates
    | cons color rest =>
        cases color
        · have shape := (colorRun_five_eq_one_iff rest).mp (by
            simpa [colorEval, colorValue] using evaluates)
          rcases shape with ⟨leftTail, middleTail, rightTail, shape⟩
          refine ⟨leftTail + 1, middleTail + 1, rightTail + 1,
            by omega, by omega, by omega, ?_⟩
          simp [shape, List.replicate_succ]
        · exact False.elim (colorRun_four_ne_one rest (by
            simpa [colorEval, colorValue] using evaluates))
  · rintro ⟨leftCount, middleCount, rightCount,
      leftPositive, middlePositive, rightPositive, shape⟩
    cases leftCount with
    | zero => omega
    | succ leftCount =>
        cases middleCount with
        | zero => omega
        | succ middleCount =>
            cases rightCount with
            | zero => omega
            | succ rightCount =>
                rw [shape]
                <;> apply (colorRun_five_eq_one_iff _).mpr
                <;> exact ⟨leftCount, middleCount, rightCount, by
                  simp [List.replicate_succ]⟩

theorem eval_projection (predicate : Nat → Bool) (word : Word Nat) :
    table.semigroup.eval
        (fun letter => colorValue (predicate letter)) word =
      colorEval (word.toList.map predicate) := by
  have runMap :
      ∀ (initial : Fin 6) (letters : List Nat),
        colorRun initial (letters.map predicate) =
          letters.foldl
            (fun current letter =>
              mul current (colorValue (predicate letter)))
            initial := by
    intro initial letters
    induction letters generalizing initial with
    | nil => rfl
    | cons letter rest ih =>
        simp only [List.map_cons, colorRun, List.foldl_cons]
        exact ih _
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList, List.map_cons, colorEval]
      exact (runMap (colorValue (predicate head)) tail).symm

/-- The exact finite list kernel used after the semantic projection tests in
Lemma 5. It says that a word with the correct multiplicities, whose nonzero
letters, individual middle letters, and consecutive pairs each project to a
single middle run, has either forward or reverse block order.

This proposition contains no semigroup semantics. -/
def MateRigidity : Prop :=
  ∀ (n : Nat) (letters : List Nat),
    2 ≤ n →
    (∀ letter, letter ∈ letters ↔ letter = 0 ∨
      ∃ i, i < n ∧ letter = i + 1) →
    (∀ letter, letter ∈ letters → 2 ≤ letters.count letter) →
    Sandwich (letters.map fun letter => decide (letter ≠ 0)) →
    (∀ i, i < n →
      Sandwich (letters.map fun letter => decide (letter = i + 1))) →
    (∀ i, i + 1 < n →
      Sandwich (letters.map fun letter =>
      decide (letter = i + 1 ∨ letter = i + 2))) →
    ListInP n letters ∨ ListInQ n letters

theorem mateRigidity : MateRigidity := by
  intro n letters atLeastTwo domain large nonzero singletons pairs
  have intervalExists :
      ∀ i, i < n →
        ∃ start width,
          ValueInterval letters (i + 1) start width := by
    intro i iSmall
    exact valueInterval_of_sandwich (singletons i iSmall)
  have intervalPairExists :
      ∀ i, i < n →
        ∃ bounds : Nat × Nat,
          ValueInterval letters (i + 1) bounds.1 bounds.2 := by
    intro i iSmall
    rcases intervalExists i iSmall with ⟨start, width, interval⟩
    exact ⟨(start, width), interval⟩
  let bounds : Nat → Nat × Nat := fun i =>
    if iSmall : i < n then
      Classical.choose (intervalPairExists i iSmall)
    else
      (0, 0)
  let start := fun i => (bounds i).1
  let width := fun i => (bounds i).2
  have intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i) := by
    intro i iSmall
    dsimp [start, width, bounds]
    simp only [dif_pos iSmall]
    exact Classical.choose_spec (intervalPairExists i iSmall)
  have adjacent :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1) ∨
          start (i + 1) + width (i + 1) = start i := by
    intro i pairSmall
    exact
      value_intervals_adjacent_of_pair_sandwich
        (leftValue := i + 1) (rightValue := i + 2)
        (by omega)
        (intervals i (by omega))
        (by
          simpa [Nat.add_assoc] using intervals (i + 1) (by omega))
        (pairs i pairSmall)
  rcases
      adjacency_chain_orientation atLeastTwo start width intervals adjacent with
    forward | reverse
  · exact Or.inl
      (listInP_of_forward_intervals (by omega) domain large nonzero
        start width intervals forward)
  · exact Or.inr
      (listInQ_of_reverse_intervals (by omega) domain large nonzero
        start width intervals reverse)

/-- Equality of the finite family of Boolean projections used in the paper:
all nonzero letters, each individual middle letter, and each consecutive
pair of middle letters. -/
def ProjectionEquivalent (n : Nat) (left right : List Nat) : Prop :=
  colorEval (left.map fun letter => decide (letter ≠ 0)) =
      colorEval (right.map fun letter => decide (letter ≠ 0)) ∧
    (∀ i, i < n →
      colorEval (left.map fun letter => decide (letter = i + 1)) =
        colorEval (right.map fun letter => decide (letter = i + 1))) ∧
    (∀ i, i + 1 < n →
      colorEval (left.map fun letter =>
          decide (letter = i + 1 ∨ letter = i + 2)) =
        colorEval (right.map fun letter =>
          decide (letter = i + 1 ∨ letter = i + 2)))

/-- Pure list form of the remaining combinatorics in Zhang--Luo Lemma 5.
The two count hypotheses are exactly the support and simple-letter
consequences of Lemma 1; `ProjectionEquivalent` packages the three families
of `d/e` tests. -/
def Lemma5Combinatorics : Prop :=
  ∀ (n : Nat) (left right : List Nat),
    2 ≤ n →
    ListInP n left →
    (∀ letter, left.count letter = 0 ↔ right.count letter = 0) →
    (∀ letter, left.count letter = 1 ↔ right.count letter = 1) →
    ProjectionEquivalent n left right →
    ListInP n right ∨ ListInQ n right

theorem inP_mem_iff {n : Nat} {letters : List Nat}
    (membership : ListInP n letters) (letter : Nat) :
    letter ∈ letters ↔
      letter = 0 ∨ ∃ i, i < n ∧ letter = i + 1 := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents, leftPositive,
      rightPositive, large, shape⟩
  rw [shape]
  simp only [List.mem_append, List.mem_replicate]
  constructor
  · rintro ((⟨_, equals⟩ | middle) | ⟨_, equals⟩)
    · exact Or.inl equals
    · rw [orderedBlocks] at middle
      simp only [List.mem_flatMap] at middle
      rcases middle with ⟨i, iInRange, middle⟩
      refine Or.inr ⟨i, List.mem_range.mp iInRange, ?_⟩
      exact (by
        rw [powerBlock] at middle
        exact List.eq_of_mem_replicate middle)
    · exact Or.inl equals
  · rintro (rfl | ⟨i, iSmall, rfl⟩)
    · exact Or.inl (Or.inl ⟨by omega, rfl⟩)
    · exact Or.inl (Or.inr (by
      rw [orderedBlocks]
      simp only [List.mem_flatMap]
      refine ⟨i, List.mem_range.mpr iSmall, ?_⟩
      simp [powerBlock]
      have := large i iSmall
      omega))

theorem inP_count_at_least_two {n : Nat} {letters : List Nat}
    (membership : ListInP n letters) {letter : Nat}
    (member : letter ∈ letters) :
    2 ≤ letters.count letter := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents, leftPositive,
      rightPositive, large, shape⟩
  have letterShape :=
    inP_mem_iff
      (n := n) (letters := letters)
      ⟨leftExponent, rightExponent, exponents, leftPositive,
        rightPositive, large, shape⟩ letter
  rcases letterShape.mp member with rfl | ⟨i, iSmall, rfl⟩
  · rw [shape, List.count_append, List.count_append,
      List.count_replicate_self, List.count_replicate_self]
    omega
  · have blockMember :
        powerBlock i (exponents i) ∈
          (List.range n).map (fun j => powerBlock j (exponents j)) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr iSmall, rfl⟩
    have blockSublist :
        (powerBlock i (exponents i)).Sublist
          (orderedBlocks (List.range n) exponents) := by
      exact List.sublist_flatten_of_mem blockMember
    have middleSublist :
        (orderedBlocks (List.range n) exponents).Sublist letters := by
      rw [shape]
      exact
        (List.sublist_append_right
          (List.replicate leftExponent 0)
          (orderedBlocks (List.range n) exponents)).trans
          (List.sublist_append_left
            (List.replicate leftExponent 0 ++
              orderedBlocks (List.range n) exponents)
            (List.replicate rightExponent 0))
    have countBound :=
      (blockSublist.trans middleSublist).count_le (i + 1)
    rw [powerBlock, List.count_replicate_self] at countBound
    exact Nat.le_trans (large i iSmall) countBound

def intervalPredicate (lo hi letter : Nat) : Bool :=
  decide (lo < letter ∧ letter ≤ hi)

private theorem range_split_interval {n lo hi : Nat}
    (loLeHi : lo ≤ hi) (hiLeN : hi ≤ n) :
    List.range n =
      List.range' 0 lo ++
        List.range' lo (hi - lo) ++
        List.range' hi (n - hi) := by
  rw [List.range_eq_range']
  have first :=
    List.range'_append
      (s := 0) (m := lo) (n := hi - lo) (step := 1)
  have second :=
    List.range'_append
      (s := 0) (m := hi) (n := n - hi) (step := 1)
  simp only [Nat.one_mul, Nat.zero_add] at first second
  have loAdd : lo + (hi - lo) = hi := by omega
  have hiAdd : hi + (n - hi) = n := by omega
  rw [loAdd] at first
  rw [hiAdd] at second
  rw [← second, ← first, List.append_assoc]

private theorem map_orderedBlocks_eq_replicate
    (indices : List Nat) (exponents : Nat → Nat)
    (predicate : Nat → Bool) (color : Bool)
    (constant :
      ∀ i, i ∈ indices → predicate (i + 1) = color) :
    (orderedBlocks indices exponents).map predicate =
      List.replicate (orderedBlocks indices exponents).length color := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, ?_⟩
  intro value member
  rw [orderedBlocks] at member
  simp only [List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨letter, ⟨i, iMember, letterMember⟩,
    predicateValue⟩
  have letterEq : letter = i + 1 := by
    rw [powerBlock] at letterMember
    exact List.eq_of_mem_replicate letterMember
  subst letter
  rw [← predicateValue]
  exact constant i iMember

private theorem interval_false_before {lo hi i : Nat}
    (member : i ∈ List.range' 0 lo) :
    intervalPredicate lo hi (i + 1) = false := by
  simp only [intervalPredicate, decide_eq_false_iff_not]
  rcases List.mem_range'.mp member with ⟨j, jSmall, iEq⟩
  simp at iEq
  subst i
  omega

private theorem interval_true_middle {lo hi i : Nat}
    (member : i ∈ List.range' lo (hi - lo))
    (loLeHi : lo ≤ hi) :
    intervalPredicate lo hi (i + 1) = true := by
  simp only [intervalPredicate, decide_eq_true_eq]
  have bounds := List.mem_range'.mp member
  constructor <;> omega

private theorem interval_false_after {n lo hi i : Nat}
    (member : i ∈ List.range' hi (n - hi)) :
    intervalPredicate lo hi (i + 1) = false := by
  simp only [intervalPredicate, decide_eq_false_iff_not]
  have bounds := List.mem_range'.mp member
  omega

private theorem interval_middle_length_positive
    {n lo hi : Nat} (exponents : Nat → Nat)
    (loLtHi : lo < hi) (hiLeN : hi ≤ n)
    (large : ∀ i, i < n → 2 ≤ exponents i) :
    1 ≤ (orderedBlocks (List.range' lo (hi - lo)) exponents).length := by
  have loMember : lo ∈ List.range' lo (hi - lo) := by
    apply List.mem_range'.mpr
    exact ⟨0, by omega, by simp⟩
  have blockMember :
      powerBlock lo (exponents lo) ∈
        (List.range' lo (hi - lo)).map
          (fun i => powerBlock i (exponents i)) :=
    List.mem_map.mpr ⟨lo, loMember, rfl⟩
  have blockSublist :
      (powerBlock lo (exponents lo)).Sublist
        (orderedBlocks (List.range' lo (hi - lo)) exponents) :=
    List.sublist_flatten_of_mem blockMember
  have lengthBound := blockSublist.length_le
  simp only [powerBlock, List.length_replicate] at lengthBound
  have := large lo (Nat.lt_of_lt_of_le loLtHi hiLeN)
  omega

theorem inP_interval_sandwich {n lo hi : Nat} {letters : List Nat}
    (membership : ListInP n letters)
    (loLtHi : lo < hi) (hiLeN : hi ≤ n) :
    Sandwich (letters.map (intervalPredicate lo hi)) := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents, leftPositive,
      rightPositive, large, shape⟩
  have loLeHi : lo ≤ hi := Nat.le_of_lt loLtHi
  have ranges := range_split_interval loLeHi hiLeN
  have prefixMap :=
    map_orderedBlocks_eq_replicate
      (List.range' 0 lo) exponents (intervalPredicate lo hi) false
      (fun i member => interval_false_before member)
  have middleMap :=
    map_orderedBlocks_eq_replicate
      (List.range' lo (hi - lo)) exponents
      (intervalPredicate lo hi) true
      (fun i member => interval_true_middle member loLeHi)
  have suffixMap :=
    map_orderedBlocks_eq_replicate
      (List.range' hi (n - hi)) exponents
      (intervalPredicate lo hi) false
      (fun i member => interval_false_after member)
  let prefixLength :=
    (orderedBlocks (List.range' 0 lo) exponents).length
  let middleLength :=
    (orderedBlocks (List.range' lo (hi - lo)) exponents).length
  let suffixLength :=
    (orderedBlocks (List.range' hi (n - hi)) exponents).length
  refine
    ⟨leftExponent + prefixLength, middleLength,
      suffixLength + rightExponent, by omega, ?_, by omega, ?_⟩
  · exact interval_middle_length_positive exponents loLtHi hiLeN large
  · rw [shape, ranges]
    simp only [List.map_append, orderedBlocks, List.flatMap_append]
    simp only [orderedBlocks] at prefixMap middleMap suffixMap
    rw [prefixMap, middleMap, suffixMap]
    have zeroColor : intervalPredicate lo hi 0 = false := by
      simp [intervalPredicate]
    rw [List.map_replicate, List.map_replicate, zeroColor]
    dsimp [prefixLength, middleLength, suffixLength]
    simp only [List.append_assoc]
    simp only [orderedBlocks]
    rw [← List.append_assoc,
      List.replicate_append_replicate]
    simp only [List.replicate_append_replicate]

theorem inP_nonzero_sandwich {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n) (membership : ListInP n letters) :
    Sandwich (letters.map fun letter => decide (letter ≠ 0)) := by
  have interval :=
    inP_interval_sandwich
      (lo := 0) (hi := n) membership (by omega) (Nat.le_refl n)
  have maps :
      letters.map (intervalPredicate 0 n) =
        letters.map (fun letter => decide (letter ≠ 0)) := by
    apply List.map_congr_left
    intro letter member
    have domain := (inP_mem_iff membership letter).mp member
    rcases domain with rfl | ⟨i, iSmall, rfl⟩
    · simp [intervalPredicate]
    · simp [intervalPredicate]
      omega
  rw [← maps]
  exact interval

theorem inP_singleton_sandwich {n i : Nat} {letters : List Nat}
    (iSmall : i < n) (membership : ListInP n letters) :
    Sandwich (letters.map fun letter => decide (letter = i + 1)) := by
  have interval :=
    inP_interval_sandwich
      (lo := i) (hi := i + 1) membership (by omega)
        (Nat.succ_le_iff.mpr iSmall)
  have predicates :
      intervalPredicate i (i + 1) =
        fun letter => decide (letter = i + 1) := by
    funext letter
    by_cases equals : letter = i + 1 <;>
      simp [intervalPredicate, equals] <;> omega
  rw [← predicates]
  exact interval

theorem inP_pair_sandwich {n i : Nat} {letters : List Nat}
    (pairSmall : i + 1 < n) (membership : ListInP n letters) :
    Sandwich (letters.map fun letter =>
      decide (letter = i + 1 ∨ letter = i + 2)) := by
  have interval :=
    inP_interval_sandwich
      (lo := i) (hi := i + 2) membership (by omega)
        (Nat.succ_le_iff.mpr pairSmall)
  have predicates :
      intervalPredicate i (i + 2) =
        fun letter =>
          decide (letter = i + 1 ∨ letter = i + 2) := by
    funext letter
    by_cases first : letter = i + 1
    · simp [intervalPredicate, first]
    by_cases second : letter = i + 2
    · simp [intervalPredicate, second]
    · simp [intervalPredicate, first, second]
      omega
  rw [← predicates]
  exact interval

/-- The semantic-free Lemma 5 kernel reduces to `MateRigidity`, whose
hypotheses are only the visible block and adjacency conditions on the target
list. -/
theorem lemma5Combinatorics_of_mateRigidity
    (rigidity : MateRigidity) :
    Lemma5Combinatorics := by
  intro n left right atLeastTwo leftInP absence simplicity projections
  apply rigidity n right atLeastTwo
  · intro letter
    constructor
    · intro rightMember
      have rightPositive : 0 < right.count letter :=
        List.count_pos_iff.mpr rightMember
      have leftNonzero : left.count letter ≠ 0 := by
        intro leftZero
        exact (Nat.ne_of_gt rightPositive) ((absence letter).mp leftZero)
      exact (inP_mem_iff leftInP letter).mp
        (List.count_pos_iff.mp (Nat.pos_of_ne_zero leftNonzero))
    · intro domain
      have leftMember := (inP_mem_iff leftInP letter).mpr domain
      have leftPositive : 0 < left.count letter :=
        List.count_pos_iff.mpr leftMember
      have rightNonzero : right.count letter ≠ 0 := by
        intro rightZero
        exact (Nat.ne_of_gt leftPositive) ((absence letter).mpr rightZero)
      exact List.count_pos_iff.mp (Nat.pos_of_ne_zero rightNonzero)
  · intro letter rightMember
    have rightPositive : 0 < right.count letter :=
      List.count_pos_iff.mpr rightMember
    have rightNotOne : right.count letter ≠ 1 := by
      intro rightOne
      have leftOne := (simplicity letter).mpr rightOne
      have leftMember : letter ∈ left :=
        List.count_pos_iff.mp (by omega)
      have leftLarge := inP_count_at_least_two leftInP leftMember
      omega
    omega
  · apply colorEval_eq_one_iff.mp
    rw [← projections.1]
    exact colorEval_eq_one_iff.mpr
      (inP_nonzero_sandwich (by omega) leftInP)
  · intro i iSmall
    apply colorEval_eq_one_iff.mp
    rw [← projections.2.1 i iSmall]
    exact colorEval_eq_one_iff.mpr
      (inP_singleton_sandwich iSmall leftInP)
  · intro i pairSmall
    apply colorEval_eq_one_iff.mp
    rw [← projections.2.2 i pairSmall]
    exact colorEval_eq_one_iff.mpr
      (inP_pair_sandwich pairSmall leftInP)

theorem lemma5Combinatorics : Lemma5Combinatorics :=
  lemma5Combinatorics_of_mateRigidity mateRigidity

private def ListDisjoint (left right : List Nat) : Prop :=
  ∀ letter, letter ∈ left → letter ∉ right

private theorem flatMap_append_split
    (substitution : Nat → Word Nat)
    {source left right : List Nat}
    (sourceNonempty : source ≠ [])
    (split :
      source.flatMap (fun letter => (substitution letter).toList) =
        left ++ right) :
    ∃ before letter after imageLeft imageRight,
      source = before ++ letter :: after ∧
      (substitution letter).toList = imageLeft ++ imageRight ∧
      left =
        before.flatMap (fun value => (substitution value).toList) ++
          imageLeft ∧
      right =
        imageRight ++
          after.flatMap (fun value => (substitution value).toList) := by
  induction source generalizing left with
  | nil =>
      exact False.elim (sourceNonempty rfl)
  | cons letter rest ih =>
      simp only [List.flatMap_cons] at split
      by_cases boundary :
          left.length ≤ (substitution letter).toList.length
      · let imageLeft :=
          List.take left.length (substitution letter).toList
        let imageRight :=
          List.drop left.length (substitution letter).toList
        have leftEq : left = imageLeft := by
          have taken := congrArg (List.take left.length) split
          rw [List.take_append_of_le_length boundary,
            List.take_left] at taken
          exact taken.symm
        have imageSplit :
            (substitution letter).toList =
              imageLeft ++ imageRight := by
          exact (List.take_append_drop left.length _).symm
        have rightEq :
            right =
              imageRight ++
                rest.flatMap (fun value => (substitution value).toList) := by
          apply List.append_cancel_left (as := left)
          rw [← split, imageSplit, leftEq]
          simp only [List.append_assoc]
        exact
          ⟨[], letter, rest, imageLeft, imageRight, by simp,
            imageSplit, by simpa using leftEq, rightEq⟩
      · have imageLengthLe : (substitution letter).toList.length ≤ left.length :=
          by omega
        let leftTail :=
          List.drop (substitution letter).toList.length left
        have leftEq :
            left = (substitution letter).toList ++ leftTail := by
          have taken := congrArg
            (List.take (substitution letter).toList.length) split
          have prefixEq :
              List.take (substitution letter).toList.length left =
                (substitution letter).toList := by
            rw [List.take_left,
              List.take_append_of_le_length imageLengthLe] at taken
            exact taken.symm
          calc
            left =
                List.take (substitution letter).toList.length left ++
                  List.drop (substitution letter).toList.length left :=
              (List.take_append_drop _ left).symm
            _ = (substitution letter).toList ++ leftTail := by
              rw [prefixEq]
        have tailSplit :
            rest.flatMap (fun value => (substitution value).toList) =
              leftTail ++ right := by
          apply List.append_cancel_left
            (as := (substitution letter).toList)
          rw [split, leftEq, List.append_assoc]
        have restNonempty : rest ≠ [] := by
          intro restEmpty
          subst rest
          simp only [List.flatMap_nil, List.append_nil] at split
          have lengths := congrArg List.length split
          simp at lengths
          omega
        rcases ih restNonempty tailSplit with
          ⟨before, pivot, after, imageLeft, imageRight,
            restEq, imageEq, leftTailEq, rightEq⟩
        refine
          ⟨letter :: before, pivot, after, imageLeft, imageRight,
            ?_, imageEq, ?_, rightEq⟩
        · simp [restEq]
        · rw [leftEq, leftTailEq]
          simp [List.flatMap_cons, List.append_assoc]

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter => (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have imagePositive : 1 ≤ (substitution letter).toList.length := by
        cases substitution letter
        simp [Word.toList]
      omega

private theorem word_toList_nonempty_member (word : Word Nat) :
    ∃ letter, letter ∈ word.toList := by
  cases word with
  | mk head tail => exact ⟨head, List.Mem.head tail⟩

private theorem bind_connected
    (word : Word Nat) (substitution : Nat → Word Nat)
    (connected : SourceWords.Connected word) :
    SourceWords.Connected (word.bind substitution) := by
  constructor
  · rw [Word.toList_bind]
    exact Nat.le_trans connected.1
      (list_length_le_flatMap_words word.toList substitution)
  · rintro ⟨targetLeft, targetRight, targetSplit, targetDisjoint⟩
    have sourceNonempty : word.toList ≠ [] := by
      cases word
      simp [Word.toList]
    have listSplit :
        word.toList.flatMap
            (fun letter => (substitution letter).toList) =
          targetLeft.toList ++ targetRight.toList := by
      rw [← Word.toList_bind, targetSplit, Word.toList_append]
    rcases
        flatMap_append_split substitution sourceNonempty listSplit with
      ⟨before, pivot, after, imageLeft, imageRight,
        sourceEq, imageEq, leftEq, rightEq⟩
    cases before with
    | nil =>
        simp only [List.nil_append] at sourceEq leftEq
        cases after with
        | nil =>
            have sourceLength := connected.1
            rw [sourceEq] at sourceLength
            simp at sourceLength
        | cons afterHead afterTail =>
            apply connected.2
            let sourceLeft : Word Nat := ⟨pivot, []⟩
            let sourceRight : Word Nat := ⟨afterHead, afterTail⟩
            refine ⟨sourceLeft, sourceRight, ?_, ?_⟩
            · apply Word.toList_injective
              rw [Word.toList_append]
              simpa [sourceLeft, sourceRight, Word.toList] using sourceEq
            · intro letter leftMember rightMember
              have letterEq : letter = pivot := by
                simpa [sourceLeft, Word.toList] using leftMember
              subst letter
              have pivotAfter :
                  pivot ∈ afterHead :: afterTail := by
                simpa [sourceRight, Word.toList] using rightMember
              cases imageLeft with
              | nil =>
                  have targetLeftEmpty : targetLeft.toList = [] := by
                    simpa using leftEq
                  cases targetLeft with
                  | mk head tail =>
                      simp [Word.toList] at targetLeftEmpty
              | cons witness witnesses =>
                  have witnessInImage :
                      witness ∈ (substitution pivot).toList := by
                    rw [imageEq]
                    simp
                  have witnessLeft : witness ∈ targetLeft.toList := by
                    rw [leftEq]
                    simp
                  have witnessRight : witness ∈ targetRight.toList := by
                    rw [rightEq]
                    apply List.mem_append.mpr
                    apply Or.inr
                    exact List.mem_flatMap.mpr
                      ⟨pivot, pivotAfter, witnessInImage⟩
                  exact targetDisjoint witness witnessLeft witnessRight
    | cons beforeHead beforeTail =>
        by_cases imageRightEmpty : imageRight = []
        · subst imageRight
          simp only [List.nil_append] at imageEq rightEq
          cases after with
          | nil =>
              have targetRightEmpty : targetRight.toList = [] := by
                simpa using rightEq
              cases targetRight with
              | mk head tail =>
                  simp [Word.toList] at targetRightEmpty
          | cons afterHead afterTail =>
              apply connected.2
              let sourceLeft : Word Nat :=
                ⟨beforeHead, beforeTail ++ [pivot]⟩
              let sourceRight : Word Nat := ⟨afterHead, afterTail⟩
              refine ⟨sourceLeft, sourceRight, ?_, ?_⟩
              · apply Word.toList_injective
                rw [Word.toList_append]
                simpa [sourceLeft, sourceRight, Word.toList,
                  List.append_assoc] using sourceEq
              · intro letter leftMember rightMember
                have leftCases :
                    letter ∈ beforeHead :: beforeTail ∨ letter = pivot := by
                  have flat :
                      letter = beforeHead ∨
                        letter ∈ beforeTail ∨
                        letter = pivot := by
                    simpa [sourceLeft, Word.toList] using leftMember
                  rcases flat with equals | inTail | equals
                  · exact Or.inl (by simp [equals])
                  · exact Or.inl (by simp [inTail])
                  · exact Or.inr equals
                have letterAfter :
                    letter ∈ afterHead :: afterTail := by
                  simpa [sourceRight, Word.toList] using rightMember
                rcases word_toList_nonempty_member (substitution letter) with
                  ⟨witness, witnessImage⟩
                have witnessLeft : witness ∈ targetLeft.toList := by
                  rw [leftEq]
                  apply List.mem_append.mpr
                  rcases leftCases with inBefore | rfl
                  · exact Or.inl (List.mem_flatMap.mpr
                      ⟨letter, inBefore, witnessImage⟩)
                  · exact Or.inr (by
                      have imageLeftEq :
                          (substitution letter).toList = imageLeft := by
                        simpa using imageEq
                      rw [← imageLeftEq]
                      exact witnessImage)
                have witnessRight : witness ∈ targetRight.toList := by
                  rw [rightEq]
                  exact List.mem_flatMap.mpr
                    ⟨letter, letterAfter, witnessImage⟩
                exact targetDisjoint witness witnessLeft witnessRight
        · cases imageRight with
          | nil => exact False.elim (imageRightEmpty rfl)
          | cons witness witnesses =>
              apply connected.2
              let sourceLeft : Word Nat := ⟨beforeHead, beforeTail⟩
              let sourceRight : Word Nat := ⟨pivot, after⟩
              refine ⟨sourceLeft, sourceRight, ?_, ?_⟩
              · apply Word.toList_injective
                rw [Word.toList_append]
                simpa [sourceLeft, sourceRight, Word.toList] using sourceEq
              · intro letter leftMember rightMember
                have letterBefore :
                    letter ∈ beforeHead :: beforeTail := by
                  simpa [sourceLeft, Word.toList] using leftMember
                have rightCases :
                    letter = pivot ∨ letter ∈ after := by
                  simpa [sourceRight, Word.toList] using rightMember
                rcases rightCases with rfl | letterAfter
                · have witnessInImage :
                      witness ∈ (substitution letter).toList := by
                    rw [imageEq]
                    simp
                  have witnessLeft : witness ∈ targetLeft.toList := by
                    rw [leftEq]
                    apply List.mem_append.mpr
                    exact Or.inl (List.mem_flatMap.mpr
                      ⟨letter, letterBefore, witnessInImage⟩)
                  have witnessRight : witness ∈ targetRight.toList := by
                    rw [rightEq]
                    simp
                  exact targetDisjoint witness witnessLeft witnessRight
                · rcases word_toList_nonempty_member (substitution letter) with
                    ⟨imageHead, imageHeadMem⟩
                  have imageHeadLeft :
                      imageHead ∈ targetLeft.toList := by
                    rw [leftEq]
                    apply List.mem_append.mpr
                    exact Or.inl (List.mem_flatMap.mpr
                      ⟨letter, letterBefore, imageHeadMem⟩)
                  have imageHeadRight :
                      imageHead ∈ targetRight.toList := by
                    rw [rightEq]
                    apply List.mem_append.mpr
                    exact Or.inr (List.mem_flatMap.mpr
                      ⟨letter, letterAfter, imageHeadMem⟩)
                  exact targetDisjoint imageHead imageHeadLeft
                    imageHeadRight

private theorem connected_forbids_list_cut
    {word : Word Nat} (connected : SourceWords.Connected word)
    (cut : Nat) (cutPositive : 1 ≤ cut)
    (cutProper : cut < word.toList.length)
    (disjoint :
      ListDisjoint (List.take cut word.toList) (List.drop cut word.toList)) :
    False := by
  have leftNonempty : List.take cut word.toList ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_take, List.length_nil] at lengths
    omega
  have rightNonempty : List.drop cut word.toList ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [List.length_drop] at lengths
    omega
  cases leftEq : List.take cut word.toList with
  | nil => exact False.elim (leftNonempty leftEq)
  | cons leftHead leftTail =>
      cases rightEq : List.drop cut word.toList with
      | nil => exact False.elim (rightNonempty rightEq)
      | cons rightHead rightTail =>
          apply connected.2
          let left : Word Nat := ⟨leftHead, leftTail⟩
          let right : Word Nat := ⟨rightHead, rightTail⟩
          refine ⟨left, right, ?_, ?_⟩
          · apply Word.toList_injective
            have splitLists :
                word.toList =
                  (leftHead :: leftTail) ++
                    (rightHead :: rightTail) := by
              calc
                word.toList =
                    List.take cut word.toList ++
                      List.drop cut word.toList :=
                  (List.take_append_drop cut word.toList).symm
                _ =
                    (leftHead :: leftTail) ++
                      (rightHead :: rightTail) := by
                  rw [leftEq, rightEq]
            simpa [left, right, Word.toList] using splitLists
          · intro letter leftMember rightMember
            apply disjoint letter
            · rw [leftEq]
              simpa [left, Word.toList] using leftMember
            · rw [rightEq]
              simpa [right, Word.toList] using rightMember

private theorem getElem_context_middle
    (pre middle post : List Nat) (position : Nat)
    (small : position < middle.length) :
    (pre ++ middle ++ post)[pre.length + position]'(by simp; omega) =
      middle[position] := by
  have inside :
      pre.length + position < (pre ++ middle).length := by
    simp
    omega
  rw [List.getElem_append_left inside]
  rw [List.getElem_append_right (Nat.le_add_right pre.length position)]
  simp

private theorem connected_factor_constant_of_head_interval
    {pre post : List Nat} {factor : Word Nat}
    {value start width : Nat}
    (connected : SourceWords.Connected factor)
    (interval :
      ValueInterval (pre ++ factor.toList ++ post) value start width)
    (headValue :
      factor.toList[0]'(by
        have := connected.1
        omega) = value) :
    ∀ entry, entry ∈ factor.toList → entry = value := by
  intro entry member
  by_cases equals : entry = value
  · exact equals
  rcases List.mem_iff_getElem.mp member with
    ⟨position, positionSmall, positionValue⟩
  have positionPositive : 1 ≤ position := by
    by_cases positionZero : position = 0
    · subst position
      exact False.elim
        (equals (positionValue.symm.trans headValue))
    · omega
  rcases interval with
    ⟨_, widthPositive, endBefore, atPosition⟩
  have factorStartSmall :
      pre.length < (pre ++ factor.toList ++ post).length := by
    simp
    have := connected.1
    omega
  have wholeHead :
      (pre ++ factor.toList ++ post)[pre.length] = value := by
    simpa using
      (getElem_context_middle pre factor.toList post 0 (by
        have := connected.1
        omega)).trans headValue
  have headBounds :=
    (atPosition pre.length factorStartSmall).mp wholeHead
  have wholePositionSmall :
      pre.length + position <
        (pre ++ factor.toList ++ post).length := by
    simp
    omega
  have wholePosition :
      (pre ++ factor.toList ++ post)[pre.length + position] = entry := by
    rw [getElem_context_middle pre factor.toList post position positionSmall]
    exact positionValue
  have outside :
      ¬(start ≤ pre.length + position ∧
        pre.length + position < start + width) := by
    intro bounds
    have equalsValue :=
      (atPosition (pre.length + position) wholePositionSmall).mpr bounds
    exact equals (wholePosition.symm.trans equalsValue)
  have intervalEndBeforePosition :
      start + width ≤ pre.length + position := by omega
  let cut := start + width - pre.length
  have cutPositive : 1 ≤ cut := by
    dsimp [cut]
    omega
  have cutProper : cut < factor.toList.length := by
    dsimp [cut]
    omega
  apply False.elim
  apply connected_forbids_list_cut connected cut cutPositive cutProper
  intro candidate leftMember rightMember
  have leftValue : candidate = value := by
    rcases List.mem_iff_getElem.mp leftMember with
      ⟨leftPosition, leftSmall, leftEquals⟩
    have leftPositionCut : leftPosition < cut := by
      have takeLength :
          (List.take cut factor.toList).length = cut :=
        List.length_take_of_le (Nat.le_of_lt cutProper)
      simpa [takeLength] using leftSmall
    have factorLeftSmall : leftPosition < factor.toList.length := by omega
    have wholeLeftSmall :
        pre.length + leftPosition <
          (pre ++ factor.toList ++ post).length := by
      simp
      omega
    have wholeLeft :
        (pre ++ factor.toList ++ post)[pre.length + leftPosition] =
          candidate := by
      rw [getElem_context_middle pre factor.toList post leftPosition
        factorLeftSmall]
      rw [← List.getElem_take
        (xs := factor.toList) (j := cut) (i := leftPosition)]
      exact leftEquals
    have bounds :
        start ≤ pre.length + leftPosition ∧
          pre.length + leftPosition < start + width := by
      constructor
      · omega
      · dsimp [cut] at leftPositionCut
        omega
    exact wholeLeft.symm.trans
      ((atPosition (pre.length + leftPosition) wholeLeftSmall).mpr bounds)
  have rightNotValue : candidate ≠ value := by
    intro candidateValue
    rcases List.mem_iff_getElem.mp rightMember with
      ⟨rightPosition, rightSmall, rightEquals⟩
    have factorRightSmall :
        cut + rightPosition < factor.toList.length := by
      have droppedLength :
          (List.drop cut factor.toList).length =
            factor.toList.length - cut :=
        List.length_drop
      rw [droppedLength] at rightSmall
      omega
    have wholeRightSmall :
        pre.length + (cut + rightPosition) <
          (pre ++ factor.toList ++ post).length := by
      simp
      omega
    have wholeRight :
        (pre ++ factor.toList ++ post)[pre.length + (cut + rightPosition)] =
          candidate := by
      rw [getElem_context_middle pre factor.toList post
        (cut + rightPosition) factorRightSmall]
      have dropped :
          (List.drop cut factor.toList)[rightPosition] =
            factor.toList[cut + rightPosition] := by
        simpa [Nat.add_comm] using
          (List.getElem_drop
            (xs := factor.toList) (i := cut) (j := rightPosition))
      rw [← dropped]
      exact rightEquals
    have bounds :=
      (atPosition (pre.length + (cut + rightPosition)) wholeRightSmall).mp
        (wholeRight.trans candidateValue)
    dsimp [cut] at bounds
    omega
  exact rightNotValue leftValue

private theorem connected_reverse {word : Word Nat}
    (connected : SourceWords.Connected word) :
    SourceWords.Connected word.reverse := by
  constructor
  · simpa [Word.toList_reverse] using connected.1
  · rintro ⟨left, right, split, disjoint⟩
    apply connected.2
    refine ⟨right.reverse, left.reverse, ?_, ?_⟩
    · have reversed := congrArg Word.reverse split
      simpa [Word.reverse_append] using reversed
    · intro letter rightMember leftMember
      apply disjoint letter
      · rw [Word.toList_reverse, List.mem_reverse] at leftMember
        exact leftMember
      · rw [Word.toList_reverse, List.mem_reverse] at rightMember
        exact rightMember

private theorem connected_factor_constant_of_tail_interval
    {pre post : List Nat} {factor : Word Nat}
    {value start width : Nat}
    (connected : SourceWords.Connected factor)
    (interval :
      ValueInterval (pre ++ factor.toList ++ post) value start width)
    (tailValue :
      factor.toList[factor.toList.length - 1]'(by
        have := connected.1
        omega) = value) :
    ∀ entry, entry ∈ factor.toList → entry = value := by
  have reversedInterval :
      ValueInterval
        ((pre ++ factor.toList ++ post).reverse)
        value
        ((pre ++ factor.toList ++ post).length - (start + width))
        width :=
    valueInterval_reverse interval
  have contextualReverse :
      (pre ++ factor.toList ++ post).reverse =
        post.reverse ++ factor.reverse.toList ++ pre.reverse := by
    simp [Word.toList_reverse, List.reverse_append, List.append_assoc]
  rw [contextualReverse] at reversedInterval
  have reversedConnected : SourceWords.Connected factor.reverse :=
    connected_reverse connected
  have reversedHead :
      factor.reverse.toList[0]'(by
        have := reversedConnected.1
        omega) = value := by
    have reverseListHead :
        factor.toList.reverse[0]'(by
          simp
          have := connected.1
          omega) = value := by
      rw [List.getElem_reverse]
      simpa using tailValue
    simpa [Word.toList_reverse] using reverseListHead
  have constantReverse :=
    connected_factor_constant_of_head_interval reversedConnected
      reversedInterval reversedHead
  intro entry member
  apply constantReverse entry
  rw [Word.toList_reverse, List.mem_reverse]
  exact member

private theorem connected_factor_content_of_inP
    {n : Nat} {pre post : List Nat} {factor : Word Nat}
    (positive : 1 ≤ n)
    (connected : SourceWords.Connected factor)
    (membership :
      ListInP n (pre ++ factor.toList ++ post)) :
    (∃ value, ∀ entry, entry ∈ factor.toList → entry = value) ∨
      (∀ value,
        (value = 0 ∨ ∃ i, i < n ∧ value = i + 1) →
          value ∈ factor.toList) := by
  have headSmall : 0 < factor.toList.length := by
    have := connected.1
    omega
  let headValue := factor.toList[0]'headSmall
  by_cases constant :
      ∀ entry, entry ∈ factor.toList →
        entry = headValue
  · exact Or.inl ⟨headValue, constant⟩
  apply Or.inr
  have existsDifferent :
      ∃ entry, entry ∈ factor.toList ∧
        entry ≠ headValue := by
    apply Classical.byContradiction
    intro none
    apply constant
    intro entry member
    apply Classical.byContradiction
    intro different
    exact none ⟨entry, member, different⟩
  have headMemberFactor : headValue ∈ factor.toList := by
    exact List.getElem_mem headSmall
  have headMemberWhole :
      headValue ∈ pre ++ factor.toList ++ post := by
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr headMemberFactor)))
  have headZero : headValue = 0 := by
    rcases (inP_mem_iff membership headValue).mp headMemberWhole with
      equals | ⟨i, iSmall, equals⟩
    · exact equals
    · have interval :=
        valueInterval_of_sandwich
          (inP_singleton_sandwich iSmall membership)
      rcases interval with ⟨start, width, valueInterval⟩
      have constantHead :=
        connected_factor_constant_of_head_interval connected
          (by simpa [equals] using valueInterval)
          (by simpa [headValue, equals])
      exact False.elim (constant (fun entry member =>
        (constantHead entry member).trans equals.symm))
  have factorLengthPositive : 1 ≤ factor.toList.length := by
    have := connected.1
    omega
  let tailPosition := factor.toList.length - 1
  let tailValue := factor.toList[tailPosition]'(by
    dsimp [tailPosition]
    omega)
  have tailMemberFactor : tailValue ∈ factor.toList :=
    List.getElem_mem (by
      dsimp [tailPosition]
      omega)
  have tailMemberWhole :
      tailValue ∈ pre ++ factor.toList ++ post := by
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr tailMemberFactor)))
  have tailZero : tailValue = 0 := by
    rcases (inP_mem_iff membership tailValue).mp tailMemberWhole with
      equals | ⟨i, iSmall, equals⟩
    · exact equals
    · rcases valueInterval_of_sandwich
          (inP_singleton_sandwich iSmall membership) with
        ⟨start, width, valueInterval⟩
      have constantTail :=
        connected_factor_constant_of_tail_interval connected
          (by simpa [equals] using valueInterval)
          (by simpa [tailPosition, tailValue, equals])
      have headEquals : headValue = i + 1 :=
        constantTail headValue headMemberFactor
      omega
  rcases existsDifferent with
    ⟨differentEntry, differentMember, differentFromHead⟩
  rcases List.mem_iff_getElem.mp differentMember with
    ⟨differentPosition, differentSmall, differentAt⟩
  have differentNonzero : differentEntry ≠ 0 := by
    intro zero
    apply differentFromHead
    exact zero.trans headZero.symm
  rcases sandwich_position_iff
      (inP_nonzero_sandwich positive membership) with
    ⟨nonzeroStart, nonzeroWidth, _, _, nonzeroEndBefore, nonzeroAt⟩
  have wholeDifferentSmall :
      pre.length + differentPosition <
        (pre ++ factor.toList ++ post).length := by
    simp
    omega
  have wholeDifferent :
      (pre ++ factor.toList ++ post)[pre.length + differentPosition] =
        differentEntry := by
    rw [getElem_context_middle pre factor.toList post
      differentPosition differentSmall]
    exact differentAt
  have differentSelected :
      (decide
        ((pre ++ factor.toList ++ post)[pre.length + differentPosition] ≠ 0) :
          Bool) = true := by
    simp only [decide_eq_true_eq]
    intro equalsZero
    apply differentNonzero
    exact wholeDifferent.symm.trans equalsZero
  have differentBounds :=
    (nonzeroAt (pre.length + differentPosition) wholeDifferentSmall).mp
      differentSelected
  have wholeHeadSmall :
      pre.length < (pre ++ factor.toList ++ post).length := by
    simp
    omega
  have wholeHead :
      (pre ++ factor.toList ++ post)[pre.length] = 0 := by
    have contextual :=
      getElem_context_middle pre factor.toList post 0 (by omega)
    simpa [headValue, headZero] using contextual
  have headOutside :
      ¬(nonzeroStart ≤ pre.length ∧
        pre.length < nonzeroStart + nonzeroWidth) := by
    intro bounds
    have selected :=
      (nonzeroAt pre.length wholeHeadSmall).mpr bounds
    have nonzero :
        (pre ++ factor.toList ++ post)[pre.length] ≠ 0 := by
      simpa using selected
    exact nonzero wholeHead
  have factorStartsBefore : pre.length < nonzeroStart := by
    omega
  have wholeTailPosition :
      pre.length + tailPosition =
        pre.length + factor.toList.length - 1 := by
    dsimp [tailPosition]
    omega
  have wholeTailSmall :
      pre.length + tailPosition <
        (pre ++ factor.toList ++ post).length := by
    simp
    dsimp [tailPosition]
    omega
  have wholeTail :
      (pre ++ factor.toList ++ post)[pre.length + tailPosition] = 0 := by
    rw [getElem_context_middle pre factor.toList post tailPosition (by
      dsimp [tailPosition]
      omega)]
    exact tailZero
  have tailOutside :
      ¬(nonzeroStart ≤ pre.length + tailPosition ∧
        pre.length + tailPosition < nonzeroStart + nonzeroWidth) := by
    intro bounds
    have selected :=
      (nonzeroAt (pre.length + tailPosition) wholeTailSmall).mpr bounds
    have nonzero :
        (pre ++ factor.toList ++ post)[pre.length + tailPosition] ≠ 0 := by
      simpa using selected
    exact nonzero wholeTail
  have factorEndsAfter :
      nonzeroStart + nonzeroWidth ≤ pre.length + tailPosition := by
    omega
  intro value domainValue
  rcases domainValue with rfl | ⟨i, iSmall, rfl⟩
  · rw [← headZero]
    exact headMemberFactor
  · rcases valueInterval_of_sandwich
        (inP_singleton_sandwich iSmall membership) with
      ⟨blockStart, blockWidth, blockInterval⟩
    have blockStartSmall :
        blockStart < (pre ++ factor.toList ++ post).length := by
      have := blockInterval.2.2.1
      omega
    have blockValue :
        (pre ++ factor.toList ++ post)[blockStart] = i + 1 :=
      (blockInterval.2.2.2 blockStart blockStartSmall).mpr (by
        have := blockInterval.2.1
        omega)
    have blockSelected :
        (decide
          ((pre ++ factor.toList ++ post)[blockStart] ≠ 0) : Bool) = true := by
      simp only [decide_eq_true_eq]
      rw [blockValue]
      omega
    have blockBounds :=
      (nonzeroAt blockStart blockStartSmall).mp blockSelected
    let factorPosition := blockStart - pre.length
    have factorPositionSmall :
        factorPosition < factor.toList.length := by
      dsimp [factorPosition, tailPosition] at *
      omega
    have factorValue :
        factor.toList[factorPosition] = i + 1 := by
      have contextual :=
        getElem_context_middle pre factor.toList post factorPosition
          factorPositionSmall
      have indexEq : pre.length + factorPosition = blockStart := by
        dsimp [factorPosition]
        omega
      have contextualValue :
          (pre ++ factor.toList ++ post)[pre.length + factorPosition] =
            i + 1 := by
        apply
          (blockInterval.2.2.2
            (pre.length + factorPosition) (by
              simp
              omega)).mpr
        have widthPositive := blockInterval.2.1
        rw [indexEq]
        omega
      exact contextual.symm.trans contextualValue
    rw [← factorValue]
    exact List.getElem_mem factorPositionSmall

private def firstNonzero : List Nat → Option Nat
  | [] => none
  | 0 :: rest => firstNonzero rest
  | (value + 1) :: _ => some (value + 1)

private theorem firstNonzero_zero_prefix
    (count : Nat) (rest : List Nat) :
    firstNonzero (List.replicate count 0 ++ rest) =
      firstNonzero rest := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, firstNonzero]
      exact ih

private theorem firstNonzero_positive_run
    (value count : Nat) (positive : 1 ≤ count) (rest : List Nat) :
    firstNonzero (List.replicate count (value + 1) ++ rest) =
      some (value + 1) := by
  cases count with
  | zero => omega
  | succ count => rfl

private theorem firstNonzero_orderedBlocks
    {n : Nat} (positive : 1 ≤ n)
    (exponents : Nat → Nat)
    (large : ∀ i, i < n → 2 ≤ exponents i)
    (rest : List Nat) :
    firstNonzero (orderedBlocks (List.range n) exponents ++ rest) =
      some 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [orderedBlocks, List.range_succ_eq_map]
      simp only [List.flatMap_cons, List.flatMap_map, List.append_assoc,
        powerBlock]
      exact firstNonzero_positive_run 0 (exponents 0)
        (by have := large 0 (by omega); omega) _

private theorem firstNonzero_inP
    {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n) (membership : ListInP n letters) :
    firstNonzero letters = some 1 := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents, _, _, large, shape⟩
  rw [shape, List.append_assoc,
    firstNonzero_zero_prefix,
    firstNonzero_orderedBlocks positive exponents large]

private theorem firstNonzero_reverse_orderedBlocks
    {n : Nat} (positive : 1 ≤ n)
    (exponents : Nat → Nat)
    (large : ∀ i, i < n → 2 ≤ exponents i)
    (rest : List Nat) :
    firstNonzero
        ((orderedBlocks (List.range n) exponents).reverse ++ rest) =
      some n := by
  cases n with
  | zero => omega
  | succ n =>
      rw [orderedBlocks, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton, List.reverse_append,
        List.append_assoc, powerBlock, List.reverse_replicate]
      exact firstNonzero_positive_run n (exponents n)
        (by have := large n (by omega); omega) _

private theorem firstNonzero_inQ
    {n : Nat} {letters : List Nat}
    (positive : 1 ≤ n) (membership : ListInQ n letters) :
    firstNonzero letters = some n := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents,
      leftPositive, rightPositive, large, reverseShape⟩
  have shape := congrArg List.reverse reverseShape
  simp only [List.reverse_append, List.reverse_replicate,
    List.reverse_reverse] at shape
  rw [shape, firstNonzero_zero_prefix,
    firstNonzero_reverse_orderedBlocks positive exponents large]

private theorem firstNonzero_constant_replacement
    (pre post left right : List Nat) (value : Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConstant : ∀ entry, entry ∈ left → entry = value)
    (rightConstant : ∀ entry, entry ∈ right → entry = value) :
    firstNonzero (pre ++ left ++ post) =
      firstNonzero (pre ++ right ++ post) := by
  have leftShape :
      left = List.replicate left.length value :=
    List.eq_replicate_iff.mpr ⟨rfl, leftConstant⟩
  have rightShape :
      right = List.replicate right.length value :=
    List.eq_replicate_iff.mpr ⟨rfl, rightConstant⟩
  rw [leftShape, rightShape]
  have leftPositive : 1 ≤ left.length := by
    exact (List.length_pos_iff.mpr leftNonempty)
  have rightPositive : 1 ≤ right.length := by
    exact (List.length_pos_iff.mpr rightNonempty)
  induction pre with
  | nil =>
      simp only [List.nil_append]
      cases value with
      | zero =>
          rw [firstNonzero_zero_prefix, firstNonzero_zero_prefix]
      | succ value =>
          rw [firstNonzero_positive_run value left.length leftPositive,
            firstNonzero_positive_run value right.length rightPositive]
  | cons head tail ih =>
      cases head with
      | zero =>
          simp only [List.cons_append, firstNonzero]
          exact ih
      | succ value => rfl

private theorem bind_constant_of_sameContent
    {identity : Identity Nat} (substitution : Nat → Word Nat)
    (sameContent :
      SourceWords.SameContent identity.lhs identity.rhs)
    {value : Nat}
    (leftConstant :
      ∀ entry, entry ∈ (identity.lhs.bind substitution).toList →
        entry = value) :
    ∀ entry, entry ∈ (identity.rhs.bind substitution).toList →
      entry = value := by
  intro entry member
  rw [Word.toList_bind] at member
  rcases List.mem_flatMap.mp member with
    ⟨letter, letterMember, entryMember⟩
  apply leftConstant entry
  rw [Word.toList_bind]
  exact List.mem_flatMap.mpr
    ⟨letter, (sameContent letter).mpr letterMember, entryMember⟩

private theorem nodup_length_le_of_subset
    {source target : List Nat}
    (nodup : source.Nodup)
    (subset : ∀ value, value ∈ source → value ∈ target) :
    source.length ≤ target.length := by
  induction source generalizing target with
  | nil => simp
  | cons head tail ih =>
      have nodupParts := List.pairwise_cons.mp nodup
      have headNotTail : head ∉ tail := by
        intro member
        exact (nodupParts.1 head member) rfl
      have tailNodup : tail.Nodup := nodupParts.2
      have headTarget : head ∈ target :=
        subset head (List.Mem.head tail)
      have tailSubset :
          ∀ value, value ∈ tail → value ∈ target.erase head := by
        intro value member
        have different : value ≠ head := by
          intro equals
          subst value
          exact headNotTail member
        exact (List.mem_erase_of_ne different).mpr
          (subset value (List.Mem.tail head member))
      have lengthBound := ih tailNodup tailSubset
      rw [List.length_erase_of_mem headTarget] at lengthBound
      have targetPositive : 1 ≤ target.length := by
        apply List.length_pos_iff.mpr
        intro empty
        subst target
        simp at headTarget
      simp only [List.length_cons]
      omega

private theorem exists_nonconstant_substitution_image
    {n : Nat} {identity : Identity Nat}
    (substitution : Nat → Word Nat)
    (uses : identity.UsesAtMost n)
    (fullSupport :
      ∀ value,
        (value = 0 ∨ ∃ i, i < n ∧ value = i + 1) →
          value ∈ (identity.lhs.bind substitution).toList) :
    ∃ letter,
      letter ∈ identity.lhs.toList ∧
      ¬(∀ entry, entry ∈ (substitution letter).toList →
          entry = (substitution letter).head) := by
  rcases uses with
    ⟨variables, variablesBound, leftOnly, _⟩
  apply Classical.byContradiction
  intro none
  have imageConstant :
      ∀ letter, letter ∈ identity.lhs.toList →
        ∀ entry, entry ∈ (substitution letter).toList →
          entry = (substitution letter).head := by
    intro letter letterMember
    apply Classical.byContradiction
    intro notConstant
    exact none ⟨letter, letterMember, notConstant⟩
  let representatives :=
    variables.map fun letter => (substitution letter).head
  have rangeSubset :
      ∀ value, value ∈ List.range (n + 1) →
        value ∈ representatives := by
    intro value valueSmall
    have valueLe : value ≤ n := by
      have := List.mem_range.mp valueSmall
      omega
    have valueDomain :
        value = 0 ∨ ∃ i, i < n ∧ value = i + 1 := by
      cases value with
      | zero => exact Or.inl rfl
      | succ i => exact Or.inr ⟨i, by omega, rfl⟩
    have valueMember := fullSupport value valueDomain
    rw [Word.toList_bind] at valueMember
    rcases List.mem_flatMap.mp valueMember with
      ⟨letter, letterMember, imageMember⟩
    have representativeEq :
        value = (substitution letter).head :=
      imageConstant letter letterMember value imageMember
    rw [representativeEq]
    exact List.mem_map.mpr
      ⟨letter, leftOnly letter letterMember, rfl⟩
  have lengthBound :=
    nodup_length_le_of_subset List.nodup_range rangeSubset
  have representativesLength :
      representatives.length = variables.length := by
    simp [representatives]
  rw [List.length_range, representativesLength] at lengthBound
  omega

private def AdjacentPair (left right : Nat) (letters : List Nat) : Prop :=
  ∃ before after, letters = before ++ left :: right :: after

private def ForwardBoundary (n left right : Nat) : Prop :=
  (left = 0 ∧ right = 1) ∨
    (∃ i, i + 1 < n ∧ left = i + 1 ∧ right = i + 2) ∨
    (left = n ∧ right = 0)

private theorem adjacentPair_reverse
    {left right : Nat} {letters : List Nat}
    (pair : AdjacentPair left right letters) :
    AdjacentPair right left letters.reverse := by
  rcases pair with ⟨before, after, shape⟩
  refine ⟨after.reverse, before.reverse, ?_⟩
  rw [shape]
  simp [List.reverse_append, List.append_assoc]

private theorem adjacentPair_in_context
    {left right : Nat} {middle : List Nat}
    (pre post : List Nat)
    (pair : AdjacentPair left right middle) :
    AdjacentPair left right (pre ++ middle ++ post) := by
  rcases pair with ⟨before, after, shape⟩
  refine ⟨pre ++ before, after ++ post, ?_⟩
  rw [shape]
  simp [List.append_assoc]

private theorem adjacentPair_in_flatMap
    (substitution : Nat → Word Nat)
    {source : List Nat} {letter left right : Nat}
    (letterMember : letter ∈ source)
    (pair : AdjacentPair left right (substitution letter).toList) :
    AdjacentPair left right
      (source.flatMap fun value => (substitution value).toList) := by
  rcases List.append_of_mem letterMember with
    ⟨before, after, sourceShape⟩
  rcases pair with ⟨imageBefore, imageAfter, imageShape⟩
  refine
    ⟨before.flatMap (fun value => (substitution value).toList) ++
        imageBefore,
      imageAfter ++
        after.flatMap (fun value => (substitution value).toList),
      ?_⟩
  rw [sourceShape, List.flatMap_append, List.flatMap_cons, imageShape]
  simp [List.append_assoc]

private theorem exists_adjacent_ne_of_nonconstant
    (word : Word Nat)
    (notConstant :
      ¬(∀ entry, entry ∈ word.toList → entry = word.head)) :
    ∃ left right,
      left ≠ right ∧ AdjacentPair left right word.toList := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil =>
          exfalso
          apply notConstant
          intro entry member
          simpa [Word.toList] using member
      | cons next rest ih =>
          by_cases different : head ≠ next
          · exact ⟨head, next, different, [], rest, by
              simp [Word.toList]⟩
          · have equal : next = head := by omega
            have tailNotConstant :
                ¬(∀ entry,
                  entry ∈ (Word.mk next rest : Word Nat).toList →
                    entry = next) := by
              intro tailConstant
              apply notConstant
              intro entry member
              simp only [Word.toList, List.mem_cons] at member
              rcases member with rfl | member
              · rfl
              · exact
                  (tailConstant entry (by
                    simpa [Word.toList] using member)).trans equal
            rcases ih next tailNotConstant with
              ⟨left, right, leftNeRight, before, after, tailShape⟩
            exact
              ⟨left, right, leftNeRight, head :: before, after, by
                change next :: rest =
                  before ++ left :: right :: after at tailShape
                exact congrArg (List.cons head) tailShape⟩

private theorem adjacentPair_positions
    {left right : Nat} {letters : List Nat}
    (pair : AdjacentPair left right letters) :
    ∃ position,
      position + 1 < letters.length ∧
        letters[position]? = some left ∧
          letters[position + 1]? = some right := by
  rcases pair with ⟨before, after, shape⟩
  refine ⟨before.length, ?_, ?_, ?_⟩
  · rw [shape]
    simp
  · rw [shape]
    simp
  · rw [shape]
    simp

private theorem inP_value_intervals_forward
    {n : Nat} {letters : List Nat}
    (atLeastTwo : 2 ≤ n) (membership : ListInP n letters) :
    ∃ start width : Nat → Nat,
      (∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i)) ∧
      (∀ i, i + 1 < n →
        start i + width i = start (i + 1)) := by
  have intervalExists :
      ∀ i, i < n →
        ∃ bounds : Nat × Nat,
          ValueInterval letters (i + 1) bounds.1 bounds.2 := by
    intro i iSmall
    rcases valueInterval_of_sandwich
        (inP_singleton_sandwich iSmall membership) with
      ⟨start, width, interval⟩
    exact ⟨(start, width), interval⟩
  let bounds : Nat → Nat × Nat := fun i =>
    if iSmall : i < n then
      Classical.choose (intervalExists i iSmall)
    else
      (0, 0)
  let start := fun i => (bounds i).1
  let width := fun i => (bounds i).2
  have intervals :
      ∀ i, i < n →
        ValueInterval letters (i + 1) (start i) (width i) := by
    intro i iSmall
    dsimp [start, width, bounds]
    simp only [dif_pos iSmall]
    exact Classical.choose_spec (intervalExists i iSmall)
  have adjacent :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1) ∨
          start (i + 1) + width (i + 1) = start i := by
    intro i pairSmall
    exact
      value_intervals_adjacent_of_pair_sandwich
        (leftValue := i + 1) (rightValue := i + 2)
        (by omega)
        (intervals i (by omega))
        (by
          simpa [Nat.add_assoc] using intervals (i + 1) (by omega))
        (inP_pair_sandwich pairSmall membership)
  rcases adjacency_chain_orientation atLeastTwo start width intervals adjacent
      with forward | reverse
  · exact ⟨start, width, intervals, forward⟩
  · have domain :
        ∀ letter, letter ∈ letters ↔
          letter = 0 ∨ ∃ i, i < n ∧ letter = i + 1 :=
      fun letter => inP_mem_iff membership letter
    have large :
        ∀ letter, letter ∈ letters → 2 ≤ letters.count letter :=
      fun letter member => inP_count_at_least_two membership member
    have nonzero :=
      inP_nonzero_sandwich (by omega) membership
    have alsoQ :=
      listInQ_of_reverse_intervals (by omega) domain large nonzero
        start width intervals reverse
    have firstP := firstNonzero_inP (by omega) membership
    have firstQ := firstNonzero_inQ (by omega) alsoQ
    rw [firstP] at firstQ
    have : n = 1 := Option.some.inj firstQ.symm
    omega

private theorem start_mono_of_forward
    {n : Nat} (start width : Nat → Nat)
    (forward :
      ∀ i, i + 1 < n →
        start i + width i = start (i + 1)) :
    ∀ j, j < n → ∀ i, i ≤ j → start i ≤ start j := by
  intro j jSmall
  induction j with
  | zero =>
      intro i iLe
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      intro i iLe
      by_cases equal : i = j + 1
      · subst i
        exact Nat.le_refl _
      · have previous := ih (by omega) i (by omega)
        have touches := forward j (by omega)
        omega

private theorem adjacent_unequal_inP_forwardBoundary
    {n left right : Nat} {letters : List Nat}
    (atLeastTwo : 2 ≤ n)
    (membership : ListInP n letters)
    (different : left ≠ right)
    (pair : AdjacentPair left right letters) :
    ForwardBoundary n left right := by
  rcases adjacentPair_positions pair with
    ⟨position, pairSmall, leftOption, rightOption⟩
  rcases List.getElem?_eq_some_iff.mp leftOption with
    ⟨leftSmall, leftAt⟩
  rcases List.getElem?_eq_some_iff.mp rightOption with
    ⟨rightSmall, rightAt⟩
  have leftMember : left ∈ letters := by
    rw [← leftAt]
    exact List.getElem_mem leftSmall
  have rightMember : right ∈ letters := by
    rw [← rightAt]
    exact List.getElem_mem rightSmall
  have leftDomain := (inP_mem_iff membership left).mp leftMember
  have rightDomain := (inP_mem_iff membership right).mp rightMember
  rcases inP_value_intervals_forward atLeastTwo membership with
    ⟨start, width, intervals, forward⟩
  have startMono := start_mono_of_forward start width forward
  rcases sandwich_position_iff
      (inP_nonzero_sandwich (by omega) membership) with
    ⟨nonzeroStart, nonzeroWidth, _, _, nonzeroEndBefore, nonzeroAt⟩
  have intervalInside :
      ∀ i, i < n →
        nonzeroStart ≤ start i ∧
          start i + width i ≤ nonzeroStart + nonzeroWidth := by
    intro i iSmall
    rcases intervals i iSmall with
      ⟨_, widthPositive, endBefore, atPosition⟩
    have startSmall : start i < letters.length := by omega
    have startValue :
        letters[start i] = i + 1 :=
      (atPosition (start i) startSmall).mpr (by omega)
    have startSelected :
        (decide (letters[start i] ≠ 0) : Bool) = true := by
      simp [startValue]
    have startBounds := (nonzeroAt (start i) startSmall).mp startSelected
    have lastSmall : start i + width i - 1 < letters.length := by omega
    have lastValue :
        letters[start i + width i - 1] = i + 1 :=
      (atPosition (start i + width i - 1) lastSmall).mpr (by omega)
    have lastSelected :
        (decide (letters[start i + width i - 1] ≠ 0) : Bool) = true := by
      simp [lastValue]
    have lastBounds :=
      (nonzeroAt (start i + width i - 1) lastSmall).mp lastSelected
    omega
  have firstStart : start 0 = nonzeroStart := by
    have zeroInside := (intervalInside 0 (by omega)).1
    have nonzeroStartSmall : nonzeroStart < letters.length := by omega
    have selected :
        (decide (letters[nonzeroStart] ≠ 0) : Bool) = true :=
      (nonzeroAt nonzeroStart nonzeroStartSmall).mpr (by omega)
    have nonzeroValue : letters[nonzeroStart] ≠ 0 := by
      simpa using selected
    have member : letters[nonzeroStart] ∈ letters :=
      List.getElem_mem nonzeroStartSmall
    rcases (inP_mem_iff membership letters[nonzeroStart]).mp member with
      equalsZero | ⟨i, iSmall, equals⟩
    · exact False.elim (nonzeroValue equalsZero)
    · have inInterval :
          start i ≤ nonzeroStart :=
        ((intervals i iSmall).2.2.2 nonzeroStart nonzeroStartSmall).mp
          equals |>.1
      have firstLe := startMono i iSmall 0 (by omega)
      omega
  let last := n - 1
  have lastSmall : last < n := by
    dsimp [last]
    omega
  have endMono :
      ∀ i, i < n →
        start i + width i ≤ start last + width last := by
    intro i iSmall
    by_cases equal : i = last
    · subst i
      exact Nat.le_refl _
    · have beforeLast : i < last := by
        dsimp [last] at *
        omega
      have touches := forward i (by omega)
      have startsLe := startMono last lastSmall (i + 1) (by omega)
      omega
  have lastEnd :
      start last + width last = nonzeroStart + nonzeroWidth := by
    have inside := (intervalInside last lastSmall).2
    have endPositionSmall :
        nonzeroStart + nonzeroWidth - 1 < letters.length := by omega
    have selected :
        (decide
          (letters[nonzeroStart + nonzeroWidth - 1] ≠ 0) : Bool) = true :=
      (nonzeroAt (nonzeroStart + nonzeroWidth - 1) endPositionSmall).mpr
        (by omega)
    have nonzeroValue :
        letters[nonzeroStart + nonzeroWidth - 1] ≠ 0 := by
      simpa using selected
    have member :
        letters[nonzeroStart + nonzeroWidth - 1] ∈ letters :=
      List.getElem_mem endPositionSmall
    rcases
        (inP_mem_iff membership
          letters[nonzeroStart + nonzeroWidth - 1]).mp member with
      equalsZero | ⟨i, iSmall, equals⟩
    · exact False.elim (nonzeroValue equalsZero)
    · have inInterval :=
        ((intervals i iSmall).2.2.2
          (nonzeroStart + nonzeroWidth - 1) endPositionSmall).mp equals
      have endLe := endMono i iSmall
      omega
  rcases leftDomain with rfl | ⟨i, iSmall, rfl⟩
  · rcases rightDomain with rfl | ⟨j, jSmall, rfl⟩
    · exact False.elim (different rfl)
    · apply Or.inl
      refine ⟨rfl, ?_⟩
      have rightSelected :
          (decide (letters[position + 1] ≠ 0) : Bool) = true := by
        simp [rightAt]
      have rightBounds :=
        (nonzeroAt (position + 1) rightSmall).mp rightSelected
      have leftOutside :
          ¬(nonzeroStart ≤ position ∧
            position < nonzeroStart + nonzeroWidth) := by
        intro bounds
        have selected := (nonzeroAt position leftSmall).mpr bounds
        simp [leftAt] at selected
      have positionEq : position + 1 = nonzeroStart := by omega
      have zeroInterval := intervals 0 (by omega)
      have widthPositive := zeroInterval.2.1
      have valueOne :
          letters[position + 1] = 1 := by
        apply (zeroInterval.2.2.2 (position + 1) rightSmall).mpr
        rw [firstStart, positionEq]
        omega
      omega
  · rcases rightDomain with rfl | ⟨j, jSmall, rfl⟩
    · apply Or.inr
      apply Or.inr
      refine ⟨?_, rfl⟩
      have leftSelected :
          (decide (letters[position] ≠ 0) : Bool) = true := by
        simp [leftAt]
      have leftBounds := (nonzeroAt position leftSmall).mp leftSelected
      have rightOutside :
          ¬(nonzeroStart ≤ position + 1 ∧
            position + 1 < nonzeroStart + nonzeroWidth) := by
        intro bounds
        have selected := (nonzeroAt (position + 1) rightSmall).mpr bounds
        simp [rightAt] at selected
      have positionEq :
          position + 1 = nonzeroStart + nonzeroWidth := by omega
      have lastInterval := intervals last lastSmall
      have widthPositive := lastInterval.2.1
      have lastPosition :
          position = start last + width last - 1 := by
        rw [← lastEnd] at positionEq
        omega
      have valueLast :
          letters[position] = last + 1 := by
        apply (lastInterval.2.2.2 position leftSmall).mpr
        rw [lastPosition]
        omega
      dsimp [last] at valueLast
      omega
    · apply Or.inr
      apply Or.inl
      have indicesDifferent : i ≠ j := by
        intro equals
        subst j
        exact different rfl
      by_cases order : i < j
      · have nextSmall : i + 1 < n := by omega
        have touches := forward i (by omega)
        have startsLe := startMono j jSmall (i + 1) (by omega)
        have leftBounds :=
          ((intervals i iSmall).2.2.2 position leftSmall).mp leftAt
        have rightBounds :=
          ((intervals j jSmall).2.2.2 (position + 1) rightSmall).mp
            rightAt
        have boundaryEq :
            position + 1 = start (i + 1) := by omega
        have nextInterval := intervals (i + 1) nextSmall
        have nextWidthPositive := nextInterval.2.1
        have nextValue :
            letters[position + 1] = i + 2 := by
          apply (nextInterval.2.2.2 (position + 1) rightSmall).mpr
          rw [boundaryEq]
          omega
        refine ⟨i, by omega, rfl, ?_⟩
        omega
      · have orderReverse : j < i := by omega
        have nextSmall : j + 1 < n := by omega
        have touches := forward j (by omega)
        have startsLe := startMono i iSmall (j + 1) (by omega)
        have leftBounds :=
          ((intervals i iSmall).2.2.2 position leftSmall).mp leftAt
        have rightBounds :=
          ((intervals j jSmall).2.2.2 (position + 1) rightSmall).mp
            rightAt
        omega

private theorem forwardBoundary_ne
    {n left right : Nat}
    (atLeastTwo : 2 ≤ n)
    (boundary : ForwardBoundary n left right) :
    left ≠ right := by
  rcases boundary with boundary | boundary | boundary
  · omega
  · rcases boundary with ⟨i, iSmall, rfl, rfl⟩
    omega
  · omega

private theorem forwardBoundary_reverse_impossible
    {n left right : Nat}
    (atLeastTwo : 2 ≤ n)
    (forward : ForwardBoundary n left right)
    (reverse : ForwardBoundary n right left) :
    False := by
  rcases forward with forward | forward | forward
  · rcases reverse with reverse | reverse | reverse
    · omega
    · rcases reverse with ⟨i, iSmall, _, _⟩
      omega
    · omega
  · rcases forward with ⟨i, iSmall, rfl, rfl⟩
    rcases reverse with reverse | reverse | reverse
    · omega
    · rcases reverse with ⟨j, jSmall, _, _⟩
      omega
    · omega
  · rcases reverse with reverse | reverse | reverse
    · omega
    · rcases reverse with ⟨i, iSmall, _, _⟩
      omega
    · omega

private theorem no_forwardBoundary_inQ
    {n left right : Nat} {letters : List Nat}
    (atLeastTwo : 2 ≤ n)
    (membership : ListInQ n letters)
    (boundary : ForwardBoundary n left right)
    (pair : AdjacentPair left right letters) :
    False := by
  have reversePair := adjacentPair_reverse pair
  have reverseBoundary :=
    adjacent_unequal_inP_forwardBoundary atLeastTwo membership
      (Ne.symm (forwardBoundary_ne atLeastTwo boundary)) reversePair
  exact
    forwardBoundary_reverse_impossible atLeastTwo boundary reverseBoundary

/-- Pure source-word core of the orientation exclusion in Lemma 6.

The semigroup-validity assumption has been replaced by exactly its two
Lemma 1 consequences: equal content and preservation of simple letters.
Everything else is contextual substitution, connectedness, the variable
bound, and the explicit `P_n`/`Q_n` word shapes. -/
def OrientationCombinatorics : Prop :=
  ∀ (n : Nat) (identity : Identity Nat)
      (pre post : List Nat) (substitution : Nat → Word Nat),
    2 ≤ n →
    SourceWords.ConnectedIdentity identity →
    SourceWords.SameContent identity.lhs identity.rhs →
    (∀ letter,
      SourceWords.SimpleIn letter identity.lhs ↔
        SourceWords.SimpleIn letter identity.rhs) →
    identity.UsesAtMost n →
    ListInP n
      (pre ++ (identity.lhs.bind substitution).toList ++ post) →
    ListInQ n
      (pre ++ (identity.rhs.bind substitution).toList ++ post) →
    False

/-- The strictly smaller orientation boundary after connected-image and
connected-factor classification have been discharged. -/
def OrientationTransitionKernel : Prop :=
  ∀ (n : Nat) (identity : Identity Nat)
      (pre post : List Nat) (substitution : Nat → Word Nat),
    2 ≤ n →
    SourceWords.Connected identity.rhs →
    SourceWords.SameContent identity.lhs identity.rhs →
    (∀ letter,
      SourceWords.SimpleIn letter identity.lhs ↔
        SourceWords.SimpleIn letter identity.rhs) →
    identity.UsesAtMost n →
    ListInP n
      (pre ++ (identity.lhs.bind substitution).toList ++ post) →
    ListInQ n
      (pre ++ (identity.rhs.bind substitution).toList ++ post) →
    ((∃ value,
        ∀ entry,
          entry ∈ (identity.lhs.bind substitution).toList →
            entry = value) ∨
      (∀ value,
        (value = 0 ∨ ∃ i, i < n ∧ value = i + 1) →
          value ∈ (identity.lhs.bind substitution).toList)) →
    False

theorem orientationTransitionKernel : OrientationTransitionKernel := by
  intro n identity pre post substitution atLeastTwo _ sameContent _ uses
    sourceInP targetInQ classified
  rcases classified with ⟨value, leftConstant⟩ | fullSupport
  · have rightConstant :=
      bind_constant_of_sameContent substitution sameContent leftConstant
    have leftNonempty :
        (identity.lhs.bind substitution).toList ≠ [] := by
      cases identity.lhs.bind substitution
      simp [Word.toList]
    have rightNonempty :
        (identity.rhs.bind substitution).toList ≠ [] := by
      cases identity.rhs.bind substitution
      simp [Word.toList]
    have sameFirst :=
      firstNonzero_constant_replacement pre post
        (identity.lhs.bind substitution).toList
        (identity.rhs.bind substitution).toList value
        leftNonempty rightNonempty leftConstant rightConstant
    have sourceFirst := firstNonzero_inP (by omega) sourceInP
    have targetFirst := firstNonzero_inQ (by omega) targetInQ
    rw [sourceFirst, targetFirst] at sameFirst
    have : 1 = n := Option.some.inj sameFirst
    omega
  · rcases
        exists_nonconstant_substitution_image substitution uses fullSupport with
      ⟨letter, letterMember, imageNotConstant⟩
    rcases
        exists_adjacent_ne_of_nonconstant
          (substitution letter) imageNotConstant with
      ⟨left, right, different, imagePair⟩
    have sourceInnerPair :
        AdjacentPair left right
          (identity.lhs.bind substitution).toList := by
      rw [Word.toList_bind]
      exact adjacentPair_in_flatMap substitution letterMember imagePair
    have sourcePair :=
      adjacentPair_in_context pre post sourceInnerPair
    have boundary :=
      adjacent_unequal_inP_forwardBoundary atLeastTwo sourceInP different
        sourcePair
    have targetLetterMember : letter ∈ identity.rhs.toList :=
      (sameContent letter).mp letterMember
    have targetInnerPair :
        AdjacentPair left right
          (identity.rhs.bind substitution).toList := by
      rw [Word.toList_bind]
      exact
        adjacentPair_in_flatMap substitution targetLetterMember imagePair
    have targetPair :=
      adjacentPair_in_context pre post targetInnerPair
    exact
      no_forwardBoundary_inQ atLeastTwo targetInQ boundary targetPair

theorem orientationCombinatorics_of_transitionKernel
    (kernel : OrientationTransitionKernel) :
    OrientationCombinatorics := by
  intro n identity pre post substitution atLeastTwo connected sameContent
    simple uses sourceInP targetInQ
  apply kernel n identity pre post substitution atLeastTwo connected.2
    sameContent simple uses sourceInP targetInQ
  exact
    connected_factor_content_of_inP (by omega)
      (bind_connected identity.lhs substitution connected.1) sourceInP

theorem orientationCombinatorics : OrientationCombinatorics :=
  orientationCombinatorics_of_transitionKernel orientationTransitionKernel

/-- A single explicit, semantics-free certificate for the entire remaining
Lee `L` frontier. -/
structure CombinatorialCore : Prop where
  mateRigidity : MateRigidity
  orientation : OrientationCombinatorics

def combinatorialCore : CombinatorialCore where
  mateRigidity := mateRigidity
  orientation := orientationCombinatorics

end BlockCombinatorics

end SemigroupBasis.Examples.LeeL
