import SemigroupBasis.CoRoots.Order6LeeZhangClass453Normalization
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.CoRoots.S5_254Canonical
import SemigroupBasis.Examples.SimpleSequenceFirstGap

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass453

open SemigroupBasis
open SemigroupBasis.Examples

private theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    S5_107.cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold S5_107.cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-! ## Reading the first-gap scanner literally -/

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (pairKeep x y)

private def orderScanFrom
    (x y : Nat) (initial : S5_793Invariant.OrderGapState)
    (letters : List Nat) : S5_793Invariant.OrderGapState :=
  letters.foldl
    (fun state letter =>
      S5_793Invariant.orderStep state
        (S5_793Invariant.orderSymbol x y letter))
    initial

private theorem orderScanFrom_pairProjection
    (x y : Nat) :
    forall (letters : List Nat)
      (initial : S5_793Invariant.OrderGapState),
      orderScanFrom x y initial letters =
        orderScanFrom x y initial (pairProjection letters x y)
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases isX : letter = x
      · subst letter
        have induction :=
          orderScanFrom_pairProjection x y rest
            (S5_793Invariant.orderStep initial
              (S5_793Invariant.orderSymbol x y x))
        simpa [orderScanFrom, pairProjection, pairKeep] using induction
      · by_cases isY : letter = y
        · subst letter
          have induction :=
            orderScanFrom_pairProjection x y rest
              (S5_793Invariant.orderStep initial
                (S5_793Invariant.orderSymbol x y y))
          simpa [orderScanFrom, pairProjection, pairKeep, isX]
            using induction
        · have induction :=
            orderScanFrom_pairProjection x y rest initial
          simpa [orderScanFrom, pairProjection, pairKeep,
            S5_793Invariant.orderSymbol, isX, isY] using induction

private theorem pairProjection_count_of_kept
    (letters : List Nat) (x y selected : Nat)
    (kept : pairKeep x y selected = true) :
    (pairProjection letters x y).count selected =
      letters.count selected := by
  unfold pairProjection
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = selected
      · subst first
        simp [kept, induction]
      · by_cases firstKept : pairKeep x y first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem pairProjection_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ pairProjection letters x y) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem pairList_length
    {x y : Nat} (different : x ≠ y) :
    forall letters : List Nat,
      (forall value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          forall selected, selected ∈ rest →
            selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction := pairList_length different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      forall value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [pairList_length different letters onlyPair, xCount, yCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  rcases firstPair with rfl | rfl
  · rcases secondPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases secondPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairProjection_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1) :
    pairProjection letters x y = [x, y] ∨
      pairProjection letters x y = [y, x] := by
  apply pairList_shape_one_one
  · exact different
  · rw [pairProjection_count_of_kept]
    · exact xCount
    · simp [pairKeep]
  · rw [pairProjection_count_of_kept]
    · exact yCount
    · simp [pairKeep]
  · intro value member
    exact pairProjection_member member

private theorem s5SimplePrecedes_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.SimplePrecedes word x y ↔
      pairProjection word.toList x y = [x, y] := by
  rw [S5_793Invariant.SimplePrecedes]
  have scanEq :
      S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty
          (pairProjection word.toList x y) := by
    rw [show S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty word.toList by rfl]
    exact orderScanFrom_pairProjection x y word.toList .empty
  rw [scanEq]
  rcases pairProjection_shape_one_one
      word.toList different xCount yCount with shape | shape
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]

private theorem pairProjection_comm
    (letters : List Nat) (x y : Nat) :
    pairProjection letters x y = pairProjection letters y x := by
  apply List.filter_congr
  intro value _
  simp [pairKeep, Bool.or_comm]

private theorem pairProjection_reverse
    (letters : List Nat) (x y : Nat) :
    pairProjection letters.reverse x y =
      (pairProjection letters x y).reverse := by
  simp [pairProjection, List.filter_reverse]

private theorem simplePrecedes_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    SimpleSequenceFirstGap.SimplePrecedes word x y ↔
      pairProjection word.toList x y = [x, y] := by
  have reversedYCount : word.reverse.toList.count y = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using yCount
  have reversedXCount : word.reverse.toList.count x = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using xCount
  rw [SimpleSequenceFirstGap.SimplePrecedes,
    s5SimplePrecedes_iff_pairProjection word.reverse
      (Ne.symm different) reversedYCount reversedXCount]
  rw [Word.toList_reverse, pairProjection_reverse,
    pairProjection_comm word.toList y x]
  constructor
  · intro equality
    have reversed := congrArg List.reverse equality
    simpa using reversed
  · intro equality
    rw [equality]
    simp

private theorem pairProjection_of_y_absent
    {x y : Nat} (different : x ≠ y) :
    forall letters : List Nat,
      y ∉ letters →
        pairProjection letters x y =
          List.replicate (letters.count x) x
  | [], _ => by simp [pairProjection]
  | letter :: rest, absent => by
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      by_cases isX : letter = x
      · subst letter
        simp [pairProjection, pairKeep]
        change
          x :: pairProjection rest x y =
            List.replicate (Nat.succ (rest.count x)) x
        rw [pairProjection_of_y_absent different rest restAbsent]
        rw [List.replicate_succ]
      · have isY : letter ≠ y := by
          intro equality
          subst letter
          exact absent (List.Mem.head rest)
        simp [pairProjection, pairKeep, isX, isY]
        exact pairProjection_of_y_absent different rest restAbsent

private theorem pairProjection_at_simple_split
    (word : Word Nat) {x y : Nat} {front rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = front ++ y :: rest)
    (yCount : word.toList.count y = 1) :
    pairProjection word.toList x y =
      List.replicate (front.count x) x ++
        y :: List.replicate (rest.count x) x := by
  have yAbsentPrefix : y ∉ front := by
    intro member
    have positive : 1 ≤ front.count y :=
      List.one_le_count_iff.mpr member
    rw [shape, List.count_append, List.count_cons_self] at yCount
    omega
  have yAbsentRest : y ∉ rest := by
    intro member
    have positive : 1 ≤ rest.count y :=
      List.one_le_count_iff.mpr member
    rw [shape, List.count_append, List.count_cons_self] at yCount
    omega
  rw [shape]
  simp only [pairProjection, List.filter_append, List.filter_cons]
  have yKept : pairKeep x y y = true := by
    simp [pairKeep]
  rw [if_pos yKept]
  change
    pairProjection front x y ++
        y :: pairProjection rest x y = _
  rw [pairProjection_of_y_absent different front yAbsentPrefix,
    pairProjection_of_y_absent different rest yAbsentRest]

private theorem simplePrecedes_iff_prefix_count_one
    (word : Word Nat) {x y : Nat} {front rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = front ++ y :: rest)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    SimpleSequenceFirstGap.SimplePrecedes word x y ↔
      front.count x = 1 := by
  rw [simplePrecedes_iff_pairProjection
    word different xCount yCount]
  rw [pairProjection_at_simple_split
    word different shape yCount]
  have splitCount : front.count x + rest.count x = 1 := by
    rw [shape, List.count_append,
      List.count_cons_of_ne (Ne.symm different)] at xCount
    simpa using xCount
  constructor
  · intro projection
    by_cases prefixOne : front.count x = 1
    · exact prefixOne
    · have prefixZero : front.count x = 0 := by omega
      have restOne : rest.count x = 1 := by omega
      simp [prefixZero, restOne, different,
        Ne.symm different] at projection
  · intro prefixOne
    have restZero : rest.count x = 0 := by omega
    simp [prefixOne, restZero]

private theorem simplePrecedes_iff_mem_prefix
    (word : Word Nat) {x y : Nat}
    (xSimple : word.toList.count x = 1)
    (ySimple : word.toList.count y = 1) :
    SimpleSequenceFirstGap.SimplePrecedes word x y ↔
      x ∈ S5_254.simplePrefixBefore y word.toList := by
  have yMember : y ∈ word.toList :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨front, rest, shape⟩ := List.mem_iff_append.mp yMember
  have prefixEq :
      S5_254.simplePrefixBefore y word.toList = front :=
    S5_254.simplePrefixBefore_eq_of_split
      (by simpa [S5_254.GloballySimple] using ySimple)
      front rest shape
  by_cases different : x ≠ y
  · rw [prefixEq, ← List.count_pos_iff]
    have bound : front.count x ≤ 1 := by
      rw [shape, List.count_append, List.count_cons] at xSimple
      omega
    rw [simplePrecedes_iff_prefix_count_one
      word different shape xSimple ySimple]
    omega
  · have equality : x = y := by
      exact Classical.byContradiction different
    subst y
    have prefixAbsent : x ∉ front := by
      intro member
      have positive : 0 < front.count x :=
        List.count_pos_iff.mpr member
      rw [shape, List.count_append, List.count_cons_self] at xSimple
      omega
    rw [prefixEq]
    simp [SimpleSequenceFirstGap.SimplePrecedes,
      S5_793Invariant.SimplePrecedes, prefixAbsent]

private theorem orderScanFrom_replicate_fixed
    (x y : Nat) (state : S5_793Invariant.OrderGapState)
    (fixed :
      S5_793Invariant.orderStep state .x = state) :
    forall count : Nat,
      orderScanFrom x y state (List.replicate count x) = state
  | 0 => rfl
  | count + 1 => by
      simp only [List.replicate_succ, orderScanFrom, List.foldl_cons]
      rw [show S5_793Invariant.orderSymbol x y x = .x by
        simp [S5_793Invariant.orderSymbol]]
      rw [fixed]
      exact orderScanFrom_replicate_fixed x y state fixed count

private theorem orderScanFrom_append
    (x y : Nat) (state : S5_793Invariant.OrderGapState)
    (left right : List Nat) :
    orderScanFrom x y state (left ++ right) =
      orderScanFrom x y (orderScanFrom x y state left) right := by
  simp [orderScanFrom, List.foldl_append]

private theorem orderScanFrom_empty_replicate_twoPlus
    {x y : Nat} (different : x ≠ y) (count : Nat) :
    orderScanFrom x y .empty (List.replicate (count + 2) x) =
      .onlyXMany := by
  have fixed :=
    orderScanFrom_replicate_fixed x y
      S5_793Invariant.OrderGapState.onlyXMany (by rfl) count
  simpa [orderScanFrom, List.replicate_succ,
    S5_793Invariant.orderSymbol, S5_793Invariant.orderStep,
    different, Ne.symm different] using fixed

private theorem orderScanFrom_onlyYOne_replicate_twoPlus
    {x y : Nat} (different : x ≠ y) (count : Nat) :
    orderScanFrom x y .onlyYOne
        (List.replicate (count + 2) x) =
      .xManyYOneAfterYFirst := by
  have fixed :=
    orderScanFrom_replicate_fixed x y
      S5_793Invariant.OrderGapState.xManyYOneAfterYFirst (by rfl) count
  simpa [orderScanFrom, List.replicate_succ,
    S5_793Invariant.orderSymbol, S5_793Invariant.orderStep,
    different, Ne.symm different] using fixed

private theorem orderScanFrom_simpleXY_replicate_onePlus
    {x y : Nat} (different : x ≠ y) (count : Nat) :
    orderScanFrom x y .simpleXY
        (List.replicate (count + 1) x) =
      .xManyYOneAfterXFirst := by
  have fixed :=
    orderScanFrom_replicate_fixed x y
      S5_793Invariant.OrderGapState.xManyYOneAfterXFirst (by rfl) count
  simpa [orderScanFrom, List.replicate_succ,
    S5_793Invariant.orderSymbol, S5_793Invariant.orderStep,
    different, Ne.symm different] using fixed

private theorem orderScanFrom_before_replicate_onePlus
    {x y : Nat} (different : x ≠ y) (count : Nat) :
    orderScanFrom x y .xManyYOneBefore
        (List.replicate (count + 1) x) =
      .xManyYOneAfterXFirst := by
  have fixed :=
    orderScanFrom_replicate_fixed x y
      S5_793Invariant.OrderGapState.xManyYOneAfterXFirst (by rfl) count
  simpa [orderScanFrom, List.replicate_succ,
    S5_793Invariant.orderSymbol, S5_793Invariant.orderStep,
    different, Ne.symm different] using fixed

private theorem orderScan_x_y_x_eq_before_iff
    {x y : Nat} (different : x ≠ y) (before after : Nat) :
    orderScanFrom x y .empty
        (List.replicate before x ++
          y :: List.replicate after x) =
        .xManyYOneBefore ↔
      2 ≤ before ∧ after = 0 := by
  rcases before with _ | before
  · rcases after with _ | after
    · simp [orderScanFrom, S5_793Invariant.orderSymbol,
        S5_793Invariant.orderStep, different, Ne.symm different]
    · rcases after with _ | after
      · simp [orderScanFrom, S5_793Invariant.orderSymbol,
          S5_793Invariant.orderStep, different, Ne.symm different]
      · rw [show
          orderScanFrom x y .empty
              (List.replicate 0 x ++
                y :: List.replicate (after + 1 + 1) x) =
            orderScanFrom x y .onlyYOne
              (List.replicate (after + 1 + 1) x) by
            simp [orderScanFrom, S5_793Invariant.orderSymbol,
              S5_793Invariant.orderStep, different,
              Ne.symm different]]
        rw [show after + 1 + 1 = after + 2 by omega,
          orderScanFrom_onlyYOne_replicate_twoPlus different after]
        simp
  · rcases before with _ | before
    · rcases after with _ | after
      · simp [orderScanFrom, S5_793Invariant.orderSymbol,
          S5_793Invariant.orderStep, different, Ne.symm different]
      · rw [show
          orderScanFrom x y .empty
              (List.replicate 1 x ++
                y :: List.replicate (after + 1) x) =
            orderScanFrom x y .simpleXY
              (List.replicate (after + 1) x) by
            simp [orderScanFrom, S5_793Invariant.orderSymbol,
              S5_793Invariant.orderStep, different,
              Ne.symm different]]
        rw [orderScanFrom_simpleXY_replicate_onePlus
          different after]
        simp
    · rw [orderScanFrom_append,
        orderScanFrom_empty_replicate_twoPlus different before]
      rcases after with _ | after
      · simp [orderScanFrom, S5_793Invariant.orderSymbol,
          S5_793Invariant.orderStep, different, Ne.symm different]
      · rw [show
          orderScanFrom x y .onlyXMany
              (y :: List.replicate (after + 1) x) =
            orderScanFrom x y .xManyYOneBefore
              (List.replicate (after + 1) x) by
            simp [orderScanFrom, S5_793Invariant.orderSymbol,
              S5_793Invariant.orderStep, different,
              Ne.symm different]]
        rw [orderScanFrom_before_replicate_onePlus
          different after]
        simp

private theorem simpleBeforeMultipleFirst_iff_prefix_absent
    (word : Word Nat) {simple multiple : Nat}
    {front rest : List Nat}
    (shape : word.toList = front ++ simple :: rest)
    (simpleCount : word.toList.count simple = 1)
    (multipleCount : 2 ≤ word.toList.count multiple) :
    SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
        word simple multiple ↔
      multiple ∉ front := by
  have different : multiple ≠ simple := by
    intro equality
    subst simple
    omega
  have projectionShape :=
    pairProjection_at_simple_split word different shape simpleCount
  have totalCount :
      front.count multiple + rest.count multiple =
        word.toList.count multiple := by
    rw [shape, List.count_append,
      List.count_cons_of_ne (Ne.symm different)]
  have scanEq :
      S5_793Invariant.orderGapScan word.reverse multiple simple =
        orderScanFrom multiple simple .empty
          (List.replicate (rest.count multiple) multiple ++
            simple :: List.replicate (front.count multiple) multiple) := by
    calc
      S5_793Invariant.orderGapScan word.reverse multiple simple =
          orderScanFrom multiple simple .empty
            word.reverse.toList := rfl
      _ = orderScanFrom multiple simple .empty
            (pairProjection word.reverse.toList multiple simple) :=
        orderScanFrom_pairProjection multiple simple
          word.reverse.toList .empty
      _ = orderScanFrom multiple simple .empty
            (List.replicate (rest.count multiple) multiple ++
              simple ::
                List.replicate (front.count multiple) multiple) := by
        rw [Word.toList_reverse, pairProjection_reverse,
          projectionShape]
        simp [List.reverse_append]
  rw [SimpleSequenceFirstGap.SimpleBeforeMultipleFirst,
    S5_793Invariant.MultipleLastBeforeSimple, scanEq]
  rw [orderScan_x_y_x_eq_before_iff different]
  rw [← List.count_eq_zero]
  constructor
  · rintro ⟨_, _, prefixZero⟩
    exact prefixZero
  · intro prefixZero
    refine ⟨different, ?_, prefixZero⟩
    omega

/-! ## Ordered simple separators -/

private theorem mem_of_mem_simplePrefixBefore
    (separator tested : Nat) :
    forall {letters : List Nat},
      tested ∈ S5_254.simplePrefixBefore separator letters →
        tested ∈ letters
  | [], member => by
      simp [S5_254.simplePrefixBefore] at member
  | letter :: letters, member => by
      by_cases equal : letter = separator
      · simp [S5_254.simplePrefixBefore, equal] at member
      · simp only [S5_254.simplePrefixBefore, equal, if_false,
          List.mem_cons] at member |-
        rcases member with testedEqual | member
        · exact Or.inl testedEqual
        · exact Or.inr <|
            mem_of_mem_simplePrefixBefore separator tested member

private theorem simplePrefixBefore_filter
    (separator : Nat) (keep : Nat → Bool)
    (separatorKept : keep separator = true) :
    forall letters : List Nat,
      S5_254.simplePrefixBefore separator (letters.filter keep) =
        (S5_254.simplePrefixBefore separator letters).filter keep
  | [] => by simp [S5_254.simplePrefixBefore]
  | letter :: letters => by
      by_cases equal : letter = separator
      · subst letter
        simp [S5_254.simplePrefixBefore, separatorKept]
      · by_cases kept : keep letter = true
        · simp [S5_254.simplePrefixBefore, equal, kept,
            simplePrefixBefore_filter separator keep
              separatorKept letters]
        · simp [S5_254.simplePrefixBefore, equal, kept,
            simplePrefixBefore_filter separator keep
              separatorKept letters]

private theorem sequencePrefixMembership_iff
    (word : Word Nat) (separator tested : Nat)
    (separatorSimple : S5_254.GloballySimple word separator) :
    tested ∈ S5_254.simplePrefixBefore separator
        (S5_254.simpleSeparatorSequence word) ↔
      S5_254.GloballySimple word tested ∧
        tested ∈ S5_254.simplePrefixBefore separator word.toList := by
  let keep :=
    fun letter => decide (word.toList.count letter = 1)
  have separatorKept : keep separator = true := by
    simp [keep, S5_254.GloballySimple] at separatorSimple |-
    exact separatorSimple
  rw [S5_254.simpleSeparatorSequence,
    simplePrefixBefore_filter separator keep separatorKept]
  simp [keep, S5_254.GloballySimple, and_comm]

private theorem list_eq_of_same_mem_same_prefix :
    forall (left right : List Nat),
      left.Nodup → right.Nodup →
      (forall tested, tested ∈ left ↔ tested ∈ right) →
      (forall marker tested,
        marker ∈ left → marker ∈ right →
        (tested ∈ S5_254.simplePrefixBefore marker left ↔
          tested ∈ S5_254.simplePrefixBefore marker right)) →
      left = right
  | [], right, _, _, sameMem, _ => by
      symm
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro tested member
      exact List.not_mem_nil ((sameMem tested).mpr member)
  | head :: tail, right, leftNodup, rightNodup,
      sameMem, samePrefix => by
      have headRight : head ∈ right :=
        (sameMem head).mp (by simp)
      obtain ⟨before, after, rightShape⟩ :=
        List.mem_iff_append.mp headRight
      have headNotBefore : head ∉ before := by
        intro member
        have beforePositive : 0 < before.count head :=
          List.count_pos_iff.mpr member
        have rightCount : right.count head = 1 := by
          rw [rightNodup.count]
          simp [headRight]
        rw [rightShape, List.count_append,
          List.count_cons_self] at rightCount
        omega
      have beforeEmpty : before = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro tested member
        have rightPrefixMember :
            tested ∈ S5_254.simplePrefixBefore head right := by
          rw [rightShape,
            S5_254.simplePrefixBefore_split head before after
              headNotBefore]
          exact member
        have leftPrefixMember :
            tested ∈ S5_254.simplePrefixBefore head (head :: tail) :=
          (samePrefix head tested (by simp) headRight).mpr
            rightPrefixMember
        simpa [S5_254.simplePrefixBefore] using leftPrefixMember
      have rightCons : right = head :: after := by
        simpa [beforeEmpty] using rightShape
      rw [rightCons] at rightNodup sameMem samePrefix |-
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp leftNodup).1
      have headNotAfter : head ∉ after :=
        (List.nodup_cons.mp rightNodup).1
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have afterNodup := (List.nodup_cons.mp rightNodup).2
      have tailMem :
          forall tested, tested ∈ tail ↔ tested ∈ after := by
        intro tested
        constructor
        · intro member
          have full :=
            (sameMem tested).mp (List.Mem.tail head member)
          exact (List.mem_cons.mp full).resolve_left (by
            intro equality
            subst tested
            exact headNotTail member)
        · intro member
          have full :=
            (sameMem tested).mpr (List.Mem.tail head member)
          exact (List.mem_cons.mp full).resolve_left (by
            intro equality
            subst tested
            exact headNotAfter member)
      have tailPrefix : forall marker tested,
          marker ∈ tail → marker ∈ after →
          (tested ∈ S5_254.simplePrefixBefore marker tail ↔
            tested ∈ S5_254.simplePrefixBefore marker after) := by
        intro marker tested markerLeft markerRight
        have markerNeHead : marker ≠ head := by
          intro equality
          subst marker
          exact headNotTail markerLeft
        have full :=
          samePrefix marker tested
            (List.Mem.tail head markerLeft)
            (List.Mem.tail head markerRight)
        by_cases testedEq : tested = head
        · subst tested
          constructor
          · intro member
            exact (headNotTail
              (mem_of_mem_simplePrefixBefore marker head member)).elim
          · intro member
            exact (headNotAfter
              (mem_of_mem_simplePrefixBefore marker head member)).elim
        · simpa [S5_254.simplePrefixBefore, Ne.symm markerNeHead,
            testedEq, Ne.symm testedEq] using full
      rw [list_eq_of_same_mem_same_prefix
        tail after tailNodup afterNodup tailMem tailPrefix]

theorem simpleSeparatorSequence_eq
    {left right : Word Nat}
    (same : SimpleSequenceFirstGap.SameSignature left right) :
    S5_254.simpleSeparatorSequence left =
      S5_254.simpleSeparatorSequence right := by
  apply list_eq_of_same_mem_same_prefix
    (S5_254.simpleSeparatorSequence left)
    (S5_254.simpleSeparatorSequence right)
    (S5_254.simpleSeparatorSequence_nodup left)
    (S5_254.simpleSeparatorSequence_nodup right)
  · intro tested
    rw [S5_254.simpleSeparatorSequence_mem_iff,
      S5_254.simpleSeparatorSequence_mem_iff]
    simpa [S5_254.GloballySimple, S5_107.SimpleIn] using
      same.simple tested
  · intro marker tested markerLeft markerRight
    have leftMarkerSimple : left.toList.count marker = 1 := by
      simpa [S5_254.GloballySimple] using
        (S5_254.simpleSeparatorSequence_mem_iff left marker).mp
          markerLeft
    have rightMarkerSimple : right.toList.count marker = 1 := by
      simpa [S5_254.GloballySimple] using
        (S5_254.simpleSeparatorSequence_mem_iff right marker).mp
          markerRight
    rw [sequencePrefixMembership_iff left marker tested
          (by simpa [S5_254.GloballySimple] using leftMarkerSimple),
      sequencePrefixMembership_iff right marker tested
          (by simpa [S5_254.GloballySimple] using rightMarkerSimple)]
    have testedSimple := same.simple tested
    constructor
    · rintro ⟨leftTestedSimple, leftBefore⟩
      have leftCount : left.toList.count tested = 1 := by
        simpa [S5_254.GloballySimple] using leftTestedSimple
      have rightCount : right.toList.count tested = 1 := by
        exact (testedSimple.mp leftCount)
      have leftOrder :=
        (simplePrecedes_iff_mem_prefix left
          leftCount leftMarkerSimple).mpr leftBefore
      have rightOrder :=
        (same.simpleSequence tested marker).mp leftOrder
      exact
        ⟨by simpa [S5_254.GloballySimple] using rightCount,
          (simplePrecedes_iff_mem_prefix right
            rightCount rightMarkerSimple).mp rightOrder⟩
    · rintro ⟨rightTestedSimple, rightBefore⟩
      have rightCount : right.toList.count tested = 1 := by
        simpa [S5_254.GloballySimple] using rightTestedSimple
      have leftCount : left.toList.count tested = 1 := by
        exact (testedSimple.mpr rightCount)
      have rightOrder :=
        (simplePrecedes_iff_mem_prefix right
          rightCount rightMarkerSimple).mpr rightBefore
      have leftOrder :=
        (same.simpleSequence tested marker).mpr rightOrder
      exact
        ⟨by simpa [S5_254.GloballySimple] using leftCount,
          (simplePrecedes_iff_mem_prefix left
            leftCount leftMarkerSimple).mp leftOrder⟩

/-! ## Canonical-bank support -/

private theorem sortedDistinctLetters_nodup (letters : List Nat) :
    (sortedDistinctLetters letters).Nodup :=
  (sortedDistinctLetters_perm letters).nodup_iff.mpr
    (S5_107.distinctLetters_nodup letters)

private theorem sortedDistinctLetters_pairwise (letters : List Nat) :
    (sortedDistinctLetters letters).Pairwise (fun x y => x ≤ y) := by
  have transitive :
      forall left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      forall left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted :=
    List.pairwise_mergeSort transitive total
      (S5_107.distinctLetters letters)
  exact sorted.imp fun relation => of_decide_eq_true relation

theorem sortedDistinctLetters_eq_of_support
    (left right : List Nat)
    (support : forall letter, letter ∈ left ↔ letter ∈ right) :
    sortedDistinctLetters left = sortedDistinctLetters right := by
  have permutation :
      (sortedDistinctLetters left).Perm
        (sortedDistinctLetters right) := by
    rw [List.perm_iff_count]
    intro tested
    rw [(sortedDistinctLetters_nodup left).count,
      (sortedDistinctLetters_nodup right).count]
    simp only [sortedDistinctLetters_mem_iff, support tested]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (sortedDistinctLetters_pairwise left)
    (sortedDistinctLetters_pairwise right)
    permutation

private def ProcessedSupport
    (whole front seen : List Nat) : Prop :=
  forall letter,
    letter ∈ seen ↔
      2 ≤ whole.count letter ∧ letter ∈ front

private theorem processedSupport_empty (whole : List Nat) :
    ProcessedSupport whole [] [] := by
  intro letter
  simp [ProcessedSupport]

private theorem nextBankLabels_member_iff
    (seen gap : List Nat) (letter : Nat) :
    letter ∈ nextBankLabels seen gap ↔
      letter ∈ seen ∨ letter ∈ gap := by
  simp [nextBankLabels, sortedDistinctLetters_mem_iff]

private theorem processedSupport_extend
    {whole front seen gap : List Nat} {separator : Nat}
    (processed : ProcessedSupport whole front seen)
    (gapRepeated :
      forall letter, letter ∈ gap → 2 ≤ whole.count letter)
    (separatorSimple : whole.count separator = 1) :
    ProcessedSupport whole
      (front ++ gap ++ [separator])
      (nextBankLabels seen gap) := by
  intro letter
  rw [nextBankLabels_member_iff]
  constructor
  · intro member
    rcases member with old | inGap
    · have data := (processed letter).mp old
      exact ⟨data.1, by simp [data.2]⟩
    · exact ⟨gapRepeated letter inGap, by simp [inGap]⟩
  · rintro ⟨multiple, member⟩
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (inFront | inGap) | atSeparator
    · exact Or.inl ((processed letter).mpr ⟨multiple, inFront⟩)
    · exact Or.inr inGap
    · subst letter
      omega

private theorem processedSupport_extend_empty
    {whole front seen : List Nat} {separator : Nat}
    (processed : ProcessedSupport whole front seen)
    (separatorSimple : whole.count separator = 1) :
    ProcessedSupport whole (front ++ [separator]) seen := by
  intro letter
  rw [processed letter]
  constructor
  · rintro ⟨multiple, member⟩
    exact ⟨multiple, by simp [member]⟩
  · rintro ⟨multiple, member⟩
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with inPrefix | atSeparator
    · exact ⟨multiple, inPrefix⟩
    · subst letter
      omega

private theorem nextBankLabels_eq_before_separator
    {left right : Word Nat}
    (same : SimpleSequenceFirstGap.SameSignature left right)
    {leftPrefix rightPrefix seen leftGap rightGap
      leftRest rightRest : List Nat} {separator : Nat}
    (leftProcessed :
      ProcessedSupport left.toList leftPrefix seen)
    (rightProcessed :
      ProcessedSupport right.toList rightPrefix seen)
    (leftRepeated :
      forall letter, letter ∈ leftGap →
        2 ≤ left.toList.count letter)
    (rightRepeated :
      forall letter, letter ∈ rightGap →
        2 ≤ right.toList.count letter)
    (leftShape :
      left.toList = leftPrefix ++ leftGap ++ separator :: leftRest)
    (rightShape :
      right.toList = rightPrefix ++ rightGap ++ separator :: rightRest)
    (leftSimple : left.toList.count separator = 1)
    (rightSimple : right.toList.count separator = 1) :
    nextBankLabels seen leftGap =
      nextBankLabels seen rightGap := by
  apply sortedDistinctLetters_eq_of_support
  intro letter
  rw [List.mem_append, List.mem_append,
    sortedDistinctLetters_mem_iff,
    sortedDistinctLetters_mem_iff]
  have leftMember :
      letter ∈ seen ∨ letter ∈ leftGap ↔
        2 ≤ left.toList.count letter ∧
          letter ∈ leftPrefix ++ leftGap := by
    constructor
    · rintro (old | inGap)
      · have data := (leftProcessed letter).mp old
        exact ⟨data.1, by simp [data.2]⟩
      · exact ⟨leftRepeated letter inGap, by simp [inGap]⟩
    · rintro ⟨multiple, member⟩
      rcases List.mem_append.mp member with inPrefix | inGap
      · exact Or.inl ((leftProcessed letter).mpr
          ⟨multiple, inPrefix⟩)
      · exact Or.inr inGap
  have rightMember :
      letter ∈ seen ∨ letter ∈ rightGap ↔
        2 ≤ right.toList.count letter ∧
          letter ∈ rightPrefix ++ rightGap := by
    constructor
    · rintro (old | inGap)
      · have data := (rightProcessed letter).mp old
        exact ⟨data.1, by simp [data.2]⟩
      · exact ⟨rightRepeated letter inGap, by simp [inGap]⟩
    · rintro ⟨multiple, member⟩
      rcases List.mem_append.mp member with inPrefix | inGap
      · exact Or.inl ((rightProcessed letter).mpr
          ⟨multiple, inPrefix⟩)
      · exact Or.inr inGap
  rw [leftMember, rightMember]
  have multipleIff :
      2 ≤ left.toList.count letter ↔
        2 ≤ right.toList.count letter := by
    rw [← cappedMultiplicity_eq_two_iff left letter,
      ← cappedMultiplicity_eq_two_iff right letter,
      same.capped letter]
  constructor
  · rintro ⟨leftMultiple, leftBefore⟩
    have leftNotRelation :
        ¬ SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          left separator letter := by
      intro relation
      have absent :=
        (simpleBeforeMultipleFirst_iff_prefix_absent left
          (front := leftPrefix ++ leftGap)
          (rest := leftRest)
          (by simpa [List.append_assoc] using leftShape)
          leftSimple leftMultiple).mp relation
      exact absent leftBefore
    have rightNotRelation :
        ¬ SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          right separator letter := by
      intro relation
      exact leftNotRelation
        ((same.firstGap separator letter).mpr relation)
    have rightMultiple := multipleIff.mp leftMultiple
    have rightBefore :
        letter ∈ rightPrefix ++ rightGap := by
      apply Classical.byContradiction
      intro absent
      exact rightNotRelation
        ((simpleBeforeMultipleFirst_iff_prefix_absent right
          (front := rightPrefix ++ rightGap)
          (rest := rightRest)
          (by simpa [List.append_assoc] using rightShape)
          rightSimple rightMultiple).mpr absent)
    exact ⟨rightMultiple, rightBefore⟩
  · rintro ⟨rightMultiple, rightBefore⟩
    have rightNotRelation :
        ¬ SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          right separator letter := by
      intro relation
      have absent :=
        (simpleBeforeMultipleFirst_iff_prefix_absent right
          (front := rightPrefix ++ rightGap)
          (rest := rightRest)
          (by simpa [List.append_assoc] using rightShape)
          rightSimple rightMultiple).mp relation
      exact absent rightBefore
    have leftNotRelation :
        ¬ SimpleSequenceFirstGap.SimpleBeforeMultipleFirst
          left separator letter := by
      intro relation
      exact rightNotRelation
        ((same.firstGap separator letter).mp relation)
    have leftMultiple := multipleIff.mpr rightMultiple
    have leftBefore :
        letter ∈ leftPrefix ++ leftGap := by
      apply Classical.byContradiction
      intro absent
      exact leftNotRelation
        ((simpleBeforeMultipleFirst_iff_prefix_absent left
          (front := leftPrefix ++ leftGap)
          (rest := leftRest)
          (by simpa [List.append_assoc] using leftShape)
          leftSimple leftMultiple).mpr absent)
    exact ⟨leftMultiple, leftBefore⟩

private theorem nextBankLabels_eq_at_end
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    {leftPrefix rightPrefix seen leftGap rightGap : List Nat}
    (leftProcessed :
      ProcessedSupport left.toList leftPrefix seen)
    (rightProcessed :
      ProcessedSupport right.toList rightPrefix seen)
    (leftRepeated :
      forall letter, letter ∈ leftGap →
        2 ≤ left.toList.count letter)
    (rightRepeated :
      forall letter, letter ∈ rightGap →
        2 ≤ right.toList.count letter)
    (leftShape : left.toList = leftPrefix ++ leftGap)
    (rightShape : right.toList = rightPrefix ++ rightGap) :
    nextBankLabels seen leftGap =
      nextBankLabels seen rightGap := by
  apply sortedDistinctLetters_eq_of_support
  intro letter
  rw [List.mem_append, List.mem_append,
    sortedDistinctLetters_mem_iff,
    sortedDistinctLetters_mem_iff]
  have leftIff :
      letter ∈ seen ∨ letter ∈ leftGap ↔
        2 ≤ left.toList.count letter := by
    constructor
    · rintro (old | inGap)
      · exact ((leftProcessed letter).mp old).1
      · exact leftRepeated letter inGap
    · intro multiple
      have member : letter ∈ leftPrefix ++ leftGap :=
        leftShape.symm ▸ List.count_pos_iff.mp (by omega)
      rcases List.mem_append.mp member with inPrefix | inGap
      · exact Or.inl ((leftProcessed letter).mpr
          ⟨multiple, inPrefix⟩)
      · exact Or.inr inGap
  have rightIff :
      letter ∈ seen ∨ letter ∈ rightGap ↔
        2 ≤ right.toList.count letter := by
    constructor
    · rintro (old | inGap)
      · exact ((rightProcessed letter).mp old).1
      · exact rightRepeated letter inGap
    · intro multiple
      have member : letter ∈ rightPrefix ++ rightGap :=
        rightShape.symm ▸ List.count_pos_iff.mp (by omega)
      rcases List.mem_append.mp member with inPrefix | inGap
      · exact Or.inl ((rightProcessed letter).mpr
          ⟨multiple, inPrefix⟩)
      · exact Or.inr inGap
  rw [leftIff, rightIff]
  rw [← cappedMultiplicity_eq_two_iff left letter,
    ← cappedMultiplicity_eq_two_iff right letter,
    same.capped letter]

/-! ## Empty gaps from the adjacency signature -/

private theorem simpleInitial_iff_prefix_nil
    (word : Word Nat) (separator : Nat)
    (before after : List Nat)
    (shape : word.toList = before ++ separator :: after)
    (simple : word.toList.count separator = 1) :
    S5_107.SimpleInitial word separator ↔ before = [] := by
  constructor
  · intro initial
    have scanned :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := separator)
        (by simpa [S5_254.GloballySimple] using simple)
        before after shape
    have emptyScan :
        S5_254.simplePrefixBefore separator word.toList = [] := by
      cases word with
      | mk head tail =>
          simpa [Word.toList, S5_254.simplePrefixBefore]
            using initial.2
    rw [emptyScan] at scanned
    exact scanned.symm
  · intro empty
    subst before
    refine ⟨by simpa [S5_107.SimpleIn] using simple, ?_⟩
    cases word with
    | mk head tail =>
        simp only [Word.toList, List.nil_append] at shape
        injection shape

private theorem reverseAux_head_eq_getLastD (head : Nat) :
    forall tail : List Nat,
      (Word.reverseAux head tail).head = tail.getLastD head
  | [] => rfl
  | next :: rest => by
      change
        (Word.reverseAux next rest).head =
          (next :: rest).getLastD head
      rw [List.getLastD_cons]
      exact reverseAux_head_eq_getLastD next rest

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  cases word with
  | mk head tail => exact reverseAux_head_eq_getLastD head tail

private theorem simpleInitial_reverse_iff_simpleFinal
    (word : Word Nat) (separator : Nat) :
    S5_107.SimpleInitial word.reverse separator ↔
      S5_107.SimpleFinal word separator := by
  simp [S5_107.SimpleInitial, S5_107.SimpleFinal,
    S5_107.SimpleIn, reverse_head_eq_final]

private theorem simpleFinal_iff_suffix_nil
    (word : Word Nat) (separator : Nat)
    (before after : List Nat)
    (shape : word.toList = before ++ separator :: after)
    (simple : word.toList.count separator = 1) :
    S5_107.SimpleFinal word separator ↔ after = [] := by
  have reversedShape :
      word.reverse.toList =
        after.reverse ++ separator :: before.reverse := by
    rw [Word.toList_reverse, shape]
    simp [List.reverse_append]
  have reversedSimple :
      word.reverse.toList.count separator = 1 := by
    simpa using simple
  calc
    S5_107.SimpleFinal word separator ↔
        S5_107.SimpleInitial word.reverse separator :=
      (simpleInitial_reverse_iff_simpleFinal word separator).symm
    _ ↔ after.reverse = [] :=
      simpleInitial_iff_prefix_nil word.reverse separator
        after.reverse before.reverse reversedShape reversedSimple
    _ ↔ after = [] := by simp

private theorem adjacentPair_iff_middle_nil
    (word : Word Nat) (source target : Nat)
    (before middle after : List Nat)
    (shape :
      word.toList = before ++ source :: (middle ++ target :: after))
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    (source, target) ∈ word.adjacentPairs ↔ middle = [] := by
  constructor
  · intro adjacent
    obtain ⟨adjacentBefore, adjacentAfter, adjacentShape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word).mp adjacent
    have sourcePrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := source)
        (by simpa [S5_254.GloballySimple] using sourceSimple)
        before (middle ++ target :: after) shape
    have adjacentSourcePrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := source)
        (by simpa [S5_254.GloballySimple] using sourceSimple)
        adjacentBefore (target :: adjacentAfter) adjacentShape
    have beforeEq : before = adjacentBefore :=
      sourcePrefix.symm.trans adjacentSourcePrefix
    have targetShape :
        word.toList =
          (before ++ source :: middle) ++ target :: after := by
      simpa [List.append_assoc] using shape
    have adjacentTargetShape :
        word.toList =
          (adjacentBefore ++ [source]) ++ target :: adjacentAfter := by
      simpa [List.append_assoc] using adjacentShape
    have targetPrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := target)
        (by simpa [S5_254.GloballySimple] using targetSimple)
        (before ++ source :: middle) after targetShape
    have adjacentTargetPrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := target)
        (by simpa [S5_254.GloballySimple] using targetSimple)
        (adjacentBefore ++ [source]) adjacentAfter
        adjacentTargetShape
    have prefixEq :
        before ++ source :: middle =
          adjacentBefore ++ [source] :=
      targetPrefix.symm.trans adjacentTargetPrefix
    rw [← beforeEq] at prefixEq
    have tailEq : source :: middle = [source] :=
      List.append_cancel_left prefixEq
    simpa using tailEq
  · intro empty
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word).mpr
    exact ⟨before, after, by simpa [empty] using shape⟩

/-! ## Alignment of the cumulative normal forms -/

private theorem renderCumulative_eq_after
    {left right : Word Nat}
    (first : SimpleSequenceFirstGap.SameSignature left right)
    (adjacency : S5_107.SameSimpleAdjacencySignature left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal seen leftBefore rightBefore : List Nat}
    {previous : Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftPreviousSimple : left.toList.count previous = 1)
    (rightPreviousSimple : right.toList.count previous = 1)
    (leftShape :
      left.toList = leftBefore ++ previous :: leftSource)
    (rightShape :
      right.toList = rightBefore ++ previous :: rightSource)
    (leftProcessed :
      ProcessedSupport left.toList
        (leftBefore ++ [previous]) seen)
    (rightProcessed :
      ProcessedSupport right.toList
        (rightBefore ++ [previous]) seen)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderCumulativeDecomposition seen leftSegments leftFinal =
      renderCumulativeDecomposition seen rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal previous
      leftBefore rightBefore seen with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          have leftFinalIff :=
            simpleFinal_iff_suffix_nil left previous
              leftBefore leftGap leftShape leftPreviousSimple
          have rightFinalIff :=
            simpleFinal_iff_suffix_nil right previous
              rightBefore rightSource rightShape rightPreviousSimple
          have emptyIff : leftGap = [] ↔ rightSource = [] := by
            calc
              leftGap = [] ↔ S5_107.SimpleFinal left previous :=
                leftFinalIff.symm
              _ ↔ S5_107.SimpleFinal right previous :=
                adjacency.final previous
              _ ↔ rightSource = [] := rightFinalIff
          by_cases leftEmpty : leftGap = []
          · have rightEmpty := emptyIff.mp leftEmpty
            simp [renderCumulativeDecomposition,
              leftEmpty, rightEmpty]
          · have rightNonempty : rightSource ≠ [] := by
              intro rightEmpty
              exact leftEmpty (emptyIff.mpr rightEmpty)
            have bankEq :=
              nextBankLabels_eq_at_end adjacency
                leftProcessed rightProcessed
                leftRepeated rightRepeated
                (by simpa [List.append_assoc] using leftShape)
                (by simpa [List.append_assoc] using rightShape)
            simp [renderCumulativeDecomposition,
              leftEmpty, rightNonempty, bankEq]
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail leftInduction =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have leftPair :
              S5_107.SimpleAdjacent left previous leftSeparator ↔
                leftGap = [] := by
            simpa [S5_107.SimpleAdjacent, S5_107.SimpleIn,
              leftPreviousSimple, leftSeparatorSimple] using
              adjacentPair_iff_middle_nil left previous leftSeparator
                leftBefore leftGap leftRemainder
                (by simpa [List.append_assoc] using leftShape)
                leftPreviousSimple leftSeparatorSimple
          have rightPair :
              S5_107.SimpleAdjacent right previous leftSeparator ↔
                rightGap = [] := by
            simpa [S5_107.SimpleAdjacent, S5_107.SimpleIn,
              rightPreviousSimple, rightSeparatorSimple] using
              adjacentPair_iff_middle_nil right previous leftSeparator
                rightBefore rightGap rightRemainder
                (by simpa [List.append_assoc] using rightShape)
                rightPreviousSimple rightSeparatorSimple
          have emptyIff : leftGap = [] ↔ rightGap = [] := by
            calc
              leftGap = [] ↔
                  S5_107.SimpleAdjacent left previous leftSeparator :=
                leftPair.symm
              _ ↔
                  S5_107.SimpleAdjacent right previous leftSeparator :=
                adjacency.adjacent previous leftSeparator
              _ ↔ rightGap = [] := rightPair
          by_cases leftEmpty : leftGap = []
          · have rightEmpty := emptyIff.mp leftEmpty
            subst leftGap
            subst rightGap
            have leftNextProcessed :=
              processedSupport_extend_empty
                leftProcessed leftSeparatorSimple
            have rightNextProcessed :=
              processedSupport_extend_empty
                rightProcessed rightSeparatorSimple
            have leftTailShape :
                left.toList =
                  (leftBefore ++ [previous]) ++
                    leftSeparator :: leftRemainder := by
              simpa [List.append_assoc] using leftShape
            have rightTailShape :
                right.toList =
                  (rightBefore ++ [previous]) ++
                    leftSeparator :: rightRemainder := by
              simpa [List.append_assoc] using rightShape
            have tailEq :=
              leftInduction rightTail
                leftSeparatorSimple rightSeparatorSimple
                leftTailShape rightTailShape
                leftNextProcessed rightNextProcessed separatorTailEq
            simpa [renderCumulativeDecomposition, tailEq]
          · have rightNonempty : rightGap ≠ [] := by
              intro rightEmpty
              exact leftEmpty (emptyIff.mpr rightEmpty)
            have bankEq :=
              nextBankLabels_eq_before_separator first
                leftProcessed rightProcessed
                leftRepeated rightRepeated
                (by simpa [List.append_assoc] using leftShape)
                (by simpa [List.append_assoc] using rightShape)
                leftSeparatorSimple rightSeparatorSimple
            let next := nextBankLabels seen leftGap
            have rightNext :
                nextBankLabels seen rightGap = next := bankEq.symm
            have leftNextProcessed :
                ProcessedSupport left.toList
                  ((leftBefore ++ [previous]) ++ leftGap ++
                    [leftSeparator]) next :=
              processedSupport_extend leftProcessed
                leftRepeated leftSeparatorSimple
            have rightNextProcessed :
                ProcessedSupport right.toList
                  ((rightBefore ++ [previous]) ++ rightGap ++
                    [leftSeparator]) next := by
              rw [← rightNext]
              exact processedSupport_extend rightProcessed
                rightRepeated rightSeparatorSimple
            have leftTailShape :
                left.toList =
                  (leftBefore ++ previous :: leftGap) ++
                    leftSeparator :: leftRemainder := by
              simpa [List.append_assoc] using leftShape
            have rightTailShape :
                right.toList =
                  (rightBefore ++ previous :: rightGap) ++
                    leftSeparator :: rightRemainder := by
              simpa [List.append_assoc] using rightShape
            have tailEq :=
              leftInduction rightTail
                leftSeparatorSimple rightSeparatorSimple
                leftTailShape rightTailShape
                (by simpa [next, List.append_assoc] using
                  leftNextProcessed)
                (by simpa [next, List.append_assoc] using
                  rightNextProcessed)
                separatorTailEq
            simp [renderCumulativeDecomposition, leftEmpty,
              rightNonempty]
            rw [← bankEq, tailEq]

private theorem renderCumulative_eq_from_start
    {left right : Word Nat}
    (first : SimpleSequenceFirstGap.SameSignature left right)
    (adjacency : S5_107.SameSimpleAdjacencySignature left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftShape : left.toList = leftSource)
    (rightShape : right.toList = rightSource)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderCumulativeDecomposition [] leftSegments leftFinal =
      renderCumulativeDecomposition [] rightSegments rightFinal := by
  cases leftDecomposition with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          have leftNonempty : leftSource ≠ [] := by
            intro empty
            have wholeEmpty : left.toList = [] := by
              simpa [empty] using leftShape
            cases left
            simp [Word.toList] at wholeEmpty
          have rightNonempty : rightSource ≠ [] := by
            intro empty
            have wholeEmpty : right.toList = [] := by
              simpa [empty] using rightShape
            cases right
            simp [Word.toList] at wholeEmpty
          have bankEq :=
            nextBankLabels_eq_at_end adjacency
              (processedSupport_empty left.toList)
              (processedSupport_empty right.toList)
              leftRepeated rightRepeated leftShape rightShape
          simp [renderCumulativeDecomposition,
            leftNonempty, rightNonempty, bankEq]
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have leftInitial :=
            simpleInitial_iff_prefix_nil left leftSeparator
              leftGap leftRemainder leftShape leftSeparatorSimple
          have rightInitial :=
            simpleInitial_iff_prefix_nil right leftSeparator
              rightGap rightRemainder rightShape rightSeparatorSimple
          have emptyIff : leftGap = [] ↔ rightGap = [] := by
            calc
              leftGap = [] ↔
                  S5_107.SimpleInitial left leftSeparator :=
                leftInitial.symm
              _ ↔ S5_107.SimpleInitial right leftSeparator :=
                adjacency.initial leftSeparator
              _ ↔ rightGap = [] := rightInitial
          by_cases leftEmpty : leftGap = []
          · have rightEmpty := emptyIff.mp leftEmpty
            subst leftGap
            subst rightGap
            have leftProcessed :=
              processedSupport_extend_empty
                (processedSupport_empty left.toList)
                leftSeparatorSimple
            have rightProcessed :=
              processedSupport_extend_empty
                (processedSupport_empty right.toList)
                rightSeparatorSimple
            have tailEq :=
              renderCumulative_eq_after first adjacency
                leftTail rightTail
                leftSeparatorSimple rightSeparatorSimple
                leftShape rightShape
                (by simpa using leftProcessed)
                (by simpa using rightProcessed)
                separatorTailEq
            simpa [renderCumulativeDecomposition, tailEq]
          · have rightNonempty : rightGap ≠ [] := by
              intro rightEmpty
              exact leftEmpty (emptyIff.mpr rightEmpty)
            have bankEq :=
              nextBankLabels_eq_before_separator first
                (processedSupport_empty left.toList)
                (processedSupport_empty right.toList)
                leftRepeated rightRepeated leftShape rightShape
                leftSeparatorSimple rightSeparatorSimple
            let next := nextBankLabels [] leftGap
            have rightNext :
                nextBankLabels [] rightGap = next := bankEq.symm
            have leftProcessed :
                ProcessedSupport left.toList
                  (leftGap ++ [leftSeparator]) next := by
              simpa [next] using
                processedSupport_extend
                  (processedSupport_empty left.toList)
                  leftRepeated leftSeparatorSimple
            have rightProcessed :
                ProcessedSupport right.toList
                  (rightGap ++ [leftSeparator]) next := by
              rw [← rightNext]
              simpa using
                processedSupport_extend
                  (processedSupport_empty right.toList)
                  rightRepeated rightSeparatorSimple
            have tailEq :=
              renderCumulative_eq_after first adjacency
                leftTail rightTail
                leftSeparatorSimple rightSeparatorSimple
                leftShape rightShape
                leftProcessed rightProcessed separatorTailEq
            simp [renderCumulativeDecomposition, leftEmpty,
              rightNonempty]
            rw [← bankEq, tailEq]

/-- The cumulative normal form is a function only of the first-gap and
simple-adjacency signatures. -/
theorem renderCumulative_eq_of_signatures
    {left right : Word Nat}
    (first : SimpleSequenceFirstGap.SameSignature left right)
    (adjacency : S5_107.SameSimpleAdjacencySignature left right)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal) :
    renderCumulativeDecomposition [] leftSegments leftFinal =
      renderCumulativeDecomposition [] rightSegments rightFinal := by
  have separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd =
          S5_254.simpleSeparatorSequence left := by
        simpa [S5_254.simpleSeparatorSequence] using
          leftDecomposition.separatorSequence_eq
      _ = S5_254.simpleSeparatorSequence right :=
        simpleSeparatorSequence_eq first
      _ = rightSegments.map Prod.snd := by
        simpa [S5_254.simpleSeparatorSequence] using
          rightDecomposition.separatorSequence_eq.symm
  exact renderCumulative_eq_from_start first adjacency
    leftDecomposition rightDecomposition rfl rfl separatorEq

/-- Unrestricted completeness of Lee--Zhang Condition 10. No variable bound
or finite-word search is used. -/
theorem derivesOfSignatures
    {left right : Word Nat}
    (first : SimpleSequenceFirstGap.SameSignature left right)
    (adjacency : S5_107.SameSimpleAdjacencySignature left right) :
    Derives basis left right := by
  obtain ⟨leftSegments, leftFinal, leftDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition left.toList
  obtain ⟨rightSegments, rightFinal, rightDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition right.toList
  have leftNormal :=
    listDerivesCumulativeDecomposition left.toList leftDecomposition
  have rightNormal :=
    listDerivesCumulativeDecomposition right.toList rightDecomposition
  have normalEq :=
    renderCumulative_eq_of_signatures first adjacency
      leftDecomposition rightDecomposition
  rw [normalEq] at leftNormal
  have combined : ListDerives left.toList right.toList :=
    leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord combined

/-- Generic endpoint bridge for a semigroup whose valid identities expose
the two lower-order signatures. -/
theorem basisCompleteOfSignatures
    {S : Type} (G : Semigroup S)
    (modelsG : Models G basis)
    (firstValid :
      forall identity : Identity Nat, identity.SatisfiedBy G →
        SimpleSequenceFirstGap.SameSignature
          identity.lhs identity.rhs)
    (adjacencyValid :
      forall identity : Identity Nat, identity.SatisfiedBy G →
        S5_107.SameSimpleAdjacencySignature
          identity.lhs identity.rhs) :
    BasisFor G basis := by
  refine ⟨modelsG, ?_⟩
  intro identity valid
  exact derivesOfSignatures
    (firstValid identity valid)
    (adjacencyValid identity valid)

end SemigroupBasis.CoRoots.Order6LeeZhangClass453
