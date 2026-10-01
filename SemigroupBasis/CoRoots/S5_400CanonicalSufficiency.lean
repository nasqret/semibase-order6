import SemigroupBasis.CoRoots.S5_400Canonical

namespace SemigroupBasis.CoRoots.S5_400

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives :
    List (Identity Nat) → List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives

private abbrev OrderGapState : Type :=
  SemigroupBasis.CoRoots.S5_793Invariant.OrderGapState

private inductive SimpleSeparatorDecomposition (whole : List Nat) :
    List Nat → List (List Nat × Nat) → List Nat → Prop where
  | final (gap : List Nat)
      (gapRepeated :
        ∀ letter, letter ∈ gap → 2 ≤ whole.count letter) :
      SimpleSeparatorDecomposition whole gap [] gap
  | step (gap : List Nat) (separator : Nat) (remainder : List Nat)
      (segments : List (List Nat × Nat)) (finalGap : List Nat)
      (separatorSimple : whole.count separator = 1)
      (gapRepeated :
        ∀ letter, letter ∈ gap → 2 ≤ whole.count letter)
      (tail :
        SimpleSeparatorDecomposition whole remainder segments finalGap) :
      SimpleSeparatorDecomposition
        whole (gap ++ separator :: remainder)
          ((gap, separator) :: segments) finalGap

private theorem prependRepeatedToSimpleSeparatorDecomposition
    {whole remaining : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (letter : Nat) (letterRepeated : 2 ≤ whole.count letter)
    (decomposition :
      SimpleSeparatorDecomposition whole remaining segments finalGap) :
    ∃ newSegments newFinalGap,
      SimpleSeparatorDecomposition
        whole (letter :: remaining) newSegments newFinalGap := by
  induction decomposition with
  | final gap gapRepeated =>
      refine ⟨[], letter :: gap, .final (letter :: gap) ?_⟩
      intro tested member
      rcases List.mem_cons.mp member with equal | inGap
      · subst tested
        exact letterRepeated
      · exact gapRepeated tested inGap
  | step gap separator remainder restSegments restFinal
      separatorSimple gapRepeated tail _tailInduction =>
      have extendedRepeated :
          ∀ tested, tested ∈ letter :: gap →
            2 ≤ whole.count tested := by
        intro tested member
        rcases List.mem_cons.mp member with equal | inGap
        · subst tested
          exact letterRepeated
        · exact gapRepeated tested inGap
      refine
        ⟨(letter :: gap, separator) :: restSegments, restFinal, ?_⟩
      simpa using
        SimpleSeparatorDecomposition.step
          (whole := whole) (gap := letter :: gap)
          (separator := separator) (remainder := remainder)
          (segments := restSegments) (finalGap := restFinal)
          separatorSimple extendedRepeated tail

private theorem existsSimpleSeparatorDecompositionAux
    (whole : List Nat) :
    ∀ remaining : List Nat,
      (∀ letter, letter ∈ remaining → letter ∈ whole) →
      ∃ segments finalGap,
        SimpleSeparatorDecomposition whole remaining segments finalGap
  | [], _ => by
      exact ⟨[], [], .final [] (by simp)⟩
  | head :: tail, contained => by
      have tailContained :
          ∀ letter, letter ∈ tail → letter ∈ whole := by
        intro letter member
        exact contained letter (List.mem_cons_of_mem head member)
      obtain ⟨segments, finalGap, decomposition⟩ :=
        existsSimpleSeparatorDecompositionAux whole tail tailContained
      by_cases simple : whole.count head = 1
      · refine ⟨([], head) :: segments, finalGap, ?_⟩
        simpa using
          SimpleSeparatorDecomposition.step
            (whole := whole) (gap := []) (separator := head)
            (remainder := tail) (segments := segments)
            (finalGap := finalGap) simple (by simp) decomposition
      · have headMember : head ∈ whole :=
          contained head (by simp)
        have positive : 0 < whole.count head :=
          List.count_pos_iff.mpr headMember
        have repeated : 2 ≤ whole.count head := by omega
        exact prependRepeatedToSimpleSeparatorDecomposition
          head repeated decomposition

private theorem existsSimpleSeparatorDecomposition (whole : List Nat) :
    ∃ segments finalGap,
      SimpleSeparatorDecomposition whole whole segments finalGap := by
  exact existsSimpleSeparatorDecompositionAux whole whole (by
    intro letter member
    exact member)

private theorem repeatedGap_filter_simple_nil
    (whole gap : List Nat)
    (repeated : ∀ letter, letter ∈ gap → 2 ≤ whole.count letter) :
    gap.filter (fun letter => decide (whole.count letter = 1)) = [] := by
  induction gap with
  | nil => rfl
  | cons letter gap induction =>
      have letterRepeated := repeated letter (by simp)
      have letterNotSimple : whole.count letter ≠ 1 := by omega
      simp [letterNotSimple, induction (by
        intro tested member
        exact repeated tested (List.Mem.tail letter member))]

namespace SimpleSeparatorDecomposition

private theorem separatorSequence_eq
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      SimpleSeparatorDecomposition whole source segments finalGap) :
    segments.map Prod.snd =
      source.filter (fun letter => decide (whole.count letter = 1)) := by
  induction decomposition with
  | final gap gapRepeated =>
      simpa using repeatedGap_filter_simple_nil whole gap gapRepeated
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail induction =>
      have gapEmpty :=
        repeatedGap_filter_simple_nil whole gap gapRepeated
      simp [List.filter_append, gapEmpty, separatorSimple, induction]

end SimpleSeparatorDecomposition

/-! ## Concrete two-letter reading of the S4_71 signature -/

/-- The public `S4_71` scanner with its private symbol layer inlined. The
transition table below is proved extensionally equal to `orderGapScan`. -/
private def canonicalOrderStep
    (x y : Nat) (state : OrderGapState) (letter : Nat) :
    OrderGapState :=
  if letter = x then
    match state with
    | .empty => .onlyXOne
    | .onlyYOne => .simpleYX
    | .onlyYMany => .xOneYManyYFirst
    | .onlyXOne => .onlyXMany
    | .onlyXMany => .onlyXMany
    | .simpleXY => .xManyYOneAfterXFirst
    | .simpleYX => .xManyYOneAfterYFirst
    | .xOneYManyXFirst => .xManyYManyAfterXFirst
    | .xOneYManyYFirst => .xManyYManyAfterYFirst
    | .xManyYOneBefore => .xManyYOneAfterXFirst
    | .xManyYOneAfterXFirst => .xManyYOneAfterXFirst
    | .xManyYOneAfterYFirst => .xManyYOneAfterYFirst
    | .xManyYManyBefore => .xManyYManyAfterXFirst
    | .xManyYManyAfterXFirst => .xManyYManyAfterXFirst
    | .xManyYManyAfterYFirst => .xManyYManyAfterYFirst
  else if letter = y then
    match state with
    | .empty => .onlyYOne
    | .onlyYOne => .onlyYMany
    | .onlyYMany => .onlyYMany
    | .onlyXOne => .simpleXY
    | .onlyXMany => .xManyYOneBefore
    | .simpleXY => .xOneYManyXFirst
    | .simpleYX => .xOneYManyYFirst
    | .xOneYManyXFirst => .xOneYManyXFirst
    | .xOneYManyYFirst => .xOneYManyYFirst
    | .xManyYOneBefore => .xManyYManyBefore
    | .xManyYOneAfterXFirst => .xManyYManyAfterXFirst
    | .xManyYOneAfterYFirst => .xManyYManyAfterYFirst
    | .xManyYManyBefore => .xManyYManyBefore
    | .xManyYManyAfterXFirst => .xManyYManyAfterXFirst
    | .xManyYManyAfterYFirst => .xManyYManyAfterYFirst
  else state

private def canonicalOrderScan
    (letters : List Nat) (x y : Nat) : OrderGapState :=
  letters.foldl (canonicalOrderStep x y) .empty

private theorem canonicalOrderScan_eq_orderGapScan
    (word : Word Nat) (x y : Nat) :
    canonicalOrderScan word.toList x y =
      S5_793Invariant.orderGapScan word x y := by
  unfold canonicalOrderScan S5_793Invariant.orderGapScan
  apply congrArg (fun step => word.toList.foldl step (.empty : OrderGapState))
  funext state letter
  cases state <;>
    by_cases isX : letter = x <;>
    by_cases isY : letter = y <;>
    simp_all [canonicalOrderStep, S5_793Invariant.orderStep,
      S5_793Invariant.orderSymbol, isX, isY]

private def canonicalPairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def canonicalPairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (canonicalPairKeep x y)

private theorem canonicalOrderFold_filter
    (x y : Nat) :
    ∀ (letters : List Nat) (initial : OrderGapState),
      letters.foldl (canonicalOrderStep x y) initial =
        (canonicalPairProjection letters x y).foldl
          (canonicalOrderStep x y) initial
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases isX : letter = x
      · subst letter
        have induction :=
          canonicalOrderFold_filter x y rest
            (canonicalOrderStep x y initial x)
        simpa [canonicalPairProjection, canonicalPairKeep] using induction
      · by_cases isY : letter = y
        · subst letter
          have induction :=
            canonicalOrderFold_filter x y rest
              (canonicalOrderStep x y initial y)
          simpa [canonicalPairProjection, canonicalPairKeep, isX]
            using induction
        · have induction :=
            canonicalOrderFold_filter x y rest initial
          simpa [canonicalPairProjection, canonicalPairKeep,
            canonicalOrderStep, isX, isY] using induction

private theorem canonicalOrderScan_eq_pairProjection
    (letters : List Nat) (x y : Nat) :
    canonicalOrderScan letters x y =
      canonicalOrderScan (canonicalPairProjection letters x y) x y := by
  exact canonicalOrderFold_filter x y letters .empty

private theorem canonicalPairProjection_count_of_kept
    (letters : List Nat) (x y selected : Nat)
    (kept : canonicalPairKeep x y selected = true) :
    (canonicalPairProjection letters x y).count selected =
      letters.count selected := by
  unfold canonicalPairProjection
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = selected
      · subst first
        simp [kept, induction]
      · by_cases firstKept : canonicalPairKeep x y first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem canonicalPairProjection_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ canonicalPairProjection letters x y) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [canonicalPairProjection, canonicalPairKeep] using kept

private theorem canonicalPairList_length
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest → selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction := canonicalPairList_length different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem canonicalPairList_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [canonicalPairList_length different letters onlyPair,
      xCount, yCount]
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

private theorem canonicalPairList_shape_two_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 2)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, x, y] ∨
      letters = [x, y, x] ∨ letters = [y, x, x] := by
  have lengthThree : letters.length = 3 := by
    rw [canonicalPairList_length different letters onlyPair,
      xCount, yCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨third, rest⟩
  · simp at lengthThree
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthThree
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  have thirdPair := onlyPair third (by simp)
  rcases firstPair with rfl | rfl
  · rcases secondPair with rfl | rfl
    · rcases thirdPair with rfl | rfl
      · simp [different, Ne.symm different] at yCount
      · exact Or.inl rfl
    · rcases thirdPair with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · simp [different, Ne.symm different] at xCount
  · rcases secondPair with rfl | rfl
    · rcases thirdPair with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · simp [different, Ne.symm different] at xCount
    · rcases thirdPair with rfl | rfl
      · simp [different, Ne.symm different] at xCount
      · simp [different, Ne.symm different] at xCount

private theorem canonicalPairProjection_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1) :
    canonicalPairProjection letters x y = [x, y] ∨
      canonicalPairProjection letters x y = [y, x] := by
  apply canonicalPairList_shape_one_one
  · exact different
  · rw [canonicalPairProjection_count_of_kept]
    · exact xCount
    · simp [canonicalPairKeep]
  · rw [canonicalPairProjection_count_of_kept]
    · exact yCount
    · simp [canonicalPairKeep]
  · intro value member
    exact canonicalPairProjection_member member

private theorem canonicalPairProjection_shape_two_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 2)
    (yCount : letters.count y = 1) :
    canonicalPairProjection letters x y = [x, x, y] ∨
      canonicalPairProjection letters x y = [x, y, x] ∨
        canonicalPairProjection letters x y = [y, x, x] := by
  apply canonicalPairList_shape_two_one
  · exact different
  · rw [canonicalPairProjection_count_of_kept]
    · exact xCount
    · simp [canonicalPairKeep]
  · rw [canonicalPairProjection_count_of_kept]
    · exact yCount
    · simp [canonicalPairKeep]
  · intro value member
    exact canonicalPairProjection_member member

private theorem simplePrecedes_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.SimplePrecedes word x y ↔
      canonicalPairProjection word.toList x y = [x, y] := by
  rw [S5_793Invariant.SimplePrecedes,
    ← canonicalOrderScan_eq_orderGapScan]
  rw [canonicalOrderScan_eq_pairProjection]
  rcases canonicalPairProjection_shape_one_one
      word.toList different xCount yCount with shape | shape
  · rw [shape]
    simp [canonicalOrderScan, canonicalOrderStep, different,
      Ne.symm different]
  · rw [shape]
    simp [canonicalOrderScan, canonicalOrderStep, different,
      Ne.symm different]

private theorem multipleLastBeforeSimple_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.MultipleLastBeforeSimple word x y ↔
      canonicalPairProjection word.toList x y = [x, x, y] := by
  rw [S5_793Invariant.MultipleLastBeforeSimple,
    ← canonicalOrderScan_eq_orderGapScan]
  rw [canonicalOrderScan_eq_pairProjection]
  rcases canonicalPairProjection_shape_two_one
      word.toList different xCount yCount with shape | shape | shape
  · rw [shape]
    simp [canonicalOrderScan, canonicalOrderStep, different,
      Ne.symm different]
  · rw [shape]
    simp [canonicalOrderScan, canonicalOrderStep, different,
      Ne.symm different]
  · rw [shape]
    simp [canonicalOrderScan, canonicalOrderStep, different,
      Ne.symm different]

private theorem canonicalPairProjection_reverse
    (letters : List Nat) (x y : Nat) :
    canonicalPairProjection letters.reverse x y =
      (canonicalPairProjection letters x y).reverse := by
  simp [canonicalPairProjection]

private theorem reverseMultipleLastBeforeSimple_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.MultipleLastBeforeSimple word.reverse x y ↔
      canonicalPairProjection word.toList x y = [y, x, x] := by
  have reversedXCount : word.reverse.toList.count x = 2 := by
    simpa [Word.toList_reverse, List.count_reverse] using xCount
  have reversedYCount : word.reverse.toList.count y = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using yCount
  rw [multipleLastBeforeSimple_iff_pairProjection
    word.reverse different reversedXCount reversedYCount]
  rw [Word.toList_reverse, canonicalPairProjection_reverse]
  constructor
  · intro equality
    have reversed := congrArg List.reverse equality
    simpa using reversed
  · intro equality
    rw [equality]
    simp

/-! ## Exact cuts at globally simple separators -/

private theorem canonicalPairProjection_of_y_absent
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      y ∉ letters →
        canonicalPairProjection letters x y =
          List.replicate (letters.count x) x
  | [], _ => by simp [canonicalPairProjection]
  | letter :: rest, absent => by
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      by_cases isX : letter = x
      · subst letter
        simp [canonicalPairProjection, canonicalPairKeep]
        change
          x :: canonicalPairProjection rest x y =
            List.replicate (Nat.succ (rest.count x)) x
        rw [canonicalPairProjection_of_y_absent different rest restAbsent]
        rw [List.replicate_succ]
      · have isY : letter ≠ y := by
          intro equality
          subst letter
          exact absent (List.Mem.head rest)
        simp [canonicalPairProjection, canonicalPairKeep, isX, isY]
        change
          canonicalPairProjection rest x y =
            List.replicate (rest.count x) x
        exact
          canonicalPairProjection_of_y_absent different rest restAbsent

private theorem canonicalPairProjection_at_simple_split
    (word : Word Nat) {x y : Nat} {prefixWords rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = prefixWords ++ y :: rest)
    (yCount : word.toList.count y = 1) :
    canonicalPairProjection word.toList x y =
      List.replicate (prefixWords.count x) x ++
        y :: List.replicate (rest.count x) x := by
  have yAbsentPrefix : y ∉ prefixWords := by
    intro member
    have positive : 1 ≤ prefixWords.count y :=
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
  simp only [canonicalPairProjection, List.filter_append,
    List.filter_cons]
  have yKept : canonicalPairKeep x y y = true := by
    simp [canonicalPairKeep]
  rw [if_pos yKept]
  change
    canonicalPairProjection prefixWords x y ++
        y :: canonicalPairProjection rest x y = _
  rw [canonicalPairProjection_of_y_absent different prefixWords yAbsentPrefix,
    canonicalPairProjection_of_y_absent different rest yAbsentRest]

private theorem simplePrecedes_iff_prefixCount_one
    (word : Word Nat) {x y : Nat} {prefixWords rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = prefixWords ++ y :: rest)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.SimplePrecedes word x y ↔
      prefixWords.count x = 1 := by
  rw [simplePrecedes_iff_pairProjection word different xCount yCount]
  rw [canonicalPairProjection_at_simple_split
    word different shape yCount]
  have splitCount : prefixWords.count x + rest.count x = 1 := by
    rw [shape, List.count_append, List.count_cons_of_ne
      (Ne.symm different)] at xCount
    simpa using xCount
  constructor
  · intro projection
    by_cases prefixOne : prefixWords.count x = 1
    · exact prefixOne
    · have prefixZero : prefixWords.count x = 0 := by omega
      have restOne : rest.count x = 1 := by omega
      simp [prefixZero, restOne, different, Ne.symm different] at projection
  · intro prefixOne
    have restZero : rest.count x = 0 := by omega
    simp [prefixOne, restZero]

private theorem multipleLastBeforeSimple_iff_prefixCount_two
    (word : Word Nat) {x y : Nat} {prefixWords rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = prefixWords ++ y :: rest)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.MultipleLastBeforeSimple word x y ↔
      prefixWords.count x = 2 := by
  rw [multipleLastBeforeSimple_iff_pairProjection
    word different xCount yCount]
  rw [canonicalPairProjection_at_simple_split
    word different shape yCount]
  have splitCount : prefixWords.count x + rest.count x = 2 := by
    rw [shape, List.count_append, List.count_cons_of_ne
      (Ne.symm different)] at xCount
    simpa using xCount
  constructor
  · intro projection
    by_cases prefixZero : prefixWords.count x = 0
    · have restTwo : rest.count x = 2 := by omega
      simp [prefixZero, restTwo, different, Ne.symm different] at projection
    · by_cases prefixOne : prefixWords.count x = 1
      · have restOne : rest.count x = 1 := by omega
        simp [prefixOne, restOne, different, Ne.symm different] at projection
      · omega
  · intro prefixTwo
    have restZero : rest.count x = 0 := by omega
    simp [prefixTwo, restZero]

private theorem reverseMultipleLastBeforeSimple_iff_prefixCount_zero
    (word : Word Nat) {x y : Nat} {prefixWords rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = prefixWords ++ y :: rest)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.MultipleLastBeforeSimple word.reverse x y ↔
      prefixWords.count x = 0 := by
  rw [reverseMultipleLastBeforeSimple_iff_pairProjection
    word different xCount yCount]
  rw [canonicalPairProjection_at_simple_split
    word different shape yCount]
  have splitCount : prefixWords.count x + rest.count x = 2 := by
    rw [shape, List.count_append, List.count_cons_of_ne
      (Ne.symm different)] at xCount
    simpa using xCount
  constructor
  · intro projection
    by_cases prefixZero : prefixWords.count x = 0
    · exact prefixZero
    · by_cases prefixOne : prefixWords.count x = 1
      · have restOne : rest.count x = 1 := by omega
        simp [prefixOne, restOne, different, Ne.symm different] at projection
      · have prefixTwo : prefixWords.count x = 2 := by omega
        have restZero : rest.count x = 0 := by omega
        simp [prefixTwo, restZero, different, Ne.symm different] at projection
  · intro prefixZero
    have restTwo : rest.count x = 2 := by omega
    simp [prefixZero, restTwo]

namespace SameCanonicalSignature

theorem refl (word : Word Nat) : SameCanonicalSignature word word :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameCanonicalSignature left right) :
    SameCanonicalSignature right left :=
  ⟨fun letter => (same.capped letter).symm,
    fun x y => (same.simpleSequence x y).symm,
    fun x y => (same.lastGap x y).symm,
    fun x y => (same.firstGap x y).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameCanonicalSignature left middle)
    (second : SameCanonicalSignature middle right) :
    SameCanonicalSignature left right :=
  ⟨fun letter => (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.simpleSequence x y).trans (second.simpleSequence x y),
    fun x y => (first.lastGap x y).trans (second.lastGap x y),
    fun x y => (first.firstGap x y).trans (second.firstGap x y)⟩

theorem count_eq_of_twoLimited
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList) :
    ∀ letter, left.toList.count letter = right.toList.count letter := by
  intro letter
  have equal := same.capped letter
  unfold S5_107.cappedMultiplicity at equal
  have leftUncapped :
      Nat.min 2 (left.toList.count letter) =
        left.toList.count letter :=
    Nat.min_eq_right (leftLimited letter)
  have rightUncapped :
      Nat.min 2 (right.toList.count letter) =
        right.toList.count letter :=
    Nat.min_eq_right (rightLimited letter)
  exact leftUncapped.symm.trans (equal.trans rightUncapped)

theorem prefixCount_eq
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList)
    {separator : Nat}
    {leftPrefix leftRest rightPrefix rightRest : List Nat}
    (leftShape : left.toList = leftPrefix ++ separator :: leftRest)
    (rightShape : right.toList = rightPrefix ++ separator :: rightRest)
    (leftSeparator : left.toList.count separator = 1)
    (rightSeparator : right.toList.count separator = 1) :
    ∀ letter, leftPrefix.count letter = rightPrefix.count letter := by
  have counts := same.count_eq_of_twoLimited leftLimited rightLimited
  intro letter
  by_cases selectedSeparator : letter = separator
  · subst letter
    have leftZero : leftPrefix.count separator = 0 := by
      rw [leftShape, List.count_append, List.count_cons_self] at leftSeparator
      omega
    have rightZero : rightPrefix.count separator = 0 := by
      rw [rightShape, List.count_append, List.count_cons_self] at rightSeparator
      omega
    rw [leftZero, rightZero]
  · have different : letter ≠ separator := selectedSeparator
    have totalEqual := counts letter
    have leftBound : left.toList.count letter ≤ 2 := leftLimited letter
    have rightBound : right.toList.count letter ≤ 2 := rightLimited letter
    by_cases leftAbsent : left.toList.count letter = 0
    · have rightAbsent : right.toList.count letter = 0 := by omega
      have leftPrefixZero : leftPrefix.count letter = 0 := by
        rw [leftShape, List.count_append,
          List.count_cons_of_ne (Ne.symm different)] at leftAbsent
        omega
      have rightPrefixZero : rightPrefix.count letter = 0 := by
        rw [rightShape, List.count_append,
          List.count_cons_of_ne (Ne.symm different)] at rightAbsent
        omega
      rw [leftPrefixZero, rightPrefixZero]
    · by_cases leftSimple : left.toList.count letter = 1
      · have rightSimple : right.toList.count letter = 1 := by omega
        have order := same.simpleSequence letter separator
        have leftOrder :=
          simplePrecedes_iff_prefixCount_one left different
            leftShape leftSimple leftSeparator
        have rightOrder :=
          simplePrecedes_iff_prefixCount_one right different
            rightShape rightSimple rightSeparator
        have prefixIff :
            leftPrefix.count letter = 1 ↔
              rightPrefix.count letter = 1 := by
          rw [← leftOrder, ← rightOrder]
          exact order
        have leftPrefixBound : leftPrefix.count letter ≤ 1 := by
          rw [leftShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at leftSimple
          omega
        have rightPrefixBound : rightPrefix.count letter ≤ 1 := by
          rw [rightShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at rightSimple
          omega
        by_cases leftOne : leftPrefix.count letter = 1
        · rw [leftOne, prefixIff.mp leftOne]
        · have rightNotOne : rightPrefix.count letter ≠ 1 :=
            fun rightOne => leftOne (prefixIff.mpr rightOne)
          omega
      · have leftMultiple : left.toList.count letter = 2 := by omega
        have rightMultiple : right.toList.count letter = 2 := by omega
        have lastIff :
            leftPrefix.count letter = 2 ↔
              rightPrefix.count letter = 2 := by
          rw [← multipleLastBeforeSimple_iff_prefixCount_two
              left different leftShape leftMultiple leftSeparator,
            ← multipleLastBeforeSimple_iff_prefixCount_two
              right different rightShape rightMultiple rightSeparator]
          exact same.lastGap letter separator
        have firstIff :
            leftPrefix.count letter = 0 ↔
              rightPrefix.count letter = 0 := by
          rw [← reverseMultipleLastBeforeSimple_iff_prefixCount_zero
              left different leftShape leftMultiple leftSeparator,
            ← reverseMultipleLastBeforeSimple_iff_prefixCount_zero
              right different rightShape rightMultiple rightSeparator]
          exact same.firstGap letter separator
        have leftPrefixBound : leftPrefix.count letter ≤ 2 := by
          rw [leftShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at leftMultiple
          omega
        have rightPrefixBound : rightPrefix.count letter ≤ 2 := by
          rw [rightShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at rightMultiple
          omega
        by_cases leftZero : leftPrefix.count letter = 0
        · rw [leftZero, firstIff.mp leftZero]
        · by_cases leftTwo : leftPrefix.count letter = 2
          · rw [leftTwo, lastIff.mp leftTwo]
          · have rightNotZero : rightPrefix.count letter ≠ 0 :=
              fun rightZero => leftZero (firstIff.mpr rightZero)
            have rightNotTwo : rightPrefix.count letter ≠ 2 :=
              fun rightTwo => leftTwo (lastIff.mpr rightTwo)
            omega

end SameCanonicalSignature

private def canonicalSimpleProjection (letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (letters.count letter = 1)

private theorem canonicalSimpleProjection_nodup (letters : List Nat) :
    (canonicalSimpleProjection letters).Nodup := by
  rw [List.nodup_iff_count]
  intro tested
  have countBound :=
    (List.filter_sublist
      (l := letters)
      (p := fun letter => decide (letters.count letter = 1))).count_le tested
  by_cases simple : letters.count tested = 1
  · simpa [canonicalSimpleProjection, simple] using countBound
  · have absent : tested ∉ canonicalSimpleProjection letters := by
      simp [canonicalSimpleProjection, simple]
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem canonicalSimpleProjection_pairProjection
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    (canonicalSimpleProjection letters).filter
        (canonicalPairKeep x y) =
      canonicalPairProjection letters x y := by
  unfold canonicalSimpleProjection canonicalPairProjection
  rw [List.filter_filter]
  apply List.filter_congr
  intro value _
  by_cases isX : value = x
  · subst value
    simp [canonicalPairKeep, xSimple]
  · by_cases isY : value = y
    · subst value
      simp [canonicalPairKeep, isX, ySimple]
    · simp [canonicalPairKeep, isX, isY]

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ value, value ∈ left ↔ value ∈ right) →
      (∀ x y,
        x ≠ y →
        x ∈ left →
        y ∈ left →
        (left.filter (canonicalPairKeep x y)).head? =
          (right.filter (canonicalPairKeep x y)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at this
  | head :: tail, [], _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at this
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have leftHeadMember : leftHead ∈ leftHead :: leftTail := by simp
        have rightHeadMember : rightHead ∈ leftHead :: leftTail :=
          (sameMembers rightHead).mpr (by simp)
        have pairHeads :=
          sameHeads leftHead rightHead different
            leftHeadMember rightHeadMember
        simp [canonicalPairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight : value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft : value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ x y,
            x ≠ y →
            x ∈ leftTail →
            y ∈ leftTail →
            (leftTail.filter (canonicalPairKeep x y)).head? =
              (rightTail.filter (canonicalPairKeep x y)).head? := by
        intro x y different xMember yMember
        have xNotHead : x ≠ leftHead := by
          intro equality
          subst x
          exact leftNodup.1 xMember
        have yNotHead : y ≠ leftHead := by
          intro equality
          subst y
          exact leftNodup.1 yMember
        have inherited :=
          sameHeads x y different
            (by simp [xMember]) (by simp [yMember])
        simpa [canonicalPairKeep, Ne.symm xNotHead,
          Ne.symm yNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

private theorem canonicalSimpleProjection_eq
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList) :
    canonicalSimpleProjection left.toList =
      canonicalSimpleProjection right.toList := by
  have counts := same.count_eq_of_twoLimited leftLimited rightLimited
  apply nodup_eq_of_pairProjection_head
  · exact canonicalSimpleProjection_nodup left.toList
  · exact canonicalSimpleProjection_nodup right.toList
  · intro letter
    constructor
    · intro member
      have leftSimple : left.toList.count letter = 1 := by
        have kept := (List.mem_filter.mp member).2
        simpa [canonicalSimpleProjection] using kept
      have rightSimple : right.toList.count letter = 1 := by
        rw [← counts letter]
        exact leftSimple
      apply List.mem_filter.mpr
      exact ⟨List.count_pos_iff.mp (by omega), by
        simp [rightSimple]⟩
    · intro member
      have rightSimple : right.toList.count letter = 1 := by
        have kept := (List.mem_filter.mp member).2
        simpa [canonicalSimpleProjection] using kept
      have leftSimple : left.toList.count letter = 1 := by
        rw [counts letter]
        exact rightSimple
      apply List.mem_filter.mpr
      exact ⟨List.count_pos_iff.mp (by omega), by
        simp [leftSimple]⟩
  · intro x y different xMember yMember
    have leftX : left.toList.count x = 1 := by
      have kept := (List.mem_filter.mp xMember).2
      simpa [canonicalSimpleProjection] using kept
    have leftY : left.toList.count y = 1 := by
      have kept := (List.mem_filter.mp yMember).2
      simpa [canonicalSimpleProjection] using kept
    have rightX : right.toList.count x = 1 := by
      rw [← counts x]
      exact leftX
    have rightY : right.toList.count y = 1 := by
      rw [← counts y]
      exact leftY
    rw [canonicalSimpleProjection_pairProjection
        left.toList different leftX leftY,
      canonicalSimpleProjection_pairProjection
        right.toList different rightX rightY]
    rcases canonicalPairProjection_shape_one_one
        left.toList different leftX leftY with leftXY | leftYX <;>
      rcases canonicalPairProjection_shape_one_one
        right.toList different rightX rightY with rightXY | rightYX
    · simp [leftXY, rightXY]
    · have leftOrder : S5_793Invariant.SimplePrecedes left x y :=
        (simplePrecedes_iff_pairProjection
          left different leftX leftY).2 leftXY
      have rightOrder := (same.simpleSequence x y).mp leftOrder
      have impossible :=
        (simplePrecedes_iff_pairProjection
          right different rightX rightY).1 rightOrder
      rw [rightYX] at impossible
      simp [different] at impossible
    · have rightOrder : S5_793Invariant.SimplePrecedes right x y :=
        (simplePrecedes_iff_pairProjection
          right different rightX rightY).2 rightXY
      have leftOrder := (same.simpleSequence x y).mpr rightOrder
      have impossible :=
        (simplePrecedes_iff_pairProjection
          left different leftX leftY).1 leftOrder
      rw [leftYX] at impossible
      simp [different] at impossible
    · simp [leftYX, rightYX]

/-! ## Choice-independent sorted simple-separator decompositions -/

private def renderSortedSeparatorDecomposition
    (segments : List (List Nat × Nat)) (finalGap : List Nat) : List Nat :=
  segments.flatMap (fun segment =>
      uniqueSeparatorSortQuadratic segment.1 ++ [segment.2]) ++
    uniqueSeparatorSortQuadratic finalGap

private theorem sortedQuadratic_eq_of_counts
    (left right : List Nat)
    (counts : ∀ letter, left.count letter = right.count letter) :
    uniqueSeparatorSortQuadratic left =
      uniqueSeparatorSortQuadratic right := by
  have permutation :
      (uniqueSeparatorSortQuadratic left).Perm
        (uniqueSeparatorSortQuadratic right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(uniqueSeparatorSortQuadratic_perm left).count letter,
      (uniqueSeparatorSortQuadratic_perm right).count letter]
    exact counts letter
  apply List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
  · simpa [uniqueSeparatorSortSquareSegment] using
      uniqueSeparatorSortSquareSegment_sorted
        (UniqueSeparatorSquareSegment.mk left none)
  · simpa [uniqueSeparatorSortSquareSegment] using
      uniqueSeparatorSortSquareSegment_sorted
        (UniqueSeparatorSquareSegment.mk right none)
  · exact permutation

private theorem listDerivesSortedSeparatorDecomposition
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      SimpleSeparatorDecomposition
        whole source segments finalGap)
    (limited : UniqueSeparatorTwoLimited whole) :
    ∀ (pre : List Nat),
      (∀ letter, (pre ++ source).count letter = whole.count letter) →
      ListDerives basis
        (pre ++ source)
        (pre ++ renderSortedSeparatorDecomposition segments finalGap) := by
  induction decomposition with
  | final gap repeated =>
      intro pre counts
      have quadratic :
          ∀ letter ∈ gap,
            (pre ++ gap ++ []).count letter = 2 := by
        intro letter member
        have atLeast := repeated letter member
        have atMost := limited letter
        have total := counts letter
        simpa using (show (pre ++ gap).count letter = 2 by omega)
      have sorted :=
        listDerivesQuadraticPermutation
          (uniqueSeparatorSortQuadratic_perm gap).symm
          pre [] quadratic
      simpa [renderSortedSeparatorDecomposition] using sorted
  | step gap separator remainder segments finalGap
      separatorSimple repeated tail induction =>
      intro pre counts
      have quadratic :
          ∀ letter ∈ gap,
            (pre ++ gap ++ (separator :: remainder)).count letter = 2 := by
        intro letter member
        have atLeast := repeated letter member
        have atMost := limited letter
        have total := counts letter
        simpa [List.append_assoc] using
          (show (pre ++ (gap ++ separator :: remainder)).count letter = 2 by
            omega)
      have firstStep :=
        listDerivesQuadraticPermutation
          (uniqueSeparatorSortQuadratic_perm gap).symm
          pre (separator :: remainder) quadratic
      let nextPre :=
        pre ++ uniqueSeparatorSortQuadratic gap ++ [separator]
      have nextCounts :
          ∀ letter,
            (nextPre ++ remainder).count letter = whole.count letter := by
        intro letter
        calc
          (nextPre ++ remainder).count letter =
              (pre ++ gap ++ separator :: remainder).count letter := by
            simp only [nextPre, List.count_append, List.count_cons,
              List.count_nil]
            rw [(uniqueSeparatorSortQuadratic_perm gap).count letter]
            omega
          _ = whole.count letter := by
            simpa [List.append_assoc] using counts letter
      have restStep := induction nextPre nextCounts
      have firstStep' :
          ListDerives basis
            (pre ++ gap ++ separator :: remainder)
            (nextPre ++ remainder) := by
        simpa [nextPre, List.append_assoc] using firstStep
      simpa [renderSortedSeparatorDecomposition, nextPre,
        List.append_assoc] using firstStep'.trans restStep

private theorem sortedSeparatorAlignmentAux
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      SimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      SimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftPrefix rightPrefix : List Nat)
    (leftShape : left.toList = leftPrefix ++ leftSource)
    (rightShape : right.toList = rightPrefix ++ rightSource)
    (prefixCounts :
      ∀ letter, leftPrefix.count letter = rightPrefix.count letter)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderSortedSeparatorDecomposition leftSegments leftFinal =
      renderSortedSeparatorDecomposition rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal leftPrefix rightPrefix with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightRepeated =>
          have totalCounts :=
            same.count_eq_of_twoLimited leftLimited rightLimited
          have gapCounts :
              ∀ letter, leftGap.count letter = rightSource.count letter := by
            intro letter
            have total := totalCounts letter
            have prefixWords := prefixCounts letter
            rw [leftShape, rightShape,
              List.count_append, List.count_append] at total
            omega
          simp [renderSortedSeparatorDecomposition,
            sortedQuadratic_eq_of_counts leftGap rightSource gapCounts]
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
          rcases separatorEq with ⟨separatorHeadEq, separatorRestEq⟩
          subst rightSeparator
          have leftCutShape :
              left.toList =
                (leftPrefix ++ leftGap) ++
                  leftSeparator :: leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightCutShape :
              right.toList =
                (rightPrefix ++ rightGap) ++
                  leftSeparator :: rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have cumulativeCounts :
              ∀ letter,
                (leftPrefix ++ leftGap).count letter =
                  (rightPrefix ++ rightGap).count letter :=
            same.prefixCount_eq leftLimited rightLimited
              leftCutShape rightCutShape
              leftSeparatorSimple rightSeparatorSimple
          have gapCounts :
              ∀ letter, leftGap.count letter = rightGap.count letter := by
            intro letter
            have cumulative := cumulativeCounts letter
            have prefixWords := prefixCounts letter
            simp only [List.count_append] at cumulative
            omega
          have headEq :=
            sortedQuadratic_eq_of_counts leftGap rightGap gapCounts
          have nextPrefixCounts :
              ∀ letter,
                (leftPrefix ++ leftGap ++ [leftSeparator]).count letter =
                  (rightPrefix ++ rightGap ++ [leftSeparator]).count
                    letter := by
            intro letter
            have cumulative := cumulativeCounts letter
            simp only [List.count_append, List.count_cons,
              List.count_nil] at cumulative ⊢
            omega
          have leftTailShape :
              left.toList =
                (leftPrefix ++ leftGap ++ [leftSeparator]) ++
                  leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightTailShape :
              right.toList =
                (rightPrefix ++ rightGap ++ [leftSeparator]) ++
                  rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have tailEq :=
            leftInduction rightTail
              (leftPrefix ++ leftGap ++ [leftSeparator])
              (rightPrefix ++ rightGap ++ [leftSeparator])
              leftTailShape rightTailShape nextPrefixCounts separatorRestEq
          calc
            renderSortedSeparatorDecomposition
                ((leftGap, leftSeparator) :: leftRest) leftFinal =
                (uniqueSeparatorSortQuadratic leftGap ++ [leftSeparator]) ++
                  renderSortedSeparatorDecomposition leftRest leftFinal := by
              simp [renderSortedSeparatorDecomposition, List.append_assoc]
            _ =
                (uniqueSeparatorSortQuadratic rightGap ++ [leftSeparator]) ++
                  renderSortedSeparatorDecomposition rightRest rightFinal := by
              rw [headEq, tailEq]
            _ = renderSortedSeparatorDecomposition
                ((rightGap, leftSeparator) :: rightRest) rightFinal := by
              simp [renderSortedSeparatorDecomposition, List.append_assoc]

private theorem sortedSeparatorAlignment
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      SimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal)
    (rightDecomposition :
      SimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal) :
    renderSortedSeparatorDecomposition leftSegments leftFinal =
      renderSortedSeparatorDecomposition rightSegments rightFinal := by
  have separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd =
          canonicalSimpleProjection left.toList := by
        simpa [canonicalSimpleProjection] using
          SimpleSeparatorDecomposition.separatorSequence_eq
            leftDecomposition
      _ = canonicalSimpleProjection right.toList :=
        canonicalSimpleProjection_eq same leftLimited rightLimited
      _ = rightSegments.map Prod.snd := by
        simpa [canonicalSimpleProjection] using
          (SimpleSeparatorDecomposition.separatorSequence_eq
            rightDecomposition).symm
  exact sortedSeparatorAlignmentAux same leftLimited rightLimited
    leftDecomposition rightDecomposition [] []
    (by simp) (by simp) (by simp) separatorEq

/-- The unrestricted combinatorial core of Edmunds' uniqueness argument on
two-limited words. No finite table search occurs: the proof splits at globally
simple variables and uses the first/last-gap signature to align every sorted
quadratic block. -/
theorem listDerivesOfSameCanonicalSignature_twoLimited
    {left right : Word Nat}
    (same : SameCanonicalSignature left right)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList) :
    ListDerives basis left.toList right.toList := by
  obtain ⟨leftSegments, leftFinal, leftDecomposition⟩ :=
    existsSimpleSeparatorDecomposition left.toList
  obtain ⟨rightSegments, rightFinal, rightDecomposition⟩ :=
    existsSimpleSeparatorDecomposition right.toList
  have leftNormal :=
    listDerivesSortedSeparatorDecomposition
      leftDecomposition leftLimited [] (by simp)
  have rightNormal :=
    listDerivesSortedSeparatorDecomposition
      rightDecomposition rightLimited [] (by simp)
  have normalEq :=
    sortedSeparatorAlignment same leftLimited rightLimited
      leftDecomposition rightDecomposition
  rw [normalEq] at leftNormal
  simpa using leftNormal.trans rightNormal.symm

/-! ## Endpoint-cap promotion and unrestricted completeness -/

private theorem directFactorModels :
    Models Generated.S4_71.table.semigroup basis := by
  intro identity member
  exact m6S4_71Embedding.pullback_identity identity
    (publishedM6Models identity member)

private theorem oppositeFactorModels :
    Models Generated.S4_71.table.semigroup.opposite basis := by
  intro identity member
  exact m6S4_71OppositeEmbedding.pullback_identity identity
    (publishedM6Models identity member)

/-- Every derivation from the shared sixteen laws preserves the complete
two-sided canonical signature. -/
theorem sameCanonicalSignature_of_derives
    {left right : Word Nat} (derivation : Derives basis left right) :
    SameCanonicalSignature left right :=
  sameCanonicalSignature_of_s4_71_factors ⟨left, right⟩
    (fun valuation => derivation.sound directFactorModels valuation)
    (fun valuation => derivation.sound oppositeFactorModels valuation)

/-- Equal canonical signatures are derivationally sufficient for the shared
sixteen-law basis. Endpoint capping supplies exact multiplicities; the
two-limited theorem then aligns and sorts every quadratic block. -/
theorem derivesOfSameCanonicalSignature
    {left right : Word Nat}
    (same : SameCanonicalSignature left right) :
    Derives basis left right := by
  have leftListDerivation := listDerivesEndpointCap left.toList
  have rightListDerivation := listDerivesEndpointCap right.toList
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          obtain
            ⟨leftCapHead, leftCapTail, leftCapShape,
              leftCapDerivation⟩ :=
            leftListDerivation.from_cons
          obtain
            ⟨rightCapHead, rightCapTail, rightCapShape,
              rightCapDerivation⟩ :=
            rightListDerivation.from_cons
          let leftCap : Word Nat :=
            S5_107.listWordOfCons leftCapHead leftCapTail
          let rightCap : Word Nat :=
            S5_107.listWordOfCons rightCapHead rightCapTail
          have leftCapToList :
              leftCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk leftHead leftTail).toList := by
            simpa [leftCap, S5_107.listWordOfCons, Word.toList] using
              leftCapShape.symm
          have rightCapToList :
              rightCap.toList =
                uniqueSeparatorEndpointCap
                  (Word.mk rightHead rightTail).toList := by
            simpa [rightCap, S5_107.listWordOfCons, Word.toList] using
              rightCapShape.symm
          have leftCapSignature :
              SameCanonicalSignature
                (Word.mk leftHead leftTail) leftCap :=
            sameCanonicalSignature_of_derives leftCapDerivation
          have rightCapSignature :
              SameCanonicalSignature
                (Word.mk rightHead rightTail) rightCap :=
            sameCanonicalSignature_of_derives rightCapDerivation
          have capSame : SameCanonicalSignature leftCap rightCap :=
            leftCapSignature.symm.trans <|
              same.trans rightCapSignature
          have leftLimited : UniqueSeparatorTwoLimited leftCap.toList := by
            rw [leftCapToList]
            exact uniqueSeparatorEndpointCap_twoLimited
              (Word.mk leftHead leftTail).toList
          have rightLimited : UniqueSeparatorTwoLimited rightCap.toList := by
            rw [rightCapToList]
            exact uniqueSeparatorEndpointCap_twoLimited
              (Word.mk rightHead rightTail).toList
          have capListDerivation :=
            listDerivesOfSameCanonicalSignature_twoLimited
              capSame leftLimited rightLimited
          have capWordDerivation : Derives basis leftCap rightCap := by
            have represented :
                ListDerives basis
                  (leftCapHead :: leftCapTail)
                  (rightCapHead :: rightCapTail) := by
              simpa [leftCap, rightCap, S5_107.listWordOfCons,
                Word.toList] using capListDerivation
            simpa [leftCap, rightCap] using represented.toWord
          exact leftCapDerivation.trans <|
            capWordDerivation.trans rightCapDerivation.symm

/-- Canonical representatives with equal signatures are connected by the
shared basis even without appealing to literal equality of their lists. -/
theorem listDerivesCanonicalWordsOfSameSignature
    {left right : Word Nat}
    (same : SameCanonicalSignature left right) :
    ListDerives basis
      (canonicalList left.toList) (canonicalList right.toList) := by
  have middle :=
    S5_107.ListDerives.ofWord (derivesOfSameCanonicalSignature same)
  exact (listDerivesCanonical left.toList).symm.trans <|
    middle.trans (listDerivesCanonical right.toList)

/-- Edmunds' Proposition 3.1(i) completeness statement for historical M6. -/
theorem m6Completeness : M6CompletenessObligation := by
  intro identity valid
  exact derivesOfSameCanonicalSignature
    (m6Valid_sameCanonicalSignature identity valid)

/-- Edmunds' Proposition 3.1(i) completeness statement for historical M19. -/
theorem m19Completeness : M19CompletenessObligation := by
  intro identity valid
  exact derivesOfSameCanonicalSignature
    (m19Valid_sameCanonicalSignature identity valid)

end SemigroupBasis.CoRoots.S5_400
