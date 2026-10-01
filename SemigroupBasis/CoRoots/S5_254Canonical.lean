import SemigroupBasis.CoRoots.S5_254Assembly

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## Choice-independent canonical render interface -/

private theorem existsSeparatorDecompositionData (whole : List Nat) :
    ∃ data : List (List Nat × Nat) × List Nat,
      GloballySimpleSeparatorDecomposition
        whole whole data.1 data.2 := by
  obtain ⟨segments, finalGap, decomposition⟩ :=
    existsGloballySimpleSeparatorDecomposition whole
  exact ⟨(segments, finalGap), decomposition⟩

noncomputable def canonicalSeparatorDecompositionData
    (whole : List Nat) : List (List Nat × Nat) × List Nat :=
  Classical.choose (existsSeparatorDecompositionData whole)

theorem canonicalSeparatorDecompositionData_spec (whole : List Nat) :
    GloballySimpleSeparatorDecomposition whole whole
      (canonicalSeparatorDecompositionData whole).1
      (canonicalSeparatorDecompositionData whole).2 :=
  Classical.choose_spec (existsSeparatorDecompositionData whole)

/-- The canonical M18 list render selected from the unique simple-separator
decomposition: deterministic gap-parity skeleton followed by the globally
sorted repeated-letter square bank. -/
noncomputable def canonicalM18Render (word : Word Nat) : List Nat :=
  renderCanonicalSeparatorSkeleton
      (canonicalSeparatorDecompositionData word.toList).1
      (canonicalSeparatorDecompositionData word.toList).2 ++
    renderSquareBank (S5_107.sortedMultipleLetters word.toList)

/-- Every word derives to its selected canonical M18 list render. -/
theorem listDerivesCanonicalM18Render (word : Word Nat) :
    ListDerives word.toList (canonicalM18Render word) := by
  simpa [canonicalM18Render] using
    listDerivesCanonicalSeparatorAssembly
      (canonicalSeparatorDecompositionData_spec word.toList)

namespace SameM18Signature

/-- The signature preserves the distinction between globally simple and
globally repeated variables. -/
theorem multiple
    {left right : Word Nat}
    (same : SameM18Signature left right) (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  have support := same.support letter
  have simple := same.globallySimple letter
  constructor
  · intro leftMultiple
    have rightPositive : 0 < right.toList.count letter :=
      List.count_pos_iff.mpr <|
        support.mp (List.count_pos_iff.mp (by omega))
    have rightNotOne : right.toList.count letter ≠ 1 := by
      intro rightOne
      have leftOne : left.toList.count letter = 1 :=
        simple.mpr rightOne
      omega
    omega
  · intro rightMultiple
    have leftPositive : 0 < left.toList.count letter :=
      List.count_pos_iff.mpr <|
        support.mpr (List.count_pos_iff.mp (by omega))
    have leftNotOne : left.toList.count letter ≠ 1 := by
      intro leftOne
      have rightOne : right.toList.count letter = 1 :=
        simple.mp leftOne
      omega
    omega

private theorem sortedMultipleNodup (letters : List Nat) :
    (S5_107.sortedMultipleLetters letters).Nodup := by
  unfold S5_107.sortedMultipleLetters
  exact
    (List.mergeSort_perm
      ((S5_107.distinctLetters letters).filter
        (fun letter => decide (2 ≤ letters.count letter)))
      (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr <|
      (S5_107.distinctLetters_nodup letters).filter
        (fun letter => decide (2 ≤ letters.count letter))

/-- The deterministic global square-bank labels depend only on support and
the globally-simple component of the M18 signature. -/
theorem sortedMultipleLetters_eq
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    S5_107.sortedMultipleLetters left.toList =
      S5_107.sortedMultipleLetters right.toList := by
  have permutation :
      (S5_107.sortedMultipleLetters left.toList).Perm
        (S5_107.sortedMultipleLetters right.toList) := by
    rw [List.perm_iff_count]
    intro tested
    rw [(sortedMultipleNodup left.toList).count,
      (sortedMultipleNodup right.toList).count]
    simp only [S5_107.sortedMultipleLetters_mem_iff,
      same.multiple tested]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (S5_107.sortedMultipleLetters_pairwise left.toList)
    (S5_107.sortedMultipleLetters_pairwise right.toList)
    permutation

end SameM18Signature

/-! ## Simple-separator order from prefix parity -/

/-- The maximal prefix before the first occurrence of `separator`. -/
def simplePrefixBefore (separator : Nat) : List Nat → List Nat
  | [] => []
  | letter :: letters =>
      if letter = separator then []
      else letter :: simplePrefixBefore separator letters

private theorem mem_of_mem_simplePrefixBefore
    (separator tested : Nat) :
    ∀ {letters : List Nat},
      tested ∈ simplePrefixBefore separator letters → tested ∈ letters
  | [], member => by
      simp [simplePrefixBefore] at member
  | letter :: letters, member => by
      by_cases equal : letter = separator
      · simp [simplePrefixBefore, equal] at member
      · simp only [simplePrefixBefore, equal, if_false,
          List.mem_cons] at member ⊢
        rcases member with testedEqual | member
        · exact Or.inl testedEqual
        · exact Or.inr <|
            mem_of_mem_simplePrefixBefore separator tested member

theorem simplePrefixBefore_split
    (separator : Nat) :
    ∀ (prefixWords suffix : List Nat),
      separator ∉ prefixWords →
      simplePrefixBefore separator
          (prefixWords ++ separator :: suffix) = prefixWords
  | [], suffix, _ => by simp [simplePrefixBefore]
  | letter :: prefixWords, suffix, absent => by
      have different : letter ≠ separator := by
        intro equal
        subst letter
        exact absent (List.Mem.head prefixWords)
      simp only [List.cons_append, simplePrefixBefore, different,
        if_false]
      rw [simplePrefixBefore_split separator prefixWords suffix (by
        intro member
        exact absent (List.Mem.tail letter member))]

private theorem separator_not_mem_prefix
    {letters prefixWords suffix : List Nat} {separator : Nat}
    (shape : letters = prefixWords ++ separator :: suffix)
    (simple : letters.count separator = 1) :
    separator ∉ prefixWords := by
  intro member
  have positive : 0 < prefixWords.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

theorem simplePrefixBefore_eq_of_split
    {word : Word Nat} {separator : Nat}
    (simple : GloballySimple word separator)
    (prefixWords suffix : List Nat)
    (shape : word.toList = prefixWords ++ separator :: suffix) :
    simplePrefixBefore separator word.toList = prefixWords := by
  rw [shape]
  exact simplePrefixBefore_split separator prefixWords suffix
    (separator_not_mem_prefix shape simple)

/-- For a globally simple separator, `PrefixParityBefore` is exactly the
parity of the deterministic prefix scanner. -/
theorem prefixParityBefore_iff_prefixValue
    {word : Word Nat} {separator tested parity : Nat}
    (simple : GloballySimple word separator) :
    PrefixParityBefore word separator tested parity ↔
      (simplePrefixBefore separator word.toList).count tested % 2 =
        parity := by
  constructor
  · rintro ⟨prefixWords, suffix, shape, value⟩
    rw [simplePrefixBefore_eq_of_split simple prefixWords suffix shape]
    exact value
  · intro value
    have member : separator ∈ word.toList :=
      List.count_pos_iff.mp (by rw [simple]; decide)
    obtain ⟨prefixWords, suffix, shape⟩ := List.mem_iff_append.mp member
    refine ⟨prefixWords, suffix, shape, ?_⟩
    rw [simplePrefixBefore_eq_of_split simple prefixWords suffix shape] at value
    exact value

namespace SameM18Signature

/-- Prefix-parity scanner values agree for every common globally simple
separator. -/
theorem prefixValue_eq
    {left right : Word Nat}
    (same : SameM18Signature left right)
    (separator tested : Nat)
    (leftSimple : GloballySimple left separator)
    (rightSimple : GloballySimple right separator) :
    (simplePrefixBefore separator left.toList).count tested % 2 =
      (simplePrefixBefore separator right.toList).count tested % 2 := by
  let parity :=
    (simplePrefixBefore separator left.toList).count tested % 2
  have leftRelation :
      PrefixParityBefore left separator tested parity :=
    (prefixParityBefore_iff_prefixValue leftSimple).2 rfl
  have rightRelation :=
    (same.prefixParity separator leftSimple rightSimple tested parity).1
      leftRelation
  exact
    ((prefixParityBefore_iff_prefixValue rightSimple).1
      rightRelation).symm

end SameM18Signature

/-- Globally simple letters in their occurrence order. -/
def simpleSeparatorSequence (word : Word Nat) : List Nat :=
  word.toList.filter
    (fun letter => decide (word.toList.count letter = 1))

theorem simpleSeparatorSequence_mem_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ simpleSeparatorSequence word ↔
      GloballySimple word letter := by
  simp only [simpleSeparatorSequence, List.mem_filter,
    decide_eq_true_eq, GloballySimple]
  constructor
  · exact And.right
  · intro simple
    exact ⟨List.count_pos_iff.mp (by omega), simple⟩

theorem simpleSeparatorSequence_nodup (word : Word Nat) :
    (simpleSeparatorSequence word).Nodup := by
  rw [List.nodup_iff_count]
  intro tested
  by_cases simple : word.toList.count tested = 1
  · change
      (word.toList.filter
        (fun letter => decide (word.toList.count letter = 1))).count tested ≤ 1
    exact Nat.le_trans
      (List.filter_sublist.count_le tested) (by omega)
  · have absent : tested ∉ simpleSeparatorSequence word := by
      simp [simpleSeparatorSequence, simple]
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simplePrefixBefore_filter
    (separator : Nat) (keep : Nat → Bool)
    (separatorKept : keep separator = true) :
    ∀ letters : List Nat,
      simplePrefixBefore separator (letters.filter keep) =
        (simplePrefixBefore separator letters).filter keep
  | [] => by simp [simplePrefixBefore]
  | letter :: letters => by
      by_cases equal : letter = separator
      · subst letter
        simp [simplePrefixBefore, separatorKept]
      · by_cases kept : keep letter = true
        · simp [simplePrefixBefore, equal, kept,
            simplePrefixBefore_filter separator keep separatorKept letters]
        · simp [simplePrefixBefore, equal, kept,
            simplePrefixBefore_filter separator keep separatorKept letters]

private theorem simplePrefixBefore_mem_iff_parity_one
    (word : Word Nat) (separator tested : Nat)
    (separatorSimple : GloballySimple word separator)
    (testedSimple : GloballySimple word tested) :
    tested ∈ simplePrefixBefore separator word.toList ↔
      (simplePrefixBefore separator word.toList).count tested % 2 = 1 := by
  have separatorMember : separator ∈ word.toList :=
    List.count_pos_iff.mp (by rw [separatorSimple]; decide)
  obtain ⟨prefixWords, suffix, shape⟩ :=
    List.mem_iff_append.mp separatorMember
  have prefixEq :=
    simplePrefixBefore_eq_of_split separatorSimple prefixWords suffix shape
  rw [prefixEq]
  have prefixBound : prefixWords.count tested ≤ 1 := by
    change word.toList.count tested = 1 at testedSimple
    rw [shape, List.count_append, List.count_cons] at testedSimple
    omega
  constructor
  · intro member
    have positive : 0 < prefixWords.count tested :=
      List.count_pos_iff.mpr member
    omega
  · intro parityOne
    apply List.count_pos_iff.mp
    omega

private theorem sequencePrefixMembership_iff
    (word : Word Nat) (separator tested : Nat)
    (separatorSimple : GloballySimple word separator) :
    tested ∈
        simplePrefixBefore separator (simpleSeparatorSequence word) ↔
      GloballySimple word tested ∧
        tested ∈ simplePrefixBefore separator word.toList := by
  let keep :=
    fun letter => decide (word.toList.count letter = 1)
  have separatorKept : keep separator = true := by
    simp [keep, GloballySimple] at separatorSimple ⊢
    exact separatorSimple
  rw [simpleSeparatorSequence,
    simplePrefixBefore_filter separator keep separatorKept]
  simp [keep, GloballySimple, and_comm]

private theorem list_eq_of_same_mem_same_prefix :
    ∀ (left right : List Nat),
      left.Nodup → right.Nodup →
      (∀ tested, tested ∈ left ↔ tested ∈ right) →
      (∀ marker tested,
        marker ∈ left → marker ∈ right →
        (tested ∈ simplePrefixBefore marker left ↔
          tested ∈ simplePrefixBefore marker right)) →
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
            tested ∈ simplePrefixBefore head right := by
          rw [rightShape,
            simplePrefixBefore_split head before after headNotBefore]
          exact member
        have leftPrefixMember :
            tested ∈ simplePrefixBefore head (head :: tail) :=
          (samePrefix head tested (by simp) headRight).mpr
            rightPrefixMember
        simpa [simplePrefixBefore] using leftPrefixMember
      have rightCons : right = head :: after := by
        simpa [beforeEmpty] using rightShape
      rw [rightCons] at rightNodup sameMem samePrefix ⊢
      have headNotTail : head ∉ tail :=
        (List.nodup_cons.mp leftNodup).1
      have headNotAfter : head ∉ after :=
        (List.nodup_cons.mp rightNodup).1
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have afterNodup := (List.nodup_cons.mp rightNodup).2
      have tailMem : ∀ tested, tested ∈ tail ↔ tested ∈ after := by
        intro tested
        have testedNeHeadLeft : tested ∈ tail → tested ≠ head := by
          intro member equal
          subst tested
          exact headNotTail member
        have testedNeHeadRight : tested ∈ after → tested ≠ head := by
          intro member equal
          subst tested
          exact headNotAfter member
        constructor
        · intro member
          have full := (sameMem tested).mp (List.Mem.tail head member)
          exact (List.mem_cons.mp full).resolve_left
            (testedNeHeadLeft member)
        · intro member
          have full := (sameMem tested).mpr (List.Mem.tail head member)
          exact (List.mem_cons.mp full).resolve_left
            (testedNeHeadRight member)
      have tailPrefix : ∀ marker tested,
          marker ∈ tail → marker ∈ after →
          (tested ∈ simplePrefixBefore marker tail ↔
            tested ∈ simplePrefixBefore marker after) := by
        intro marker tested markerLeft markerRight
        have markerNeHead : marker ≠ head := by
          intro equal
          subst marker
          exact headNotTail markerLeft
        have headNeMarker : head ≠ marker := Ne.symm markerNeHead
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
        · simpa [simplePrefixBefore, headNeMarker,
            testedEq, Ne.symm testedEq] using full
      rw [list_eq_of_same_mem_same_prefix
        tail after tailNodup afterNodup tailMem tailPrefix]

namespace SameM18Signature

/-- The complete ordered sequence of globally simple separators is determined
by predecessor parity in the signature. -/
theorem simpleSeparatorSequence_eq
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    simpleSeparatorSequence left = simpleSeparatorSequence right := by
  apply list_eq_of_same_mem_same_prefix
    (simpleSeparatorSequence left)
    (simpleSeparatorSequence right)
    (simpleSeparatorSequence_nodup left)
    (simpleSeparatorSequence_nodup right)
  · intro tested
    rw [simpleSeparatorSequence_mem_iff,
      simpleSeparatorSequence_mem_iff]
    exact same.globallySimple tested
  · intro marker tested markerLeft markerRight
    have leftMarkerSimple : GloballySimple left marker :=
      (simpleSeparatorSequence_mem_iff left marker).mp markerLeft
    have rightMarkerSimple : GloballySimple right marker :=
      (simpleSeparatorSequence_mem_iff right marker).mp markerRight
    rw [sequencePrefixMembership_iff
          left marker tested leftMarkerSimple,
        sequencePrefixMembership_iff
          right marker tested rightMarkerSimple]
    have testedSimple := same.globallySimple tested
    constructor
    · rintro ⟨leftTestedSimple, leftBefore⟩
      have leftParity :=
        (simplePrefixBefore_mem_iff_parity_one
          left marker tested leftMarkerSimple leftTestedSimple).mp
          leftBefore
      have parityEq :=
        same.prefixValue_eq marker tested
          leftMarkerSimple rightMarkerSimple
      have rightParity :
          (simplePrefixBefore marker right.toList).count tested % 2 = 1 := by
        rw [← parityEq]
        exact leftParity
      exact
        ⟨testedSimple.mp leftTestedSimple,
          (simplePrefixBefore_mem_iff_parity_one
            right marker tested rightMarkerSimple
              (testedSimple.mp leftTestedSimple)).mpr rightParity⟩
    · rintro ⟨rightTestedSimple, rightBefore⟩
      have rightParity :=
        (simplePrefixBefore_mem_iff_parity_one
          right marker tested rightMarkerSimple rightTestedSimple).mp
          rightBefore
      have parityEq :=
        same.prefixValue_eq marker tested
          leftMarkerSimple rightMarkerSimple
      have leftParity :
          (simplePrefixBefore marker left.toList).count tested % 2 = 1 := by
        rw [parityEq]
        exact rightParity
      exact
        ⟨testedSimple.mpr rightTestedSimple,
          (simplePrefixBefore_mem_iff_parity_one
            left marker tested leftMarkerSimple
              (testedSimple.mpr rightTestedSimple)).mpr leftParity⟩

end SameM18Signature

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

namespace GloballySimpleSeparatorDecomposition

/-- The separators carried by a decomposition are exactly the globally simple
letters of its source, in source order. -/
theorem separatorSequence_eq
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      GloballySimpleSeparatorDecomposition
        whole source segments finalGap) :
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

end GloballySimpleSeparatorDecomposition

private theorem separatorSkeletonAlignmentAux
    {left right : Word Nat}
    (same : SameM18Signature left right)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      GloballySimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      GloballySimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftPrefix rightPrefix : List Nat)
    (leftShape : left.toList = leftPrefix ++ leftSource)
    (rightShape : right.toList = rightPrefix ++ rightSource)
    (prefixParity : ∀ tested,
      leftPrefix.count tested % 2 =
        rightPrefix.count tested % 2)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderCanonicalSeparatorSkeleton leftSegments leftFinal =
      renderCanonicalSeparatorSkeleton rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal leftPrefix rightPrefix with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          apply canonicalGapParityResidue_eq_of_parity
          intro tested
          have total := same.totalParity tested
          have prefixWords := prefixParity tested
          rw [leftShape, rightShape,
            List.count_append, List.count_append] at total
          omega
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
          have cumulativeParity : ∀ tested,
              (leftPrefix ++ leftGap).count tested % 2 =
                (rightPrefix ++ rightGap).count tested % 2 := by
            intro tested
            have leftRelation :
                PrefixParityBefore left leftSeparator tested
                  ((leftPrefix ++ leftGap).count tested % 2) := by
              refine ⟨leftPrefix ++ leftGap, leftRemainder, ?_, rfl⟩
              rw [leftShape]
              simp [List.append_assoc]
            have rightRelation :=
              (same.prefixParity leftSeparator
                leftSeparatorSimple rightSeparatorSimple tested _).mp
                  leftRelation
            have rightValue :=
              (prefixParityBefore_iff_prefixValue
                rightSeparatorSimple).mp rightRelation
            have rightPrefixEq :
                simplePrefixBefore leftSeparator right.toList =
                  rightPrefix ++ rightGap := by
              apply simplePrefixBefore_eq_of_split
                rightSeparatorSimple
                (rightPrefix ++ rightGap) rightRemainder
              rw [rightShape]
              simp [List.append_assoc]
            rw [rightPrefixEq] at rightValue
            exact rightValue.symm
          have gapParity : ∀ tested,
              leftGap.count tested % 2 =
                rightGap.count tested % 2 := by
            intro tested
            have cumulative := cumulativeParity tested
            have prefixWords := prefixParity tested
            simp only [List.count_append] at cumulative
            omega
          have headEq :=
            canonicalGapParityResidue_eq_of_parity
              leftGap rightGap gapParity
          have nextPrefixParity : ∀ tested,
              (leftPrefix ++ leftGap ++ [leftSeparator]).count tested % 2 =
                (rightPrefix ++ rightGap ++ [leftSeparator]).count tested % 2 := by
            intro tested
            have cumulative := cumulativeParity tested
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
              leftTailShape rightTailShape nextPrefixParity separatorTailEq
          simp [renderCanonicalSeparatorSkeleton, headEq, tailEq]

/-- Exact remaining skeleton proposition after multi-gap derivational
assembly. It contains no pair extraction or square-bank algebra: only the
claim that the ordered simple separators and each intervening gap parity are
determined by `SameM18Signature`. -/
def CanonicalSeparatorSkeletonAlignmentObligation : Prop :=
  ∀ (left right : Word Nat),
    SameM18Signature left right →
    ∀ (leftSegments rightSegments : List (List Nat × Nat))
      (leftFinal rightFinal : List Nat),
      GloballySimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal →
      GloballySimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal →
      renderCanonicalSeparatorSkeleton leftSegments leftFinal =
        renderCanonicalSeparatorSkeleton rightSegments rightFinal

/-- Prefix parity aligns the ordered simple separators and the parity profile
of every intervening gap. -/
theorem canonicalSeparatorSkeletonAlignment :
    CanonicalSeparatorSkeletonAlignmentObligation := by
  intro left right same leftSegments rightSegments leftFinal rightFinal
    leftDecomposition rightDecomposition
  have separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd = simpleSeparatorSequence left := by
        simpa [simpleSeparatorSequence] using
          leftDecomposition.separatorSequence_eq
      _ = simpleSeparatorSequence right :=
        same.simpleSeparatorSequence_eq
      _ = rightSegments.map Prod.snd := by
        simpa [simpleSeparatorSequence] using
          rightDecomposition.separatorSequence_eq.symm
  exact separatorSkeletonAlignmentAux same
    leftDecomposition rightDecomposition [] []
    (by simp) (by simp) (by simp) separatorEq

/-- Once the exact skeleton-alignment proposition is discharged, literal
canonical renders depend only on the M18 signature. -/
theorem canonicalM18Render_eq_of_sameSignature_of_alignment
    (alignment : CanonicalSeparatorSkeletonAlignmentObligation)
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    canonicalM18Render left = canonicalM18Render right := by
  have skeletonEq :=
    alignment left right same
      (canonicalSeparatorDecompositionData left.toList).1
      (canonicalSeparatorDecompositionData right.toList).1
      (canonicalSeparatorDecompositionData left.toList).2
      (canonicalSeparatorDecompositionData right.toList).2
      (canonicalSeparatorDecompositionData_spec left.toList)
      (canonicalSeparatorDecompositionData_spec right.toList)
  have bankEq := same.sortedMultipleLetters_eq
  simp [canonicalM18Render, skeletonEq, bankEq]

/-- Exact signature-sufficiency endpoint reduced to skeleton alignment. -/
theorem derivesOfSameM18Signature_of_alignment
    (alignment : CanonicalSeparatorSkeletonAlignmentObligation)
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    Derives basis left right := by
  have leftNormal := listDerivesCanonicalM18Render left
  have rightNormal := listDerivesCanonicalM18Render right
  have renderEq :=
    canonicalM18Render_eq_of_sameSignature_of_alignment alignment same
  rw [renderEq] at leftNormal
  have listDerivation := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons, Word.toList] using
            S5_107.ListDerives.toWord listDerivation

/-- Literal canonical renders are determined by `SameM18Signature`. -/
theorem canonicalM18Render_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    canonicalM18Render left = canonicalM18Render right :=
  canonicalM18Render_eq_of_sameSignature_of_alignment
    canonicalSeparatorSkeletonAlignment same

/-- Unconditional M18 signature sufficiency for the displayed fifteen-law
basis. -/
theorem derivesOfSameM18Signature
    {left right : Word Nat}
    (same : SameM18Signature left right) :
    Derives basis left right :=
  derivesOfSameM18Signature_of_alignment
    canonicalSeparatorSkeletonAlignment same

end SemigroupBasis.CoRoots.S5_254
