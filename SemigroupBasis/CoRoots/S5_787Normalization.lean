import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_787Invariant
import SemigroupBasis.Examples.UniqueSeparatorFourFinal

namespace SemigroupBasis.CoRoots.S5_787

open SemigroupBasis
open SemigroupBasis.Examples

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay an arbitrary derivation for the seven-law `S4_69` basis after a
fixed nonempty prefix. The first six laws are direct consequences of the
`S5_787` basis. The source rotation is replayed by the prefix-guarded
rotation law. -/
private theorem liftUniqueSeparatorUnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives uniqueSeparatorFourBasis left right)
    (pre : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (pre ++ left.bind sigma)
      (pre ++ right.bind sigma) := by
  induction derivation generalizing pre sigma with
  | fromBasis member =>
      simp only [uniqueSeparatorFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [uniqueSeparatorPowerLaw, uniqueSeparatorXX,
          uniqueSeparatorXXX, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          Derives.prepend pre
            (derivesPowerExpansion (sigma 0))
      · simpa [uniqueSeparatorLeftDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pre
            (derivesLeftDuplication (sigma 0) (sigma 1))
      · simpa [uniqueSeparatorMiddleDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pre
            (derivesMiddleDuplication (sigma 0) (sigma 1))
      · simpa [uniqueSeparatorRightDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pre
            (derivesRightDuplication (sigma 0) (sigma 1))
      · simpa [uniqueSeparatorAlternatingLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pre
            (derivesAlternatingExtension (sigma 0) (sigma 1))
      · simpa [uniqueSeparatorSquaresLaw,
          uniqueSeparatorXYX, uniqueSeparatorXXYY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend pre
            (derivesSquares (sigma 0) (sigma 1))
      · simpa [uniqueSeparatorRotationLaw,
          uniqueSeparatorXYX, uniqueSeparatorYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesPrefixedRotation pre (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih pre sigma)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst pre sigma) (ihSecond pre sigma)
  | prepend innerPre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (pre ++ innerPre.bind sigma) sigma
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih pre sigma) (post.bind sigma)
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih pre (fun letter => (tau letter).bind sigma)

private theorem liftUniqueSeparatorListUnderPrefix
    (pre : Word Nat) {left right : List Nat}
    (derivation : UniqueSeparatorListDerives left right) :
    S5_107.ListDerives basis
      (pre.toList ++ left)
      (pre.toList ++ right) := by
  cases derivation with
  | empty =>
      simpa using
        S5_107.ListDerives.refl
          (basis := basis) pre.toList
  | words wordDerivation =>
      have lifted :=
        liftUniqueSeparatorUnderPrefix
          wordDerivation pre Word.singleton
      rw [bind_singleton, bind_singleton] at lifted
      simpa [Word.toList_append] using
        S5_107.ListDerives.ofWord lifted

private theorem exactCut_left_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right)
    (member : tested ∈ left) :
    tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_left _ member

private theorem exactCut_right_mem
    {letters left right : List Nat} {separator tested : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right)
    (member : tested ∈ right) :
    tested ∈ letters := by
  rw [cut.1]
  exact List.mem_append_right _ (List.Mem.tail separator member)

private theorem exactCut_addPrefix
    {letters left right pre : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right)
    (separatorNotPrefix : separator ∉ pre)
    (prefixDisjointRight :
      UniqueSeparatorFourSupportsDisjoint pre right) :
    UniqueSeparatorFourExactCut
      (pre ++ letters) (pre ++ left)
      separator right := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cut.1]
    simp [List.append_assoc]
  · rw [List.count_append,
      List.count_eq_zero.mpr separatorNotPrefix, cut.2.1]
  · intro tested member rightMember
    rcases List.mem_append.mp member with
      prefixMember | leftMember
    · exact prefixDisjointRight tested prefixMember rightMember
    · exact cut.2.2 tested leftMember rightMember

private theorem exactCut_dropPrefix
    {separator : Nat} :
    ∀ {pre letters left right : List Nat},
      separator ∉ pre ->
      UniqueSeparatorFourExactCut
          (pre ++ letters) left separator right ->
      ∃ tailLeft,
        left = pre ++ tailLeft ∧
          UniqueSeparatorFourExactCut
            letters tailLeft separator right
  | [], letters, left, right, _, cut => by
      exact ⟨left, by simp, by simpa using cut⟩
  | prefixHead :: prefixTail, letters, left, right,
      separatorNotPrefix, cut => by
      have headDifferent : prefixHead ≠ separator := by
        intro equality
        subst prefixHead
        exact separatorNotPrefix (by simp)
      cases left with
      | nil =>
          have headsEqual : prefixHead = separator := by
            simpa [List.cons_append] using
              congrArg List.head? cut.1
          exact False.elim (headDifferent headsEqual)
      | cons leftHead leftTail =>
          have splitTail :
              prefixTail ++ letters =
                leftTail ++ separator :: right := by
            have split := cut.1
            simp only [List.cons_append, List.cons.injEq] at split
            exact split.2
          have headEqual : prefixHead = leftHead := by
            have split := cut.1
            simp only [List.cons_append, List.cons.injEq] at split
            exact split.1
          subst leftHead
          have tailCount :
              (prefixTail ++ letters).count separator = 1 := by
            have fullCount := cut.2.1
            simp only [List.cons_append,
              List.count_cons_of_ne headDifferent] at fullCount
            exact fullCount
          have tailDisjoint :
              UniqueSeparatorFourSupportsDisjoint
                leftTail right := by
            intro tested leftMember rightMember
            exact cut.2.2 tested
              (List.Mem.tail prefixHead leftMember) rightMember
          have tailCut :
              UniqueSeparatorFourExactCut
                (prefixTail ++ letters)
                leftTail separator right :=
            ⟨splitTail, tailCount, tailDisjoint⟩
          have separatorNotTail :
              separator ∉ prefixTail := by
            intro member
            exact separatorNotPrefix
              (List.Mem.tail prefixHead member)
          obtain ⟨tailLeft, leftEq, reducedCut⟩ :=
            exactCut_dropPrefix separatorNotTail tailCut
          exact
            ⟨tailLeft, by simp [leftEq], reducedCut⟩

/-- The support skeleton of a canonical render is the canonical segment
list itself. -/
private theorem exactCutSupportSkeleton_eq_canonicalRender
    {segments : List UniqueSeparatorCanonicalSegment}
    (canonical : UniqueSeparatorCanonical segments) :
    S5_441.exactCutSupportSkeleton
        (uniqueSeparatorCanonicalRender segments) =
      segments := by
  apply uniqueSeparatorCanonical_eq_of_sameSignature
    (S5_441.exactCutSupportSkeleton_canonical
      (uniqueSeparatorCanonicalRender segments))
    canonical
  refine ⟨?_, ?_, ?_⟩
  · intro tested
    rw [S5_441.exactCutSupportSkeleton_render_mem_iff]
  · intro skeletonLeft skeletonRight separator cut
    obtain
      ⟨left, right, sourceCut, leftSupport, rightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_reflectExactCut cut
    exact
      ⟨left, right, sourceCut,
        fun tested => (leftSupport tested).symm,
        fun tested => (rightSupport tested).symm⟩
  · intro left right separator cut
    obtain
      ⟨skeletonLeft, skeletonRight, skeletonCut,
        leftSupport, rightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_transportExactCut cut
    exact
      ⟨skeletonLeft, skeletonRight, skeletonCut,
        leftSupport, rightSupport⟩

/-- The complete `S4_69` normalizer can be retargeted to the exact-cut
support skeleton, since both canonical segment lists have the same support
and exact-cut signature. -/
private theorem uniqueSeparatorDerivesExactCutSupportSkeleton
    (word : Word Nat) :
    UniqueSeparatorListDerives word.toList
      (uniqueSeparatorCanonicalRender
        (S5_441.exactCutSupportSkeleton word.toList)) := by
  have normalDerivation :=
    uniqueSeparatorFour_derivesNormal word
  have targetNonempty :
      uniqueSeparatorFourNormalRender word ≠ [] := by
    cases word with
    | mk head tail =>
        exact normalDerivation.target_ne_nil
  cases normalShape :
      uniqueSeparatorFourNormalRender word with
  | nil =>
      exact False.elim (targetNonempty normalShape)
  | cons normalHead normalTail =>
      have shapedDerivation := normalDerivation
      rw [normalShape] at shapedDerivation
      let normalWord :=
        uniqueSeparatorWordOfCons normalHead normalTail
      have wordDerivation :
          Derives uniqueSeparatorFourBasis word normalWord := by
        cases word with
        | mk head tail =>
            exact shapedDerivation.toWord
      have equalEval :
          ∀ valuation : Nat -> Fin 4,
            uniqueSeparatorFour.semigroup.eval valuation word =
              uniqueSeparatorFour.semigroup.eval
                valuation normalWord :=
        fun valuation =>
          wordDerivation.sound
            uniqueSeparatorFourBasis_models valuation
      have sameSupport :
          S5_441Invariant.SameSupport word normalWord :=
        S5_441Invariant.sameSupport_of_uniqueSeparatorFour_equalEval
          word normalWord equalEval
      have sameExactCuts :
          S5_441Invariant.SameExactCutSignature word normalWord :=
        S5_441Invariant.sameExactCutSignature_of_uniqueSeparatorFour_equalEval
          word normalWord equalEval
      have skeletonsEqual :
          S5_441.exactCutSupportSkeleton word.toList =
            S5_441.exactCutSupportSkeleton normalWord.toList :=
        S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
          sameSupport sameExactCuts
      have normalWordList :
          normalWord.toList =
            uniqueSeparatorCanonicalRender
              (uniqueSeparatorFourNormalSegments word) := by
        change normalHead :: normalTail =
          uniqueSeparatorCanonicalRender
            (uniqueSeparatorFourNormalSegments word)
        simpa [uniqueSeparatorFourNormalRender] using
          normalShape.symm
      have normalSkeleton :
          S5_441.exactCutSupportSkeleton normalWord.toList =
            uniqueSeparatorFourNormalSegments word := by
        rw [normalWordList]
        exact
          exactCutSupportSkeleton_eq_canonicalRender
            (uniqueSeparatorFourNormalSegments_canonical word)
      have sourceSkeleton :
          S5_441.exactCutSupportSkeleton word.toList =
            uniqueSeparatorFourNormalSegments word :=
        skeletonsEqual.trans normalSkeleton
      have renderedEqual :
          uniqueSeparatorFourNormalRender word =
            uniqueSeparatorCanonicalRender
              (S5_441.exactCutSupportSkeleton word.toList) := by
        simp [uniqueSeparatorFourNormalRender, sourceSkeleton]
      rw [renderedEqual] at normalDerivation
      exact normalDerivation

private theorem exactCutSupportSkeleton_eq_of_listSignature
    {left right : List Nat}
    (sameSupport :
      ∀ tested, tested ∈ left ↔ tested ∈ right)
    (forward :
      ∀ {leftPrefix leftSuffix separator},
        UniqueSeparatorFourExactCut
            left leftPrefix separator leftSuffix ->
        ∃ rightPrefix rightSuffix,
          UniqueSeparatorFourExactCut
              right rightPrefix separator rightSuffix ∧
            (∀ tested,
              tested ∈ rightPrefix ↔ tested ∈ leftPrefix) ∧
            (∀ tested,
              tested ∈ rightSuffix ↔ tested ∈ leftSuffix))
    (backward :
      ∀ {rightPrefix rightSuffix separator},
        UniqueSeparatorFourExactCut
            right rightPrefix separator rightSuffix ->
        ∃ leftPrefix leftSuffix,
          UniqueSeparatorFourExactCut
              left leftPrefix separator leftSuffix ∧
            (∀ tested,
              tested ∈ leftPrefix ↔ tested ∈ rightPrefix) ∧
            (∀ tested,
              tested ∈ leftSuffix ↔ tested ∈ rightSuffix)) :
    S5_441.exactCutSupportSkeleton left =
      S5_441.exactCutSupportSkeleton right := by
  apply uniqueSeparatorCanonical_eq_of_sameSignature
    (S5_441.exactCutSupportSkeleton_canonical left)
    (S5_441.exactCutSupportSkeleton_canonical right)
  refine ⟨?_, ?_, ?_⟩
  · intro tested
    rw [S5_441.exactCutSupportSkeleton_render_mem_iff,
      S5_441.exactCutSupportSkeleton_render_mem_iff]
    exact sameSupport tested
  · intro sourceSkeletonLeft sourceSkeletonRight separator cut
    obtain
      ⟨sourceLeft, sourceRight, sourceCut,
        sourceLeftSupport, sourceRightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_reflectExactCut cut
    obtain
      ⟨targetLeft, targetRight, targetCut,
        targetLeftSupport, targetRightSupport⟩ :=
      forward sourceCut
    obtain
      ⟨targetSkeletonLeft, targetSkeletonRight,
        targetSkeletonCut, targetSkeletonLeftSupport,
        targetSkeletonRightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_transportExactCut
        targetCut
    refine
      ⟨targetSkeletonLeft, targetSkeletonRight,
        targetSkeletonCut, ?_, ?_⟩
    · intro tested
      exact
        (targetSkeletonLeftSupport tested).trans <|
          (targetLeftSupport tested).trans
            (sourceLeftSupport tested).symm
    · intro tested
      exact
        (targetSkeletonRightSupport tested).trans <|
          (targetRightSupport tested).trans
            (sourceRightSupport tested).symm
  · intro targetSkeletonLeft targetSkeletonRight separator cut
    obtain
      ⟨targetLeft, targetRight, targetCut,
        targetLeftSupport, targetRightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_reflectExactCut cut
    obtain
      ⟨sourceLeft, sourceRight, sourceCut,
        sourceLeftSupport, sourceRightSupport⟩ :=
      backward targetCut
    obtain
      ⟨sourceSkeletonLeft, sourceSkeletonRight,
        sourceSkeletonCut, sourceSkeletonLeftSupport,
        sourceSkeletonRightSupport⟩ :=
      S5_441.exactCutSupportSkeleton_transportExactCut
        sourceCut
    refine
      ⟨sourceSkeletonLeft, sourceSkeletonRight,
        sourceSkeletonCut, ?_, ?_⟩
    · intro tested
      exact
        (sourceSkeletonLeftSupport tested).trans <|
          (sourceLeftSupport tested).trans
            (targetLeftSupport tested).symm
    · intro tested
      exact
        (sourceSkeletonRightSupport tested).trans <|
          (sourceRightSupport tested).trans
            (targetRightSupport tested).symm

private theorem head_not_mem_tail_of_count_one
    {word : Word Nat}
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  intro member
  have positive : 0 < word.tail.count word.head :=
    List.count_pos_iff.mpr member
  simp only [Word.toList, List.count_cons_self] at countOne
  omega

private theorem headCountOne_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right)
    (countOne : left.toList.count left.head = 1) :
    right.toList.count right.head = 1 := by
  have initialCut :
      UniqueSeparatorFourExactCut
        left.toList [] left.head left.tail := by
    refine ⟨?_, countOne, ?_⟩
    · cases left
      rfl
    · intro tested member
      simp at member
  obtain
    ⟨targetLeft, targetRight, targetCut, _, _⟩ :=
    S5_441Invariant.SameExactCutSignature.transport
      same.exactCuts initialCut
  simpa [same.first] using targetCut.2.1

private theorem headCountOne_iff_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 :=
  ⟨headCountOne_of_sameSignature same,
    headCountOne_of_sameSignature
      (S5_787Invariant.SameSeparatorFirstSignature.symm same)⟩

private theorem tailSupport_iff_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right)
    (leftCount : left.toList.count left.head = 1)
    (rightCount : right.toList.count right.head = 1) :
    ∀ tested,
      tested ∈ left.tail ↔ tested ∈ right.tail := by
  intro tested
  have leftHeadAbsent :=
    head_not_mem_tail_of_count_one leftCount
  have rightHeadAbsent :=
    head_not_mem_tail_of_count_one rightCount
  by_cases testedEq : tested = left.head
  · subst tested
    constructor
    · intro member
      exact False.elim (leftHeadAbsent member)
    · intro member
      exact False.elim <|
        rightHeadAbsent (by simpa [same.first] using member)
  · have targetNe : tested ≠ right.head := by
      intro equality
      apply testedEq
      exact equality.trans same.first.symm
    simpa [Word.toList, testedEq, targetNe] using
      same.support tested

private theorem tailExactCutTransport
    {source target : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature source target)
    (sourceCount : source.toList.count source.head = 1)
    (targetCount : target.toList.count target.head = 1)
    {left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        source.tail left separator right) :
    ∃ targetLeft targetRight,
      UniqueSeparatorFourExactCut
          target.tail targetLeft separator targetRight ∧
        (∀ tested,
          tested ∈ targetLeft ↔ tested ∈ left) ∧
        (∀ tested,
          tested ∈ targetRight ↔ tested ∈ right) := by
  have sourceHeadAbsent :=
    head_not_mem_tail_of_count_one sourceCount
  have targetHeadAbsent :=
    head_not_mem_tail_of_count_one targetCount
  have separatorMember : separator ∈ source.tail := by
    rw [cut.1]
    exact List.mem_append_right _ (List.Mem.head _)
  have separatorNeSourceHead : separator ≠ source.head := by
    intro equality
    subst separator
    exact sourceHeadAbsent separatorMember
  have prefixDisjointRight :
      UniqueSeparatorFourSupportsDisjoint
        [source.head] right := by
    intro tested prefixMember rightMember
    have testedEq : tested = source.head := by
      simpa using prefixMember
    subst tested
    exact sourceHeadAbsent
      (exactCut_right_mem cut rightMember)
  have wholeCut :
      UniqueSeparatorFourExactCut
        source.toList ([source.head] ++ left)
        separator right := by
    change
      UniqueSeparatorFourExactCut
        ([source.head] ++ source.tail)
        ([source.head] ++ left) separator right
    exact exactCut_addPrefix cut
      (by simp [separatorNeSourceHead])
      prefixDisjointRight
  obtain
    ⟨wholeTargetLeft, targetRight, targetCut,
      targetLeftSupport, targetRightSupport⟩ :=
    S5_441Invariant.SameExactCutSignature.transport
      same.exactCuts wholeCut
  have separatorNeTargetHead : separator ≠ target.head := by
    intro equality
    apply separatorNeSourceHead
    exact equality.trans same.first.symm
  have targetCutWithPrefix :
      UniqueSeparatorFourExactCut
        ([target.head] ++ target.tail)
        wholeTargetLeft separator targetRight := by
    simpa [Word.toList] using targetCut
  obtain ⟨targetLeft, wholeTargetLeftEq, reducedCut⟩ :=
    exactCut_dropPrefix
      (pre := [target.head])
      (letters := target.tail)
      (by simp [separatorNeTargetHead])
      targetCutWithPrefix
  refine
    ⟨targetLeft, targetRight, reducedCut, ?_,
      targetRightSupport⟩
  intro tested
  have sourceLeftHeadAbsent : source.head ∉ left := by
    intro member
    exact sourceHeadAbsent
      (exactCut_left_mem cut member)
  have targetLeftHeadAbsent : target.head ∉ targetLeft := by
    intro member
    exact targetHeadAbsent
      (exactCut_left_mem reducedCut member)
  have wholeSupport := targetLeftSupport tested
  rw [wholeTargetLeftEq] at wholeSupport
  by_cases testedEq : tested = source.head
  · subst tested
    constructor
    · intro member
      exact False.elim <|
        targetLeftHeadAbsent (by simpa [same.first] using member)
    · intro member
      exact False.elim (sourceLeftHeadAbsent member)
  · have targetNe : tested ≠ target.head := by
      intro equality
      apply testedEq
      exact equality.trans same.first.symm
    simpa [testedEq, targetNe] using wholeSupport

private theorem tailSkeleton_eq_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right)
    (leftCount : left.toList.count left.head = 1)
    (rightCount : right.toList.count right.head = 1) :
    S5_441.exactCutSupportSkeleton left.tail =
      S5_441.exactCutSupportSkeleton right.tail := by
  apply exactCutSupportSkeleton_eq_of_listSignature
    (tailSupport_iff_of_sameSignature
      same leftCount rightCount)
  · intro leftPrefix leftSuffix separator cut
    exact
      tailExactCutTransport
        same leftCount rightCount cut
  · intro rightPrefix rightSuffix separator cut
    exact
      tailExactCutTransport
        (S5_787Invariant.SameSeparatorFirstSignature.symm same)
        rightCount leftCount cut

private def separatorFirstNormalList
    (word : Word Nat) : List Nat :=
  if word.toList.count word.head = 1 then
    word.head ::
      uniqueSeparatorCanonicalRender
        (S5_441.exactCutSupportSkeleton word.tail)
  else
    word.head ::
      uniqueSeparatorCanonicalRender
        (S5_441.exactCutSupportSkeleton word.toList)

private theorem separatorFirstNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right) :
    separatorFirstNormalList left =
      separatorFirstNormalList right := by
  have countIff :=
    headCountOne_iff_of_sameSignature same
  by_cases leftCount : left.toList.count left.head = 1
  · have rightCount :
        right.toList.count right.head = 1 :=
      countIff.mp leftCount
    have tailSkeletonEq :=
      tailSkeleton_eq_of_sameSignature
        same leftCount rightCount
    simp only [separatorFirstNormalList, if_pos leftCount,
      if_pos rightCount]
    rw [same.first, tailSkeletonEq]
  · have rightCount :
        right.toList.count right.head ≠ 1 := by
      intro countOne
      exact leftCount (countIff.mpr countOne)
    have skeletonEq :
        S5_441.exactCutSupportSkeleton left.toList =
          S5_441.exactCutSupportSkeleton right.toList :=
      S5_441.exactCutSupportSkeleton_eq_of_sameSupport_sameExactCutSignature
        same.support same.exactCuts
    simp only [separatorFirstNormalList, if_neg leftCount,
      if_neg rightCount]
    rw [same.first, skeletonEq]

private theorem listDerivesDuplicateInitial
    (head : Nat) {tail : List Nat}
    (headInTail : head ∈ tail) :
    S5_107.ListDerives basis
      (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after
  | cons middleHead middleTail =>
      let middle :=
        S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesLeftDuplication
            (Word.singleton head) middle)
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after

private theorem listDerivesSeparatorFirstNormal
    (word : Word Nat) :
    S5_107.ListDerives basis
      word.toList (separatorFirstNormalList word) := by
  cases word with
  | mk head tail =>
      by_cases countOne :
          (Word.mk head tail).toList.count head = 1
      · rw [separatorFirstNormalList, if_pos countOne]
        cases tail with
        | nil =>
            simpa [S5_441.exactCutSupportSkeleton,
              S5_441.exactCutSupportSegments,
              S5_441.exactCutSupportSegment?,
              S5_441.exactCutDecomposition,
              S5_441.exactCutScanner,
              uniqueSeparatorCanonicalRender] using
              S5_107.ListDerives.refl
                (basis := basis) [head]
        | cons tailHead tailTail =>
            let tailWord : Word Nat :=
              ⟨tailHead, tailTail⟩
            have tailDerivation :=
              uniqueSeparatorDerivesExactCutSupportSkeleton
                tailWord
            simpa only [Word.toList_singleton,
              List.singleton_append] using
              (liftUniqueSeparatorListUnderPrefix
                (Word.singleton head) tailDerivation)
      · rw [separatorFirstNormalList, if_neg countOne]
        have headInTail : head ∈ tail := by
          have positive : 0 < tail.count head := by
            simp only [Word.toList,
              List.count_cons_self] at countOne
            omega
          exact List.count_pos_iff.mp positive
        have duplicate :=
          listDerivesDuplicateInitial head headInTail
        have wholeDerivation :=
          uniqueSeparatorDerivesExactCutSupportSkeleton
            (Word.mk head tail)
        exact duplicate.trans <| by
          simpa only [Word.toList_singleton,
            List.singleton_append] using
            (liftUniqueSeparatorListUnderPrefix
              (Word.singleton head) wholeDerivation)

/-- Syntactic completeness of the support/exact-cut/first-letter signature
for the five-law `S5_787` basis. -/
theorem derives_of_sameSeparatorFirstSignature
    {left right : Word Nat}
    (same :
      S5_787Invariant.SameSeparatorFirstSignature left right) :
    Derives basis left right := by
  have leftNormal :=
    listDerivesSeparatorFirstNormal left
  have rightNormal :=
    listDerivesSeparatorFirstNormal right
  have normalEq :=
    separatorFirstNormalList_eq_of_sameSignature same
  have middle :
      S5_107.ListDerives basis
        (separatorFirstNormalList left)
        (separatorFirstNormalList right) := by
    rw [normalEq]
    exact
      S5_107.ListDerives.refl
        (basis := basis) _
  have listDerivation :
      S5_107.ListDerives basis left.toList right.toList :=
    leftNormal.trans <| middle.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord listDerivation

end SemigroupBasis.CoRoots.S5_787
