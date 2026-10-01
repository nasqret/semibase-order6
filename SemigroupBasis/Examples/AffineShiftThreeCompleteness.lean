import SemigroupBasis.Examples.AffineShiftThreeNormalForm
import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_870GapBlocks

namespace SemigroupBasis.Examples

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives affineShiftThreeBasis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private abbrev GapBlock :=
  SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock

/-! ## Guarded permutations -/

private theorem affineShiftThreeListDerivesSwapBothGapsEmpty
    (first second : Nat) :
    ListDerives
      [first, second, second, first]
      [first, second, first, second] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesBinaryResidueOne
          (Word.singleton first) (Word.singleton second)))

private theorem affineShiftThreeListDerivesSwapFirstGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first])
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesTernaryResidueOne
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem affineShiftThreeListDerivesSwapSecondGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first])
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesTernaryResidueTwo
          (Word.singleton first)
          (listWordOfCons gapHead gapTail)
          (Word.singleton second)))

private theorem affineShiftThreeListDerivesSwapBothGapsNonempty
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesGuardedSwap
          (Word.singleton first)
          (listWordOfCons firstGapHead firstGapTail)
          (Word.singleton second)
          (listWordOfCons secondGapHead secondGapTail)))

/-- Swap displayed later copies of two letters. The four branches select the
literal basis law appropriate to the two possibly empty witness gaps. -/
private theorem affineShiftThreeListDerivesSwapDisplayedLater
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.context before after
              (affineShiftThreeListDerivesSwapBothGapsEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.context before after
              (affineShiftThreeListDerivesSwapFirstGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.context before after
              (affineShiftThreeListDerivesSwapSecondGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.context before after
              (affineShiftThreeListDerivesSwapBothGapsNonempty
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

/-- Once both letters occur in the stem, their adjacent later occurrences
may be swapped in either first-occurrence order. -/
private theorem affineShiftThreeListDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, stemSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [stemSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed :=
        affineShiftThreeListDerivesSwapDisplayedLater
          right left before middle leftAfter suffix
      simpa [stemSplit, beforeSplit, List.append_assoc] using displayed
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      have displayed :=
        affineShiftThreeListDerivesSwapDisplayedLater
          left right leftBefore middle tail suffix
      simpa [stemSplit, afterSplit, List.append_assoc] using displayed.symm

/-- Any permutation of a later block is derivable when every block letter
already occurs in the fixed stem. -/
private theorem affineShiftThreeListDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives
      (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen letter (List.Mem.tail head member))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem := sourceSeen first (by simp)
      have secondSeen : second ∈ stem := sourceSeen second (by simp)
      simpa [List.append_assoc] using
        affineShiftThreeListDerivesSwapAfterSeen
          stem (rest ++ suffix) second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter
          ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ## Modulo-three reduction behind a witnessed stem -/

private theorem affineShiftThreeListDerivesDeleteTripleAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives
      (stem ++ [letter, letter, letter] ++ suffix)
      (stem ++ suffix) := by
  obtain ⟨before, after, stemSplit⟩ := List.mem_iff_append.mp seen
  cases after with
  | nil =>
      have core := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesPowerContraction (Word.singleton letter))
      simpa [stemSplit, listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            before suffix core
  | cons gapHead gapTail =>
      have core := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (affineShiftThreeDerivesGuardedTriple
          (Word.singleton letter) (listWordOfCons gapHead gapTail))
      simpa [stemSplit, listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            before suffix core

private theorem affineShiftThreeMem_of_mem_ternaryReduce
    {tested : Nat} {letters : List Nat}
    (member : tested ∈ ternaryReduce letters) :
    tested ∈ letters := by
  apply List.count_pos_iff.mp
  have positive : 0 < (ternaryReduce letters).count tested :=
    List.count_pos_iff.mpr member
  rw [count_ternaryReduce] at positive
  omega

private theorem affineShiftThreeTwoCopiesPerm
    (letter : Nat) (letters : List Nat)
    (count : letters.count letter = 2) :
    letters.Perm
      (letter :: letter :: (letters.erase letter).erase letter) := by
  have member : letter ∈ letters := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase member
  have erasedCount : (letters.erase letter).count letter = 1 := by
    rw [List.count_erase_self, count]
  have erasedMember : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <|
    List.Perm.cons letter (List.perm_cons_erase erasedMember)

/-- Delete all full triples from a block whose letters have already appeared
in the stem. No commutativity law is assumed: guarded swaps first gather the
three selected copies, and the witnessed triple law then deletes them. -/
private theorem affineShiftThreeListDerivesTernaryReduceAfterSeen :
    ∀ (letters stem suffix : List Nat),
      (∀ letter, letter ∈ letters → letter ∈ stem) →
      ListDerives
        (stem ++ letters ++ suffix)
        (stem ++ ternaryReduce letters ++ suffix)
  | [], stem, suffix, _ => by
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := affineShiftThreeBasis) (stem ++ suffix))
  | letter :: rest, stem, suffix, allSeen => by
      have letterSeen : letter ∈ stem :=
        allSeen letter (List.Mem.head rest)
      have restSeen : ∀ tested, tested ∈ rest → tested ∈ stem := by
        intro tested member
        exact allSeen tested (List.Mem.tail letter member)
      have tailDerivation :=
        affineShiftThreeListDerivesTernaryReduceAfterSeen
          rest (stem ++ [letter]) suffix (by
            intro tested member
            exact List.mem_append.mpr (Or.inl (restSeen tested member)))
      have normalizedTail :
          ListDerives
            (stem ++ (letter :: rest) ++ suffix)
            (stem ++ (letter :: ternaryReduce rest) ++ suffix) := by
        simpa [List.append_assoc] using tailDerivation
      by_cases short : (ternaryReduce rest).count letter < 2
      · simpa [ternaryReduce, short, List.append_assoc] using normalizedTail
      · have bounded : (ternaryReduce rest).count letter < 3 := by
          rw [count_ternaryReduce]
          exact Nat.mod_lt _ (by decide)
        have exactlyTwo : (ternaryReduce rest).count letter = 2 := by
          omega
        let remainder :=
          ((ternaryReduce rest).erase letter).erase letter
        have restPermutation :=
          affineShiftThreeTwoCopiesPerm
            letter (ternaryReduce rest) exactlyTwo
        have groupedPermutation :
            (letter :: ternaryReduce rest).Perm
              ([letter, letter, letter] ++ remainder) := by
          simpa [remainder] using List.Perm.cons letter restPermutation
        have reducedSeen :
            ∀ tested, tested ∈ letter :: ternaryReduce rest →
              tested ∈ stem := by
          intro tested member
          rcases List.mem_cons.mp member with rfl | reducedMember
          · exact letterSeen
          · exact restSeen tested <|
              affineShiftThreeMem_of_mem_ternaryReduce reducedMember
        have grouped :=
          affineShiftThreeListDerivesPermuteAfterSeen
            stem suffix reducedSeen groupedPermutation
        have deleted :=
          affineShiftThreeListDerivesDeleteTripleAfterSeen
            stem (remainder ++ suffix) letter letterSeen
        have result := normalizedTail.trans <| grouped.trans <| by
          simpa [List.append_assoc] using deleted
        simpa [ternaryReduce, short, remainder,
          List.append_assoc] using result

/-! ## Blockwise replay -/

/-- Two first-occurrence decompositions correspond when their markers agree
and each pair of gaps has the same multiplicity vector modulo three. -/
private inductive AffineShiftThreeCorrespondingGapBlocks :
    List GapBlock → List GapBlock → Prop
  | nil : AffineShiftThreeCorrespondingGapBlocks [] []
  | cons {leftBlock rightBlock : GapBlock}
      {leftRest rightRest : List GapBlock}
      (marker : leftBlock.marker = rightBlock.marker)
      (seconds : ∀ tested,
        affineShiftThreeCountResidue tested leftBlock.seconds =
          affineShiftThreeCountResidue tested rightBlock.seconds)
      (rest : AffineShiftThreeCorrespondingGapBlocks leftRest rightRest) :
      AffineShiftThreeCorrespondingGapBlocks
        (leftBlock :: leftRest) (rightBlock :: rightRest)

private theorem affineShiftThreeTernaryReducePerm_of_residueEq
    {left right : List Nat}
    (sameResidue : ∀ tested,
      affineShiftThreeCountResidue tested left =
        affineShiftThreeCountResidue tested right) :
    (ternaryReduce left).Perm (ternaryReduce right) := by
  apply ternaryReduce_perm_of_mod_eq
  intro tested
  have equal := sameResidue tested
  rw [affineShiftThreeCountResidue_eq_natResidue,
    affineShiftThreeCountResidue_eq_natResidue] at equal
  exact Fin.mk.inj equal

private theorem affineShiftThreeListDerivesCorrespondingGapBlocks
    {seen : List Nat} {left right : List GapBlock}
    (corresponding : AffineShiftThreeCorrespondingGapBlocks left right)
    (leftFormed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen left)
    (rightFormed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen right)
    (stem : List Nat)
    (seenInStem : ∀ letter, letter ∈ seen → letter ∈ stem) :
    ListDerives
      (stem ++ SemigroupBasis.CoRoots.S5_870.renderGapBlocks left)
      (stem ++ SemigroupBasis.CoRoots.S5_870.renderGapBlocks right) := by
  induction corresponding generalizing seen stem with
  | nil =>
      simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := affineShiftThreeBasis) stem)
  | @cons leftBlock rightBlock leftRest rightRest
      markerEq secondsEq restCorrespondence induction =>
      cases leftFormed with
      | cons _ _ _ leftFresh leftSecondsSeen leftTailFormed =>
        cases rightFormed with
        | cons _ _ _ rightFresh rightSecondsSeen rightTailFormed =>
          have rightTailFormed' :
              SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
                (leftBlock.marker :: seen) rightRest := by
            simpa [markerEq] using rightTailFormed
          let currentStem := stem ++ [leftBlock.marker]
          have leftSecondsInStem :
              ∀ letter, letter ∈ leftBlock.seconds →
                letter ∈ currentStem := by
            intro letter member
            have known := leftSecondsSeen letter member
            rcases List.mem_cons.mp known with atMarker | inSeen
            · subst letter
              simp [currentStem]
            · exact List.mem_append.mpr <| Or.inl <|
                seenInStem letter inSeen
          have rightSecondsInStem :
              ∀ letter, letter ∈ rightBlock.seconds →
                letter ∈ currentStem := by
            intro letter member
            have known := rightSecondsSeen letter member
            rcases List.mem_cons.mp known with atMarker | inSeen
            · rw [← markerEq] at atMarker
              subst letter
              simp [currentStem]
            · exact List.mem_append.mpr <| Or.inl <|
                seenInStem letter inSeen
          have leftReduced :=
            affineShiftThreeListDerivesTernaryReduceAfterSeen
              leftBlock.seconds currentStem
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks leftRest)
              leftSecondsInStem
          have reducedPermutation :
              (ternaryReduce leftBlock.seconds).Perm
                (ternaryReduce rightBlock.seconds) :=
            affineShiftThreeTernaryReducePerm_of_residueEq secondsEq
          have reducedLeftInStem :
              ∀ letter, letter ∈ ternaryReduce leftBlock.seconds →
                letter ∈ currentStem := by
            intro letter member
            exact leftSecondsInStem letter <|
              affineShiftThreeMem_of_mem_ternaryReduce member
          have reordered :=
            affineShiftThreeListDerivesPermuteAfterSeen
              currentStem
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks leftRest)
              reducedLeftInStem reducedPermutation
          have rightReduced :=
            affineShiftThreeListDerivesTernaryReduceAfterSeen
              rightBlock.seconds currentStem
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks leftRest)
              rightSecondsInStem
          have currentMove :=
            leftReduced.trans <| reordered.trans rightReduced.symm
          have nextSeenInStem :
              ∀ letter, letter ∈ leftBlock.marker :: seen →
                letter ∈
                  currentStem ++ rightBlock.seconds := by
            intro letter member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst letter
              exact List.mem_append.mpr <| Or.inl <| by
                simp [currentStem]
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInStem letter inSeen
          have recurse := induction
            leftTailFormed rightTailFormed'
            (currentStem ++ rightBlock.seconds) nextSeenInStem
          simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
            currentStem, markerEq, List.append_assoc] using
              currentMove.trans recurse

/-! ## Recovering block residues from the canonical invariant -/

private theorem affineShiftThreeFirstOccurrenceScansAgree :
    ∀ (frontSeen backSeen letters : List Nat),
      (∀ tested, tested ∈ frontSeen ↔ tested ∈ backSeen) →
      SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceAux
          frontSeen letters =
        affineShiftThreeFirstOccurrencesFrom backSeen letters
  | _, _, [], _ => rfl
  | frontSeen, backSeen, letter :: rest, sameSeen => by
      by_cases frontMember : letter ∈ frontSeen
      · have backMember : letter ∈ backSeen :=
          (sameSeen letter).mp frontMember
        simpa [SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceAux,
          affineShiftThreeFirstOccurrencesFrom, frontMember, backMember] using
            affineShiftThreeFirstOccurrenceScansAgree
              frontSeen backSeen rest sameSeen
      · have backAbsent : letter ∉ backSeen := by
          intro member
          exact frontMember ((sameSeen letter).mpr member)
        have nextSeen :
            ∀ tested,
              tested ∈ letter :: frontSeen ↔
                tested ∈ backSeen ++ [letter] := by
          intro tested
          constructor
          · intro member
            rcases List.mem_cons.mp member with atLetter | inSeen
            · subst tested
              simp
            · exact List.mem_append.mpr <| Or.inl <|
                (sameSeen tested).mp inSeen
          · intro member
            rcases List.mem_append.mp member with inSeen | atLetter
            · exact List.Mem.tail letter <| (sameSeen tested).mpr inSeen
            · have equal : tested = letter := List.mem_singleton.mp atLetter
              subst tested
              exact List.Mem.head _
        simpa [SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceAux,
          affineShiftThreeFirstOccurrencesFrom, frontMember, backAbsent] using
            congrArg (List.cons letter) <|
              affineShiftThreeFirstOccurrenceScansAgree
                (letter :: frontSeen) (backSeen ++ [letter]) rest nextSeen

private theorem affineShiftThreeFirstOccurrenceSequenceList_eq
    (letters : List Nat) :
    SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceList letters =
      affineShiftThreeFirstOccurrenceOrderList letters := by
  unfold SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceList
  unfold affineShiftThreeFirstOccurrenceOrderList
  exact affineShiftThreeFirstOccurrenceScansAgree [] [] letters (by simp)

private theorem affineShiftThreePrefixBeforeNextGapBlock
    {seen stem : List Nat} {block next : GapBlock}
    {rest : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        seen (block :: next :: rest))
    (stemSupport : ∀ letter, letter ∈ stem → letter ∈ seen) :
    affineShiftThreePrefixBeforeFirst next.marker
        (stem ++
          SemigroupBasis.CoRoots.S5_870.renderGapBlocks
            (block :: next :: rest)) =
      stem ++ [block.marker] ++ block.seconds := by
  cases formed with
  | cons _ _ _ blockFresh blockSecondsSeen tailFormed =>
      cases tailFormed with
      | cons _ _ _ nextFresh nextSecondsSeen restFormed =>
          have nextAbsent :
              next.marker ∉ stem ++ [block.marker] ++ block.seconds := by
            intro member
            rcases List.mem_append.mp member with inStemMarker | inSeconds
            · rcases List.mem_append.mp inStemMarker with inStem | atMarker
              · exact nextFresh <| List.Mem.tail block.marker <|
                  stemSupport next.marker inStem
              · have equal : next.marker = block.marker :=
                  List.mem_singleton.mp atMarker
                exact nextFresh <| equal ▸ List.Mem.head seen
            · exact nextFresh <| blockSecondsSeen next.marker inSeconds
          have hit :=
            affineShiftThreePrefixBeforeFirst_append_hit next.marker
              (stem ++ [block.marker] ++ block.seconds)
              (next.seconds ++
                SemigroupBasis.CoRoots.S5_870.renderGapBlocks rest)
              nextAbsent
          simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
            List.append_assoc] using hit

private theorem affineShiftThreeFinThreeAddLeftCancel
    (before left right : Fin 3)
    (equal : before + left = before + right) :
    left = right := by
  decide +revert

private theorem affineShiftThreeGapResidue_eq_of_boundary
    {leftStem rightStem leftSeconds rightSeconds : List Nat}
    {leftMarker rightMarker tested : Nat}
    (stemEq :
      affineShiftThreeCountResidue tested leftStem =
        affineShiftThreeCountResidue tested rightStem)
    (markerEq : leftMarker = rightMarker)
    (boundaryEq :
      affineShiftThreeCountResidue tested
          (leftStem ++ [leftMarker] ++ leftSeconds) =
        affineShiftThreeCountResidue tested
          (rightStem ++ [rightMarker] ++ rightSeconds)) :
    affineShiftThreeCountResidue tested leftSeconds =
      affineShiftThreeCountResidue tested rightSeconds := by
  have beforeEq :
      affineShiftThreeCountResidue tested (leftStem ++ [leftMarker]) =
        affineShiftThreeCountResidue tested (rightStem ++ [rightMarker]) := by
    subst rightMarker
    rw [affineShiftThreeCountResidue_append,
      affineShiftThreeCountResidue_append, stemEq]
  have leftExpanded :=
    affineShiftThreeCountResidue_append tested
      (leftStem ++ [leftMarker]) leftSeconds
  have rightExpanded :=
    affineShiftThreeCountResidue_append tested
      (rightStem ++ [rightMarker]) rightSeconds
  rw [leftExpanded, rightExpanded, beforeEq] at boundaryEq
  exact affineShiftThreeFinThreeAddLeftCancel _ _ _ boundaryEq

private theorem affineShiftThreeCorrespondingGapBlocksOfProfiles :
    ∀ {seen : List Nat} {left right : List GapBlock}
      (leftStem rightStem : List Nat),
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen left →
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen right →
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers left =
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers right →
      (∀ letter, letter ∈ leftStem → letter ∈ seen) →
      (∀ letter, letter ∈ rightStem → letter ∈ seen) →
      (∀ tested,
        affineShiftThreeCountResidue tested leftStem =
          affineShiftThreeCountResidue tested rightStem) →
      (∀ selected tested,
        affineShiftThreeCountResidue tested
            (affineShiftThreePrefixBeforeFirst selected
              (leftStem ++
                SemigroupBasis.CoRoots.S5_870.renderGapBlocks left)) =
          affineShiftThreeCountResidue tested
            (affineShiftThreePrefixBeforeFirst selected
              (rightStem ++
                SemigroupBasis.CoRoots.S5_870.renderGapBlocks right))) →
      (∀ tested,
        affineShiftThreeCountResidue tested
            (leftStem ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks left) =
          affineShiftThreeCountResidue tested
            (rightStem ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks right)) →
      AffineShiftThreeCorrespondingGapBlocks left right
  | _, [], [], leftStem, rightStem, _, _, _, _, _, _, _, _ =>
      AffineShiftThreeCorrespondingGapBlocks.nil
  | _, [], _ :: _, leftStem, rightStem, _, _, markers, _, _, _, _, _ => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] at markers
  | _, _ :: _, [], leftStem, rightStem, _, _, markers, _, _, _, _, _ => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] at markers
  | seen, leftBlock :: leftRest, rightBlock :: rightRest,
      leftStem, rightStem, leftFormed, rightFormed, markers,
      leftStemSupport, rightStemSupport, stemResidues,
      prefixResidues, totalResidues => by
      have leftWholeFormed := leftFormed
      have rightWholeFormed := rightFormed
      cases leftFormed with
      | cons _ _ _ leftFresh leftSecondsSeen leftTailFormed =>
        cases rightFormed with
        | cons _ _ _ rightFresh rightSecondsSeen rightTailFormed =>
          simp only [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
            List.map_cons]
              at markers
          injection markers with markerEq tailMarkers
          have rightTailFormed' :
              SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
                (leftBlock.marker :: seen) rightRest := by
            simpa [markerEq] using rightTailFormed
          have boundaryResidues :
              ∀ tested,
                affineShiftThreeCountResidue tested
                    (leftStem ++ [leftBlock.marker] ++ leftBlock.seconds) =
                  affineShiftThreeCountResidue tested
                    (rightStem ++ [rightBlock.marker] ++
                      rightBlock.seconds) := by
            intro tested
            cases leftRest with
            | nil =>
                cases rightRest with
                | nil =>
                    simpa [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
                      List.append_assoc] using totalResidues tested
                | cons rightNext rightTail =>
                    simp at tailMarkers
            | cons leftNext leftTail =>
                cases rightRest with
                | nil =>
                    simp at tailMarkers
                | cons rightNext rightTail =>
                    have nextMarkerEq :
                        leftNext.marker = rightNext.marker := by
                      simpa [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers]
                        using congrArg List.head? tailMarkers
                    have profile := prefixResidues leftNext.marker tested
                    have leftCut :=
                      affineShiftThreePrefixBeforeNextGapBlock
                        leftWholeFormed leftStemSupport
                    have rightCut :=
                      affineShiftThreePrefixBeforeNextGapBlock
                        rightWholeFormed rightStemSupport
                    rw [leftCut] at profile
                    rw [nextMarkerEq, rightCut] at profile
                    exact profile
          have secondsResidues :
              ∀ tested,
                affineShiftThreeCountResidue tested leftBlock.seconds =
                  affineShiftThreeCountResidue tested rightBlock.seconds := by
            intro tested
            exact affineShiftThreeGapResidue_eq_of_boundary
              (stemResidues tested) markerEq (boundaryResidues tested)
          let nextLeftStem :=
            leftStem ++ [leftBlock.marker] ++ leftBlock.seconds
          let nextRightStem :=
            rightStem ++ [rightBlock.marker] ++ rightBlock.seconds
          have nextLeftSupport :
              ∀ letter, letter ∈ nextLeftStem →
                letter ∈ leftBlock.marker :: seen := by
            intro letter member
            rcases List.mem_append.mp member with inStemMarker | inSeconds
            · rcases List.mem_append.mp inStemMarker with inStem | atMarker
              · exact List.Mem.tail leftBlock.marker <|
                  leftStemSupport letter inStem
              · have equal : letter = leftBlock.marker :=
                  List.mem_singleton.mp atMarker
                subst letter
                exact List.Mem.head seen
            · exact leftSecondsSeen letter inSeconds
          have nextRightSupport :
              ∀ letter, letter ∈ nextRightStem →
                letter ∈ leftBlock.marker :: seen := by
            intro letter member
            rcases List.mem_append.mp member with inStemMarker | inSeconds
            · rcases List.mem_append.mp inStemMarker with inStem | atMarker
              · exact List.Mem.tail leftBlock.marker <|
                  rightStemSupport letter inStem
              · have atRight : letter = rightBlock.marker :=
                  List.mem_singleton.mp atMarker
                have atLeft : letter = leftBlock.marker :=
                  atRight.trans markerEq.symm
                exact atLeft.symm ▸ List.Mem.head seen
            · have known := rightSecondsSeen letter inSeconds
              simpa [markerEq] using known
          have nextPrefixResidues :
              ∀ selected tested,
                affineShiftThreeCountResidue tested
                    (affineShiftThreePrefixBeforeFirst selected
                      (nextLeftStem ++
                        SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                          leftRest)) =
                  affineShiftThreeCountResidue tested
                    (affineShiftThreePrefixBeforeFirst selected
                      (nextRightStem ++
                        SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                          rightRest)) := by
            intro selected tested
            simpa [nextLeftStem, nextRightStem,
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              List.append_assoc] using prefixResidues selected tested
          have nextTotalResidues :
              ∀ tested,
                affineShiftThreeCountResidue tested
                    (nextLeftStem ++
                      SemigroupBasis.CoRoots.S5_870.renderGapBlocks leftRest) =
                  affineShiftThreeCountResidue tested
                    (nextRightStem ++
                      SemigroupBasis.CoRoots.S5_870.renderGapBlocks rightRest) := by
            intro tested
            simpa [nextLeftStem, nextRightStem,
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              List.append_assoc] using totalResidues tested
          have restCorresponding :=
            affineShiftThreeCorrespondingGapBlocksOfProfiles
              nextLeftStem nextRightStem leftTailFormed rightTailFormed'
              tailMarkers nextLeftSupport nextRightSupport boundaryResidues
              nextPrefixResidues nextTotalResidues
          exact AffineShiftThreeCorrespondingGapBlocks.cons
            markerEq secondsResidues restCorresponding

private theorem affineShiftThreeCorrespondingGapBlocksOfInvariants
    (left right : Word Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrder left =
        affineShiftThreeFirstOccurrenceOrder right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right) :
    AffineShiftThreeCorrespondingGapBlocks
      (SemigroupBasis.CoRoots.S5_870.gapBlocksList left.toList)
      (SemigroupBasis.CoRoots.S5_870.gapBlocksList right.toList) := by
  apply affineShiftThreeCorrespondingGapBlocksOfProfiles
    ([] : List Nat) ([] : List Nat)
  · exact SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed _
  · exact SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed _
  · calc
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
          (SemigroupBasis.CoRoots.S5_870.gapBlocksList left.toList) =
          SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceList
            left.toList :=
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers_gapBlocksList _
      _ = affineShiftThreeFirstOccurrenceOrder left := by
        simpa [affineShiftThreeFirstOccurrenceOrder] using
          affineShiftThreeFirstOccurrenceSequenceList_eq left.toList
      _ = affineShiftThreeFirstOccurrenceOrder right := sameOrder
      _ = SemigroupBasis.CoRoots.S5_870.firstOccurrenceSequenceList
            right.toList := by
        simpa [affineShiftThreeFirstOccurrenceOrder] using
          (affineShiftThreeFirstOccurrenceSequenceList_eq right.toList).symm
      _ = SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
          (SemigroupBasis.CoRoots.S5_870.gapBlocksList right.toList) :=
        (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers_gapBlocksList _).symm
  · simp
  · simp
  · simp
  · intro selected tested
    simpa [affineShiftThreeWordPrefixResidue,
      SemigroupBasis.CoRoots.S5_870.render_gapBlocksList] using
        samePrefix selected tested
  · intro tested
    simpa [affineShiftThreeWordTotalResidue,
      SemigroupBasis.CoRoots.S5_870.render_gapBlocksList] using
        sameTotal tested

/-- The three semantic invariants are also a complete syntactic invariant for
the six displayed laws. This is the reusable derivational core of the affine
order-six endpoint. -/
theorem affineShiftThreeDerivesOfInvariants
    (left right : Word Nat)
    (sameOrder :
      affineShiftThreeFirstOccurrenceOrder left =
        affineShiftThreeFirstOccurrenceOrder right)
    (sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested left =
        affineShiftThreeWordTotalResidue tested right)
    (samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested left =
        affineShiftThreeWordPrefixResidue selected tested right) :
    Derives affineShiftThreeBasis left right := by
  have corresponding :=
    affineShiftThreeCorrespondingGapBlocksOfInvariants
      left right sameOrder sameTotal samePrefix
  have listed :=
    affineShiftThreeListDerivesCorrespondingGapBlocks corresponding
      (SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed left.toList)
      (SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed right.toList)
      [] (by simp)
  have listed' : ListDerives left.toList right.toList := by
    simpa [SemigroupBasis.CoRoots.S5_870.render_gapBlocksList] using listed
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listed'

/-- Every word derives to the existing literal canonical normal word. -/
theorem affineShiftThreeDerivesNormal (word : Word Nat) :
    Derives affineShiftThreeBasis word
      (affineShiftThreeNormalWord word) := by
  apply affineShiftThreeDerivesOfInvariants
  · exact (affineShiftThreeNormalWord_firstOccurrenceOrder word).symm
  · intro tested
    exact (affineShiftThreeNormalWord_totalResidue word tested).symm
  · intro selected tested
    exact
      (affineShiftThreeNormalWord_prefixResidue word selected tested).symm

/-! ## Semantic recovery of first-occurrence order -/

private def AffineShiftThreeListBefore
    (first second : Nat) : List Nat → Prop
  | [] => False
  | letter :: rest =>
      (letter = first ∧ second ∈ rest) ∨
        AffineShiftThreeListBefore first second rest

private theorem AffineShiftThreeListBefore.left_mem
    {first second : Nat} :
    ∀ {letters : List Nat},
      AffineShiftThreeListBefore first second letters →
        first ∈ letters
  | [], before => by
      simp [AffineShiftThreeListBefore] at before
  | letter :: rest, before => by
      rcases before with head | tail
      · rcases head with ⟨rfl, _⟩
        simp
      · exact List.mem_cons_of_mem letter
          (AffineShiftThreeListBefore.left_mem tail)

private theorem AffineShiftThreeListBefore.right_mem
    {first second : Nat} :
    ∀ {letters : List Nat},
      AffineShiftThreeListBefore first second letters →
        second ∈ letters
  | [], before => by
      simp [AffineShiftThreeListBefore] at before
  | letter :: rest, before => by
      rcases before with head | tail
      · exact List.mem_cons_of_mem letter head.2
      · exact List.mem_cons_of_mem letter
          (AffineShiftThreeListBefore.right_mem tail)

private theorem AffineShiftThreeListBefore.asymm_of_nodup
    {first second : Nat} :
    ∀ {letters : List Nat},
      letters.Nodup →
      AffineShiftThreeListBefore first second letters →
        ¬ AffineShiftThreeListBefore second first letters
  | [], _, before => by
      simp [AffineShiftThreeListBefore] at before
  | letter :: rest, nodup, forward => by
      have data := List.nodup_cons.mp nodup
      intro reverse
      rcases forward with forwardHead | forwardTail
      · rcases forwardHead with ⟨rfl, secondInRest⟩
        rcases reverse with reverseHead | reverseTail
        · exact data.1 reverseHead.2
        · exact data.1
            (AffineShiftThreeListBefore.right_mem reverseTail)
      · rcases reverse with reverseHead | reverseTail
        · rcases reverseHead with ⟨rfl, firstInRest⟩
          exact data.1
            (AffineShiftThreeListBefore.right_mem forwardTail)
        · exact AffineShiftThreeListBefore.asymm_of_nodup
            data.2 forwardTail reverseTail

private theorem affineShiftThreeListBefore_total_of_nodup
    {first second : Nat} {letters : List Nat}
    (nodup : letters.Nodup) (different : first ≠ second)
    (firstMember : first ∈ letters) (secondMember : second ∈ letters) :
    AffineShiftThreeListBefore first second letters ∨
      AffineShiftThreeListBefore second first letters := by
  induction letters with
  | nil => simp at firstMember
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      by_cases atFirst : letter = first
      · subst letter
        have secondInRest : second ∈ rest := by
          simpa [Ne.symm different] using secondMember
        exact Or.inl <| Or.inl ⟨rfl, secondInRest⟩
      · by_cases atSecond : letter = second
        · subst letter
          have firstInRest : first ∈ rest := by
            simpa [different] using firstMember
          exact Or.inr <| Or.inl ⟨rfl, firstInRest⟩
        · have firstInRest : first ∈ rest := by
            simpa [Ne.symm atFirst] using firstMember
          have secondInRest : second ∈ rest := by
            simpa [Ne.symm atSecond] using secondMember
          rcases induction data.2 firstInRest secondInRest with
              forward | reverse
          · exact Or.inl (Or.inr forward)
          · exact Or.inr (Or.inr reverse)

private theorem affineShiftThreeNodupList_eq_of_order
    : ∀ (left right : List Nat),
      left.Nodup → right.Nodup →
      (∀ tested, tested ∈ left ↔ tested ∈ right) →
      (∀ first second,
        AffineShiftThreeListBefore first second left ↔
          AffineShiftThreeListBefore first second right) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], rightHead :: rightTail, _, _, sameMembers, _ => by
      have member := (sameMembers rightHead).mpr (List.Mem.head rightTail)
      simp at member
  | leftHead :: leftTail, [], _, _, sameMembers, _ => by
      have member := (sameMembers leftHead).mp (List.Mem.head leftTail)
      simp at member
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameOrder => by
      have leftData := List.nodup_cons.mp leftNodup
      have rightData := List.nodup_cons.mp rightNodup
      have headsEqual : leftHead = rightHead := by
        by_cases equal : leftHead = rightHead
        · exact equal
        · have rightInLeft : rightHead ∈ leftHead :: leftTail :=
            (sameMembers rightHead).mpr (List.Mem.head rightTail)
          have leftInRight : leftHead ∈ rightHead :: rightTail :=
            (sameMembers leftHead).mp (List.Mem.head leftTail)
          have rightInLeftTail : rightHead ∈ leftTail := by
            simpa [Ne.symm equal] using rightInLeft
          have leftInRightTail : leftHead ∈ rightTail := by
            simpa [equal] using leftInRight
          have forward :
              AffineShiftThreeListBefore leftHead rightHead
                (leftHead :: leftTail) :=
            Or.inl ⟨rfl, rightInLeftTail⟩
          have transported := (sameOrder leftHead rightHead).mp forward
          have reverse :
              AffineShiftThreeListBefore rightHead leftHead
                (rightHead :: rightTail) :=
            Or.inl ⟨rfl, leftInRightTail⟩
          exact False.elim <|
            (AffineShiftThreeListBefore.asymm_of_nodup
              rightNodup transported) reverse
      subst rightHead
      apply congrArg (List.cons leftHead)
      apply affineShiftThreeNodupList_eq_of_order
        leftTail rightTail leftData.2 rightData.2
      · intro tested
        by_cases atHead : tested = leftHead
        · subst tested
          simp [leftData.1, rightData.1]
        · simpa [atHead] using sameMembers tested
      · intro first second
        constructor
        · intro before
          have transported :=
            (sameOrder first second).mp (Or.inr before)
          rcases transported with atHead | inTail
          · have firstInTail := AffineShiftThreeListBefore.left_mem before
            exact False.elim
              (leftData.1 (atHead.1.symm ▸ firstInTail))
          · exact inTail
        · intro before
          have transported :=
            (sameOrder first second).mpr (Or.inr before)
          rcases transported with atHead | inTail
          · have firstInTail := AffineShiftThreeListBefore.left_mem before
            exact False.elim
              (rightData.1 (atHead.1.symm ▸ firstInTail))
          · exact inTail

private def affineShiftThreeOrderValuation
    (first second : Nat) (letter : Nat) : Fin 6 :=
  if letter = first then affineShiftThreeIdealResidue 0
  else if letter = second then affineShiftThreeIdealResidue 1
  else affineShiftThreeUnitResidue 0

private theorem affineShiftThreeOrderValuation_first
    (first second : Nat) :
    affineShiftThreeOrderValuation first second first =
      affineShiftThreeIdealResidue 0 := by
  simp [affineShiftThreeOrderValuation]

private theorem affineShiftThreeOrderValuation_second
    {first second : Nat} (different : first ≠ second) :
    affineShiftThreeOrderValuation first second second =
      affineShiftThreeIdealResidue 1 := by
  simp [affineShiftThreeOrderValuation, Ne.symm different]

private theorem affineShiftThreeOrderValuation_other
    {first second letter : Nat}
    (notFirst : letter ≠ first) (notSecond : letter ≠ second) :
    affineShiftThreeOrderValuation first second letter =
      affineShiftThreeUnitResidue 0 := by
  simp [affineShiftThreeOrderValuation, notFirst, notSecond]

private theorem affineShiftThreeEvalList_of_listBefore
    (valuation : Nat → Fin 6) (first second : Nat) (residue : Fin 3)
    (firstIdeal : valuation first = affineShiftThreeIdealResidue residue)
    (otherUnit : ∀ letter, letter ≠ first → letter ≠ second →
      valuation letter = affineShiftThreeUnitResidue 0) :
    ∀ {letters : List Nat},
      letters.Nodup →
      AffineShiftThreeListBefore first second letters →
      affineShiftThreeEvalList valuation letters =
        affineShiftThreeIdealResidue residue
  | [], _, before => by
      simp [AffineShiftThreeListBefore] at before
  | letter :: rest, nodup, before => by
      have data := List.nodup_cons.mp nodup
      rcases before with atHead | inTail
      · have equal := atHead.1
        subst letter
        rw [affineShiftThreeEvalList_cons, firstIdeal]
        exact affineShiftThreeMul_ideal_left residue _
      · have firstInTail := AffineShiftThreeListBefore.left_mem inTail
        have secondInTail := AffineShiftThreeListBefore.right_mem inTail
        have notFirst : letter ≠ first := by
          intro equal
          subst letter
          exact data.1 firstInTail
        have notSecond : letter ≠ second := by
          intro equal
          subst letter
          exact data.1 secondInTail
        rw [affineShiftThreeEvalList_cons,
          otherUnit letter notFirst notSecond,
          affineShiftThreeMul_identity_left]
        exact affineShiftThreeEvalList_of_listBefore
          valuation first second residue firstIdeal otherUnit data.2 inTail

private theorem affineShiftThreeClassify_idealResidue
    (residue : Fin 3) :
    affineShiftThreeClassify (affineShiftThreeIdealResidue residue) =
      AffineShiftThreeValue.ideal residue := by
  change affineShiftThreeClassify
      (affineShiftThreeReconstruct (.ideal residue)) = .ideal residue
  exact affineShiftThreeClassify_reconstruct (.ideal residue)

private theorem affineShiftThreeClassify_unitResidue
    (residue : Fin 3) :
    affineShiftThreeClassify (affineShiftThreeUnitResidue residue) =
      AffineShiftThreeValue.unit residue := by
  change affineShiftThreeClassify
      (affineShiftThreeReconstruct (.unit residue)) = .unit residue
  exact affineShiftThreeClassify_reconstruct (.unit residue)

private theorem affineShiftThreeOrderValuation_unitPart_zero
    (first second letter : Nat) :
    affineShiftThreeUnitPart
        (affineShiftThreeOrderValuation first second) letter = 0 := by
  unfold affineShiftThreeUnitPart
  by_cases atFirst : letter = first
  · subst letter
    rw [affineShiftThreeOrderValuation_first]
    rw [affineShiftThreeClassify_idealResidue]
  · by_cases atSecond : letter = second
    · subst letter
      rw [affineShiftThreeOrderValuation_second (Ne.symm atFirst)]
      rw [affineShiftThreeClassify_idealResidue]
    · rw [affineShiftThreeOrderValuation_other atFirst atSecond]
      rw [affineShiftThreeClassify_unitResidue]

private theorem affineShiftThreeOrderValuation_residueSum_zero
    (first second : Nat) :
    ∀ letters : List Nat,
      affineShiftThreeResidueSum
          (affineShiftThreeUnitPart
            (affineShiftThreeOrderValuation first second)) letters = 0
  | [] => rfl
  | letter :: rest => by
      rw [affineShiftThreeResidueSum,
        affineShiftThreeOrderValuation_unitPart_zero,
        affineShiftThreeOrderValuation_residueSum_zero]
      rfl

private theorem affineShiftThreeOrderValuation_firstOccurrenceOrder
    (first second : Nat) (letters : List Nat) :
    affineShiftThreeEvalList
        (affineShiftThreeOrderValuation first second)
        (affineShiftThreeFirstOccurrenceOrderList letters) =
      affineShiftThreeEvalList
        (affineShiftThreeOrderValuation first second) letters := by
  rw [affineShiftThreeEvalList_firstIdeal_formula,
    affineShiftThreeEvalList_firstIdeal_formula,
    affineShiftThreeFirstIdeal_firstOccurrenceOrder]
  cases firstIdeal :
      affineShiftThreeFirstIdeal
        (affineShiftThreeOrderValuation first second) letters with
  | none =>
      simp [affineShiftThreeOrderValuation_residueSum_zero]
  | some hit =>
      rcases hit with ⟨selected, residue⟩
      simp [affineShiftThreeOrderValuation_residueSum_zero]

private theorem affineShiftThreeEqualEval_listBefore
    (left right : Word Nat)
    (equalEval : ∀ valuation : Nat → Fin 6,
      affineShiftThree.semigroup.eval valuation left =
        affineShiftThree.semigroup.eval valuation right)
    {first second : Nat}
    (leftBefore :
      AffineShiftThreeListBefore first second
        (affineShiftThreeFirstOccurrenceOrder left)) :
    AffineShiftThreeListBefore first second
      (affineShiftThreeFirstOccurrenceOrder right) := by
  let leftOrder := affineShiftThreeFirstOccurrenceOrder left
  let rightOrder := affineShiftThreeFirstOccurrenceOrder right
  have leftNodup : leftOrder.Nodup :=
    affineShiftThreeFirstOccurrenceOrderList_nodup left.toList
  have rightNodup : rightOrder.Nodup :=
    affineShiftThreeFirstOccurrenceOrderList_nodup right.toList
  have sameMembers : ∀ tested,
      tested ∈ leftOrder ↔ tested ∈ rightOrder := by
    intro tested
    rw [show leftOrder =
        affineShiftThreeFirstOccurrenceOrderList left.toList by rfl,
      show rightOrder =
        affineShiftThreeFirstOccurrenceOrderList right.toList by rfl,
      affineShiftThreeFirstOccurrenceOrderList_mem_iff,
      affineShiftThreeFirstOccurrenceOrderList_mem_iff]
    exact affineShiftThreeEqualEval_mem_iff left right equalEval tested
  have firstLeft := AffineShiftThreeListBefore.left_mem leftBefore
  have secondLeft := AffineShiftThreeListBefore.right_mem leftBefore
  have different : first ≠ second := by
    intro equal
    subst second
    exact
      (AffineShiftThreeListBefore.asymm_of_nodup
        leftNodup leftBefore) leftBefore
  have firstRight := (sameMembers first).mp firstLeft
  have secondRight := (sameMembers second).mp secondLeft
  let valuation := affineShiftThreeOrderValuation first second
  have evaluated := equalEval valuation
  rw [affineShiftThreeEval_eq_evalList,
    affineShiftThreeEval_eq_evalList] at evaluated
  have orderEvaluated :
      affineShiftThreeEvalList valuation leftOrder =
        affineShiftThreeEvalList valuation rightOrder := by
    calc
      affineShiftThreeEvalList valuation leftOrder =
          affineShiftThreeEvalList valuation left.toList :=
        affineShiftThreeOrderValuation_firstOccurrenceOrder
          first second left.toList
      _ = affineShiftThreeEvalList valuation right.toList := evaluated
      _ = affineShiftThreeEvalList valuation rightOrder :=
        (affineShiftThreeOrderValuation_firstOccurrenceOrder
          first second right.toList).symm
  rcases affineShiftThreeListBefore_total_of_nodup
      rightNodup different firstRight secondRight with
      rightBefore | reverseRight
  · exact rightBefore
  · have leftValue :
        affineShiftThreeEvalList valuation leftOrder =
          affineShiftThreeIdealResidue 0 :=
      affineShiftThreeEvalList_of_listBefore
        valuation first second 0
        (affineShiftThreeOrderValuation_first first second)
        (by
          intro letter notFirst notSecond
          exact affineShiftThreeOrderValuation_other
            notFirst notSecond)
        leftNodup leftBefore
    have rightValue :
        affineShiftThreeEvalList valuation rightOrder =
          affineShiftThreeIdealResidue 1 :=
      affineShiftThreeEvalList_of_listBefore
        valuation second first 1
        (affineShiftThreeOrderValuation_second different)
        (by
          intro letter notSecond notFirst
          exact affineShiftThreeOrderValuation_other
            notFirst notSecond)
        rightNodup reverseRight
    have impossible : (0 : Fin 3) = 1 :=
      affineShiftThreeIdealResidue_injective <|
        leftValue.symm.trans <| orderEvaluated.trans rightValue
    simp at impossible

/-- Equality of all evaluations in the affine table recovers the literal
first-occurrence sequence. -/
theorem affineShiftThreeEqualEval_firstOccurrenceOrder
    (left right : Word Nat)
    (equalEval : ∀ valuation : Nat → Fin 6,
      affineShiftThree.semigroup.eval valuation left =
        affineShiftThree.semigroup.eval valuation right) :
    affineShiftThreeFirstOccurrenceOrder left =
      affineShiftThreeFirstOccurrenceOrder right := by
  let leftOrder := affineShiftThreeFirstOccurrenceOrder left
  let rightOrder := affineShiftThreeFirstOccurrenceOrder right
  have leftNodup : leftOrder.Nodup :=
    affineShiftThreeFirstOccurrenceOrderList_nodup left.toList
  have rightNodup : rightOrder.Nodup :=
    affineShiftThreeFirstOccurrenceOrderList_nodup right.toList
  have sameMembers : ∀ tested,
      tested ∈ leftOrder ↔ tested ∈ rightOrder := by
    intro tested
    rw [show leftOrder =
        affineShiftThreeFirstOccurrenceOrderList left.toList by rfl,
      show rightOrder =
        affineShiftThreeFirstOccurrenceOrderList right.toList by rfl,
      affineShiftThreeFirstOccurrenceOrderList_mem_iff,
      affineShiftThreeFirstOccurrenceOrderList_mem_iff]
    exact affineShiftThreeEqualEval_mem_iff left right equalEval tested
  have sameBefore : ∀ first second,
      AffineShiftThreeListBefore first second leftOrder ↔
        AffineShiftThreeListBefore first second rightOrder := by
    intro first second
    constructor
    · exact affineShiftThreeEqualEval_listBefore left right equalEval
    · exact affineShiftThreeEqualEval_listBefore right left
        (fun valuation => (equalEval valuation).symm)
  exact affineShiftThreeNodupList_eq_of_order
    leftOrder rightOrder leftNodup rightNodup sameMembers sameBefore

/-- Unconditional finite-basis endpoint for the affine order-six table
`S6_15903`. -/
theorem affineShiftThreeBasis_complete :
    BasisFor affineShiftThree.semigroup affineShiftThreeBasis := by
  refine ⟨affineShiftThreeModels, ?_⟩
  intro identity valid
  have sameOrder :=
    affineShiftThreeEqualEval_firstOccurrenceOrder
      identity.lhs identity.rhs valid
  have sameTotal : ∀ tested,
      affineShiftThreeWordTotalResidue tested identity.lhs =
        affineShiftThreeWordTotalResidue tested identity.rhs :=
    affineShiftThreeEqualEval_wordTotalResidue
      identity.lhs identity.rhs valid
  have samePrefix : ∀ selected tested,
      affineShiftThreeWordPrefixResidue selected tested identity.lhs =
        affineShiftThreeWordPrefixResidue selected tested identity.rhs :=
    affineShiftThreeEqualEval_wordPrefixResidue
      identity.lhs identity.rhs valid
  have leftNormal := affineShiftThreeDerivesNormal identity.lhs
  have rightNormal := affineShiftThreeDerivesNormal identity.rhs
  have normalEq := affineShiftThreeNormalWord_eq_of_invariants
    identity.lhs identity.rhs sameOrder sameTotal samePrefix
  have middle :
      Derives affineShiftThreeBasis
        (affineShiftThreeNormalWord identity.lhs)
        (affineShiftThreeNormalWord identity.rhs) := by
    rw [normalEq]
    exact Derives.refl _
  exact leftNormal.trans <| middle.trans rightNormal.symm

end SemigroupBasis.Examples
