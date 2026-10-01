import SemigroupBasis.CoRoots.S5_870GapBlocks

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## The four adjacent-second-occurrence placements -/

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives
      [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortBothEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortInitialGapEmpty
          (Word.singleton first)
          (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortFinalGapEmpty
          (Word.singleton first)
          (listWordOfCons gapHead gapTail)
          (Word.singleton second)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortGeneral
          (Word.singleton first)
          (listWordOfCons firstGapHead firstGapTail)
          (Word.singleton second)
          (listWordOfCons secondGapHead secondGapTail)))

/-- Swap displayed adjacent second occurrences. The four branches use only
nonempty word substitutions; empty gaps select the shorter literal law. -/
theorem listDerivesSwapDisplayedSeconds
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

/-! ## Locating the first copies in an arbitrary prefix -/

/-- Once both letters occur in `prefix`, their adjacent later occurrences can
be swapped in either first-occurrence order. This is the local rewrite needed
by a future inversion sort of one second-occurrence gap block. -/
theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      have split := List.mem_append.mp rightSeen
      rcases split with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed :=
        listDerivesSwapDisplayedSeconds
          right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

/-- Any permutation of one later block is derivable when every block letter
already occurs in the fixed prefix. This packages adjacent swaps by induction
on a `List.Perm` certificate; the remaining global task is to extract matching
gap blocks from equal signatures. -/
theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives
      (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        have inPrefix : letter ∈ stem :=
          sourceSeen letter (List.Mem.tail head member)
        exact List.mem_append.mpr (Or.inl inPrefix))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem :=
        sourceSeen first (by simp)
      have secondSeen : second ∈ stem :=
        sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen
          stem (rest ++ suffix) second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter
          ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ## Replaying corresponding gap blocks -/

private theorem listDerivesCorrespondingGapBlocks
    {seen : List Nat}
    {left right : List FirstOccurrenceGapBlock}
    (corresponding : CorrespondingGapBlocks left right)
    (formed : GapBlocksWellFormed seen left)
    (stem : List Nat)
    (seenInPrefix : ∀ letter, letter ∈ seen -> letter ∈ stem) :
    ListDerives
      (stem ++ renderGapBlocks left)
      (stem ++ renderGapBlocks right) := by
  induction corresponding generalizing seen stem with
  | nil =>
      simpa [renderGapBlocks] using
        S5_107.ListDerives.refl (basis := basis) stem
  | @cons leftBlock rightBlock leftRest rightRest
      markerEq secondsPermutation restCorrespondence induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          have sourceSeen :
              ∀ letter, letter ∈ leftBlock.seconds ->
                letter ∈ stem ++ [leftBlock.marker] := by
            intro letter member
            have known := secondsSeen letter member
            rcases List.mem_cons.mp known with atMarker | inSeen
            · subst letter
              simp
            · exact List.mem_append.mpr
                (Or.inl (seenInPrefix letter inSeen))
          have move :=
            listDerivesPermuteAfterSeen
              (stem ++ [leftBlock.marker])
              (renderGapBlocks leftRest)
              sourceSeen secondsPermutation
          have nextSeenInPrefix :
              ∀ letter, letter ∈ leftBlock.marker :: seen ->
                letter ∈
                  stem ++ [leftBlock.marker] ++ rightBlock.seconds := by
            intro letter member
            rcases List.mem_cons.mp member with atMarker | inSeen
            · subst letter
              simp
            · exact List.mem_append.mpr <| Or.inl <|
                List.mem_append.mpr <| Or.inl <|
                  seenInPrefix letter inSeen
          have recurse := induction tailFormed
            (stem ++ [leftBlock.marker] ++ rightBlock.seconds)
            nextSeenInPrefix
          simpa [renderGapBlocks, markerEq, List.append_assoc] using
            move.trans recurse

/-- Parsed two-limited words with equal signatures differ only by
permutations inside corresponding second-occurrence gap blocks. -/
theorem listDerivesOfTwoLimitedSameGapSignature
    (left right : List Nat)
    (leftLimited : ∀ letter, left.count letter <= 2)
    (rightLimited : ∀ letter, right.count letter <= 2)
    (same : gapSignatureList left = gapSignatureList right) :
    ListDerives left right := by
  have corresponding :=
    correspondingGapBlocks_of_sameSignatureList
      left right leftLimited rightLimited same
  have rendered :=
    listDerivesCorrespondingGapBlocks corresponding
      (gapBlocksList_wellFormed left) [] (by simp)
  simpa [render_gapBlocksList] using rendered

/-- Complete gap-block sorting for two-limited semigroup words. -/
theorem derivesOfTwoLimitedSameGapSignature
    (left right : Word Nat)
    (leftLimited : IsTwoLimited left)
    (rightLimited : IsTwoLimited right)
    (same : gapSignature left = gapSignature right) :
    Derives basis left right := by
  have listed : ListDerives left.toList right.toList :=
    listDerivesOfTwoLimitedSameGapSignature
      left.toList right.toList leftLimited rightLimited
      (by simpa [gapSignature] using same)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [listWordOfCons] using
            S5_107.ListDerives.toWord listed

/-- The cap scan and the block parser discharge the full sorting obligation. -/
def gapBlockSort : GapBlockSortObligation twoLimitedReduction where
  sort := derivesOfTwoLimitedSameGapSignature

/-! ## Unrestricted derivability from the gap signature -/

/-- Reduction to two occurrences followed by block sorting is complete for
the syntactic gap signature, with no bound on variables or word length. -/
theorem basisDerivesOfGapSignatureEq
    (left right : Word Nat)
    (same : gapSignature left = gapSignature right) :
    Derives basis left right := by
  obtain ⟨leftReduced, leftLimited, leftSignature, leftDerivation⟩ :=
    twoLimitedReduction.reduce left
  obtain ⟨rightReduced, rightLimited, rightSignature,
      rightDerivation⟩ :=
    twoLimitedReduction.reduce right
  have reducedSignature :
      gapSignature leftReduced = gapSignature rightReduced := by
    calc
      gapSignature leftReduced = gapSignature left := leftSignature.symm
      _ = gapSignature right := same
      _ = gapSignature rightReduced := rightSignature
  exact leftDerivation.trans <|
    (gapBlockSort.sort leftReduced rightReduced
      leftLimited rightLimited reducedSignature).trans
        rightDerivation.symm

/-- Semantic interface between validity in the exact table and equality of
the unbounded gap signature.  `S5_870Invariant` supplies the catalogue-specific
inhabitant using the two three-element embeddings and marker valuations. -/
structure TableGapSignatureSeparationObligation : Prop where
  separate :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy table.semigroup ->
        gapSignature identity.lhs = gapSignature identity.rhs

/- Direct and opposite endpoints are packaged in `S5_870Family`; their current
status remains source-authored and uncompiled. -/

end SemigroupBasis.CoRoots.S5_870
