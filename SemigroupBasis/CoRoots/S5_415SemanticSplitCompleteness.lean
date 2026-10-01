import SemigroupBasis.CoRoots.S5_415Retarget
import SemigroupBasis.CoRoots.S5_415SemanticSplit

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

private theorem sameBrandtSignature_symm
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    SameBrandtSignature right left := by
  refine ⟨fun letter => (same.1 letter).symm, ?_⟩
  intro assignment
  refine ⟨((same.2 assignment).1).symm, ?_⟩
  intro rightCompatible
  have leftCompatible := ((same.2 assignment).1).mpr rightCompatible
  have endpoints := (same.2 assignment).2 leftCompatible
  exact ⟨endpoints.1.symm, endpoints.2.symm⟩

private theorem word_final_mem_toList (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem adjacentPair_letters_mem_toList
    {word : Word Nat} {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    source ∈ word.toList ∧ target ∈ word.toList := by
  cases word with
  | mk head tail =>
      change
        (source, target) ∈ Word.adjacentPairsFrom head tail at edge
      change source ∈ head :: tail ∧ target ∈ head :: tail
      induction tail generalizing head with
      | nil =>
          simp [Word.adjacentPairsFrom] at edge
      | cons next rest ih =>
          simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
          rcases edge with edge | edge
          · cases edge
            exact ⟨by simp, by simp⟩
          · obtain ⟨sourceMem, targetMem⟩ := ih next edge
            exact
              ⟨List.mem_cons_of_mem head sourceMem,
                List.mem_cons_of_mem head targetMem⟩

private theorem compatible_congr_on_toList
    (first second : EndpointAssignment) (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList → first letter = second letter) :
    Compatible first word ↔ Compatible second word := by
  constructor
  · intro firstCompatible
    have firstEdges :=
      (compatible_iff_adjacent_endpoint_eq first word).mp
        firstCompatible
    apply (compatible_iff_adjacent_endpoint_eq second word).mpr
    intro source target edge
    have members := adjacentPair_letters_mem_toList edge
    simpa [agree source members.1, agree target members.2] using
      firstEdges source target edge
  · intro secondCompatible
    have secondEdges :=
      (compatible_iff_adjacent_endpoint_eq second word).mp
        secondCompatible
    apply (compatible_iff_adjacent_endpoint_eq first word).mpr
    intro source target edge
    have members := adjacentPair_letters_mem_toList edge
    simpa [agree source members.1, agree target members.2] using
      secondEdges source target edge

private theorem compatible_zero (word : Word Nat) :
    Compatible
      (fun _ : Nat => ((0 : Fin 2), (0 : Fin 2))) word := by
  apply (compatible_iff_adjacent_endpoint_eq _ word).mpr
  intro _ _ _
  rfl

private theorem compatible_singleton
    (assignment : EndpointAssignment) (letter : Nat) :
    Compatible assignment (Word.singleton letter) := by
  apply
    (compatible_iff_adjacent_endpoint_eq assignment
      (Word.singleton letter)).mpr
  intro source target edge
  simp [Word.adjacentPairs, Word.adjacentPairsFrom] at edge

private theorem compatible_append_iff
    (assignment : EndpointAssignment) (left right : Word Nat) :
    Compatible assignment (left ++ right) ↔
      Compatible assignment left ∧
        (assignment left.final).2 = (assignment right.head).1 ∧
          Compatible assignment right := by
  constructor
  · intro fullCompatible
    have fullEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment
        (left ++ right)).mp fullCompatible
    refine ⟨?_, ?_, ?_⟩
    · apply (compatible_iff_adjacent_endpoint_eq assignment left).mpr
      intro source target edge
      exact fullEdges source target (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr (Or.inl edge))
    · exact fullEdges left.final right.head (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr (Or.inr (by simp)))
    · apply (compatible_iff_adjacent_endpoint_eq assignment right).mpr
      intro source target edge
      exact fullEdges source target (by
        rw [Word.adjacentPairs_append]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons_of_mem _ edge)))
  · rintro ⟨leftCompatible, boundary, rightCompatible⟩
    have leftEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment left).mp
        leftCompatible
    have rightEdges :=
      (compatible_iff_adjacent_endpoint_eq assignment right).mp
        rightCompatible
    apply
      (compatible_iff_adjacent_endpoint_eq assignment
        (left ++ right)).mpr
    intro source target edge
    rw [Word.adjacentPairs_append] at edge
    rcases List.mem_append.mp edge with edge | edge
    · exact leftEdges source target edge
    · simp only [List.mem_cons] at edge
      rcases edge with edge | edge
      · cases edge
        exact boundary
      · exact rightEdges source target edge

private theorem compatible_appendTrailingLetters_of_zero
    (assignment : EndpointAssignment) (base : Word Nat)
    (letters : List Nat)
    (baseCompatible : Compatible assignment base)
    (baseFinalOutgoingZero : (assignment base.final).2 = 0)
    (lettersZero :
      ∀ letter, letter ∈ letters →
        assignment letter = ((0 : Fin 2), (0 : Fin 2))) :
    Compatible assignment (appendTrailingLetters base letters) := by
  cases letters with
  | nil =>
      simpa [appendTrailingLetters] using baseCompatible
  | cons head tail =>
      change Compatible assignment (base ++ ⟨head, tail⟩)
      apply (compatible_append_iff assignment base ⟨head, tail⟩).mpr
      refine ⟨baseCompatible, ?_, ?_⟩
      · have headZero := lettersZero head (by simp)
        rw [headZero]
        exact baseFinalOutgoingZero
      · let zeroAssignment : EndpointAssignment :=
          fun _ => ((0 : Fin 2), (0 : Fin 2))
        apply
          (compatible_congr_on_toList assignment zeroAssignment
            ⟨head, tail⟩ ?_).mpr
        · simpa [zeroAssignment] using
            (compatible_zero (⟨head, tail⟩ : Word Nat))
        · intro letter member
          have lettersMember : letter ∈ head :: tail := by
            simpa [Word.toList] using member
          simpa [zeroAssignment] using
            lettersZero letter lettersMember

private theorem compatible_base_of_appendTrailingLetters
    (assignment : EndpointAssignment) (base : Word Nat)
    (letters : List Nat)
    (compatible :
      Compatible assignment (appendTrailingLetters base letters)) :
    Compatible assignment base := by
  cases letters with
  | nil =>
      simpa [appendTrailingLetters] using compatible
  | cons head tail =>
      change Compatible assignment (base ++ ⟨head, tail⟩) at compatible
      exact
        ((compatible_append_iff assignment base ⟨head, tail⟩).mp
          compatible).1

private theorem isolatedPrefix_forward
    {source target : Word Nat}
    {sourceHead targetHead marker : Nat}
    {sourceTail targetTail sourceSuffix targetSuffix : List Nat}
    (same : SameBrandtSignature source target)
    (sourceFactorization :
      source.toList =
        (sourceHead :: sourceTail) ++ [marker] ++ sourceSuffix)
    (targetFactorization :
      target.toList =
        (targetHead :: targetTail) ++ [marker] ++ targetSuffix)
    (markerNotSourcePrefix : marker ∉ sourceHead :: sourceTail)
    (markerNotSourceSuffix : marker ∉ sourceSuffix)
    (sourceDisjoint :
      ∀ letter,
        letter ∈ sourceHead :: sourceTail → letter ∉ sourceSuffix)
    (prefixSupport :
      ∀ letter,
        letter ∈ sourceHead :: sourceTail ↔
          letter ∈ targetHead :: targetTail)
    (suffixSupport :
      ∀ letter, letter ∈ sourceSuffix ↔ letter ∈ targetSuffix)
    (assignment : EndpointAssignment)
    (sourceCompatible :
      Compatible assignment (⟨sourceHead, sourceTail⟩ : Word Nat)) :
    Compatible assignment (⟨targetHead, targetTail⟩ : Word Nat) ∧
      (assignment sourceHead).1 = (assignment targetHead).1 ∧
        (assignment
            (⟨sourceHead, sourceTail⟩ : Word Nat).final).2 =
          (assignment
            (⟨targetHead, targetTail⟩ : Word Nat).final).2 := by
  let sourcePrefix : Word Nat := ⟨sourceHead, sourceTail⟩
  let targetPrefix : Word Nat := ⟨targetHead, targetTail⟩
  let extension : EndpointAssignment := fun letter =>
    if letter ∈ sourceHead :: sourceTail then
      assignment letter
    else if letter = marker then
      ((assignment sourcePrefix.final).2, (0 : Fin 2))
    else
      ((0 : Fin 2), (0 : Fin 2))
  have sourceShape :
      source =
        appendTrailingLetters
          (sourcePrefix ++ Word.singleton marker) sourceSuffix := by
    apply Word.toList_injective
    rw [appendTrailingLetters_toList, Word.toList_append]
    simpa [sourcePrefix, Word.toList, List.append_assoc] using
      sourceFactorization
  have targetShape :
      target =
        appendTrailingLetters
          (targetPrefix ++ Word.singleton marker) targetSuffix := by
    apply Word.toList_injective
    rw [appendTrailingLetters_toList, Word.toList_append]
    simpa [targetPrefix, Word.toList, List.append_assoc] using
      targetFactorization
  have extensionSourcePrefix
      (letter : Nat) (member : letter ∈ sourcePrefix.toList) :
      extension letter = assignment letter := by
    have rawMember : letter ∈ sourceHead :: sourceTail := by
      simpa [sourcePrefix, Word.toList] using member
    simp only [extension, if_pos rawMember]
  have extensionTargetPrefix
      (letter : Nat) (member : letter ∈ targetPrefix.toList) :
      extension letter = assignment letter := by
    have targetMember : letter ∈ targetHead :: targetTail := by
      simpa [targetPrefix, Word.toList] using member
    have sourceMember := (prefixSupport letter).mpr targetMember
    simp only [extension, if_pos sourceMember]
  have extensionSourceSuffix
      (letter : Nat) (member : letter ∈ sourceSuffix) :
      extension letter = ((0 : Fin 2), (0 : Fin 2)) := by
    have notPrefix : letter ∉ sourceHead :: sourceTail := by
      intro prefixMember
      exact sourceDisjoint letter prefixMember member
    have notMarker : letter ≠ marker := by
      intro equality
      subst letter
      exact markerNotSourceSuffix member
    simp only [extension, if_neg notPrefix, if_neg notMarker]
  have extensionTargetSuffix
      (letter : Nat) (member : letter ∈ targetSuffix) :
      extension letter = ((0 : Fin 2), (0 : Fin 2)) := by
    exact extensionSourceSuffix letter ((suffixSupport letter).mpr member)
  have extensionMarker :
      extension marker =
        ((assignment sourcePrefix.final).2, (0 : Fin 2)) := by
    simp only [extension, if_neg markerNotSourcePrefix, if_pos rfl]
    simp
  have sourcePrefixExtensionCompatible :
      Compatible extension sourcePrefix :=
    (compatible_congr_on_toList extension assignment sourcePrefix
      extensionSourcePrefix).mpr (by
        simpa [sourcePrefix] using sourceCompatible)
  have sourcePrefixMarkerBoundary :
      (extension sourcePrefix.final).2 =
        (extension (Word.singleton marker).head).1 := by
    rw [extensionSourcePrefix sourcePrefix.final
      (word_final_mem_toList sourcePrefix)]
    simp [extensionMarker]
  have sourceBaseCompatible :
      Compatible extension (sourcePrefix ++ Word.singleton marker) :=
    (compatible_append_iff extension sourcePrefix
      (Word.singleton marker)).mpr
        ⟨sourcePrefixExtensionCompatible, sourcePrefixMarkerBoundary,
          compatible_singleton extension marker⟩
  have sourceBaseFinalZero :
      (extension (sourcePrefix ++ Word.singleton marker).final).2 = 0 := by
    simp [extensionMarker, Word.final]
  have sourceWholeCompatible : Compatible extension source := by
    rw [sourceShape]
    exact compatible_appendTrailingLetters_of_zero extension
      (sourcePrefix ++ Word.singleton marker) sourceSuffix
      sourceBaseCompatible sourceBaseFinalZero extensionSourceSuffix
  have targetWholeCompatible : Compatible extension target :=
    ((same.2 extension).1).mp sourceWholeCompatible
  rw [targetShape] at targetWholeCompatible
  have targetBaseCompatible :
      Compatible extension (targetPrefix ++ Word.singleton marker) :=
    compatible_base_of_appendTrailingLetters extension
      (targetPrefix ++ Word.singleton marker) targetSuffix
      targetWholeCompatible
  have targetParts :=
    (compatible_append_iff extension targetPrefix
      (Word.singleton marker)).mp targetBaseCompatible
  have targetPrefixCompatible : Compatible assignment targetPrefix :=
    (compatible_congr_on_toList extension assignment targetPrefix
      extensionTargetPrefix).mp targetParts.1
  have incomingEquality :=
    ((same.2 extension).2 sourceWholeCompatible).1
  rw [sourceShape, targetShape] at incomingEquality
  simp only [appendTrailingLetters_head, Word.append_head] at incomingEquality
  have sourceHeadAgreement :=
    extensionSourcePrefix sourcePrefix.head (by
      simp [sourcePrefix, Word.toList])
  have targetHeadAgreement :=
    extensionTargetPrefix targetPrefix.head (by
      simp [targetPrefix, Word.toList])
  have prefixHeadEquality :
      (assignment sourceHead).1 = (assignment targetHead).1 := by
    simpa [sourcePrefix, targetPrefix, sourceHeadAgreement,
      targetHeadAgreement] using incomingEquality
  have targetFinalAgreement :=
    extensionTargetPrefix targetPrefix.final
      (word_final_mem_toList targetPrefix)
  have targetToSourceFinal :
      (assignment targetPrefix.final).2 =
        (assignment sourcePrefix.final).2 := by
    simpa [targetFinalAgreement, extensionMarker] using targetParts.2.1
  refine ⟨?_, prefixHeadEquality, ?_⟩
  · simpa [targetPrefix] using targetPrefixCompatible
  · simpa [sourcePrefix, targetPrefix] using targetToSourceFinal.symm

private theorem sameBrandtSignature_of_isolated_prefix
    {left right : Word Nat}
    {leftHead rightHead marker : Nat}
    {leftTail rightTail leftSuffix rightSuffix : List Nat}
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = (leftHead :: leftTail) ++ [marker] ++ leftSuffix)
    (rightFactorization :
      right.toList =
        (rightHead :: rightTail) ++ [marker] ++ rightSuffix)
    (markerNotLeftPrefix : marker ∉ leftHead :: leftTail)
    (markerNotLeftSuffix : marker ∉ leftSuffix)
    (leftDisjoint :
      ∀ letter, letter ∈ leftHead :: leftTail → letter ∉ leftSuffix)
    (markerNotRightPrefix : marker ∉ rightHead :: rightTail)
    (markerNotRightSuffix : marker ∉ rightSuffix)
    (rightDisjoint :
      ∀ letter,
        letter ∈ rightHead :: rightTail → letter ∉ rightSuffix)
    (prefixSupport :
      ∀ letter,
        letter ∈ leftHead :: leftTail ↔
          letter ∈ rightHead :: rightTail)
    (suffixSupport :
      ∀ letter, letter ∈ leftSuffix ↔ letter ∈ rightSuffix) :
    SameBrandtSignature
      (⟨leftHead, leftTail⟩ : Word Nat)
      (⟨rightHead, rightTail⟩ : Word Nat) := by
  refine ⟨?_, ?_⟩
  · intro letter
    simpa [Word.toList] using prefixSupport letter
  · intro assignment
    constructor
    · constructor
      · intro leftCompatible
        exact (isolatedPrefix_forward same leftFactorization
          rightFactorization markerNotLeftPrefix markerNotLeftSuffix
          leftDisjoint prefixSupport suffixSupport assignment
          leftCompatible).1
      · intro rightCompatible
        exact (isolatedPrefix_forward (sameBrandtSignature_symm same)
          rightFactorization leftFactorization markerNotRightPrefix
          markerNotRightSuffix rightDisjoint
          (fun letter => (prefixSupport letter).symm)
          (fun letter => (suffixSupport letter).symm)
          assignment rightCompatible).1
    · intro leftCompatible
      exact (isolatedPrefix_forward same leftFactorization
        rightFactorization markerNotLeftPrefix markerNotLeftSuffix
        leftDisjoint prefixSupport suffixSupport assignment
        leftCompatible).2

private theorem isolatedSuffix_forward
    {source target : Word Nat}
    {sourceHead targetHead marker : Nat}
    {sourcePrefix targetPrefix sourceTail targetTail : List Nat}
    (same : SameBrandtSignature source target)
    (sourceFactorization :
      source.toList = sourcePrefix ++ [marker] ++ sourceHead :: sourceTail)
    (targetFactorization :
      target.toList = targetPrefix ++ [marker] ++ targetHead :: targetTail)
    (markerNotSourcePrefix : marker ∉ sourcePrefix)
    (markerNotSourceSuffix : marker ∉ sourceHead :: sourceTail)
    (sourceDisjoint :
      ∀ letter, letter ∈ sourcePrefix →
        letter ∉ sourceHead :: sourceTail)
    (suffixSupport :
      ∀ letter,
        letter ∈ sourceHead :: sourceTail ↔
          letter ∈ targetHead :: targetTail)
    (assignment : EndpointAssignment)
    (sourceCompatible :
      Compatible assignment (⟨sourceHead, sourceTail⟩ : Word Nat)) :
    Compatible assignment (⟨targetHead, targetTail⟩ : Word Nat) ∧
      (assignment sourceHead).1 = (assignment targetHead).1 ∧
        (assignment
            (⟨sourceHead, sourceTail⟩ : Word Nat).final).2 =
          (assignment
            (⟨targetHead, targetTail⟩ : Word Nat).final).2 := by
  let sourceSuffix : Word Nat := ⟨sourceHead, sourceTail⟩
  let targetSuffix : Word Nat := ⟨targetHead, targetTail⟩
  let sourceBase := wordWithFinalLetter sourcePrefix marker
  let targetBase := wordWithFinalLetter targetPrefix marker
  let extension : EndpointAssignment := fun letter =>
    if letter ∈ sourceHead :: sourceTail then
      assignment letter
    else if letter = marker then
      ((0 : Fin 2), (assignment sourceSuffix.head).1)
    else
      ((0 : Fin 2), (0 : Fin 2))
  have sourceShape : source = sourceBase ++ sourceSuffix := by
    apply Word.toList_injective
    have sourceBaseList :
        sourceBase.toList = sourcePrefix ++ [marker] := by
      simpa [sourceBase] using
        wordWithFinalLetter_toList sourcePrefix marker
    rw [Word.toList_append, sourceBaseList]
    simpa [sourceSuffix, Word.toList, List.append_assoc] using
      sourceFactorization
  have targetShape : target = targetBase ++ targetSuffix := by
    apply Word.toList_injective
    have targetBaseList :
        targetBase.toList = targetPrefix ++ [marker] := by
      simpa [targetBase] using
        wordWithFinalLetter_toList targetPrefix marker
    rw [Word.toList_append, targetBaseList]
    simpa [targetSuffix, Word.toList, List.append_assoc] using
      targetFactorization
  have extensionSourceSuffix
      (letter : Nat) (member : letter ∈ sourceSuffix.toList) :
      extension letter = assignment letter := by
    have rawMember : letter ∈ sourceHead :: sourceTail := by
      simpa [sourceSuffix, Word.toList] using member
    simp only [extension, if_pos rawMember]
  have extensionTargetSuffix
      (letter : Nat) (member : letter ∈ targetSuffix.toList) :
      extension letter = assignment letter := by
    have targetMember : letter ∈ targetHead :: targetTail := by
      simpa [targetSuffix, Word.toList] using member
    have sourceMember := (suffixSupport letter).mpr targetMember
    simp only [extension, if_pos sourceMember]
  have extensionSourcePrefix
      (letter : Nat) (member : letter ∈ sourcePrefix) :
      extension letter = ((0 : Fin 2), (0 : Fin 2)) := by
    have notSuffix : letter ∉ sourceHead :: sourceTail := by
      exact sourceDisjoint letter member
    have notMarker : letter ≠ marker := by
      intro equality
      subst letter
      exact markerNotSourcePrefix member
    simp only [extension, if_neg notSuffix, if_neg notMarker]
  have extensionMarker :
      extension marker =
        ((0 : Fin 2), (assignment sourceSuffix.head).1) := by
    simp only [extension, if_neg markerNotSourceSuffix, if_pos rfl]
    simp
  have sourceSuffixExtensionCompatible :
      Compatible extension sourceSuffix :=
    (compatible_congr_on_toList extension assignment sourceSuffix
      extensionSourceSuffix).mpr (by
        simpa [sourceSuffix] using sourceCompatible)
  have sourceBaseCompatible : Compatible extension sourceBase := by
    cases sourcePrefix with
    | nil =>
        simpa [sourceBase, wordWithFinalLetter] using
          compatible_singleton extension marker
    | cons prefixHead prefixTail =>
        let prefixWord : Word Nat := ⟨prefixHead, prefixTail⟩
        let zeroAssignment : EndpointAssignment :=
          fun _ => ((0 : Fin 2), (0 : Fin 2))
        have prefixCompatible : Compatible extension prefixWord := by
          apply
            (compatible_congr_on_toList extension zeroAssignment
              prefixWord ?_).mpr
          · simpa [zeroAssignment] using compatible_zero prefixWord
          · intro letter member
            have rawMember : letter ∈ prefixHead :: prefixTail := by
              simpa [prefixWord, Word.toList] using member
            simpa [zeroAssignment] using
              extensionSourcePrefix letter rawMember
        have boundary :
            (extension prefixWord.final).2 =
              (extension (Word.singleton marker).head).1 := by
          rw [extensionSourcePrefix prefixWord.final (by
            simpa [prefixWord, Word.toList] using
              word_final_mem_toList prefixWord)]
          simp [extensionMarker]
        simpa [sourceBase, wordWithFinalLetter, prefixWord] using
          (compatible_append_iff extension prefixWord
            (Word.singleton marker)).mpr
              ⟨prefixCompatible, boundary,
                compatible_singleton extension marker⟩
  have sourceBoundary :
      (extension sourceBase.final).2 =
        (extension sourceSuffix.head).1 := by
    have baseFinal : sourceBase.final = marker := by
      simp [sourceBase]
    rw [baseFinal, extensionMarker,
      extensionSourceSuffix sourceSuffix.head (by
        simp [sourceSuffix, Word.toList])]
  have sourceWholeCompatible : Compatible extension source := by
    rw [sourceShape]
    exact (compatible_append_iff extension sourceBase sourceSuffix).mpr
      ⟨sourceBaseCompatible, sourceBoundary,
        sourceSuffixExtensionCompatible⟩
  have targetWholeCompatible : Compatible extension target :=
    ((same.2 extension).1).mp sourceWholeCompatible
  rw [targetShape] at targetWholeCompatible
  have targetParts :=
    (compatible_append_iff extension targetBase targetSuffix).mp
      targetWholeCompatible
  have targetSuffixCompatible : Compatible assignment targetSuffix :=
    (compatible_congr_on_toList extension assignment targetSuffix
      extensionTargetSuffix).mp targetParts.2.2
  have targetBaseFinal : targetBase.final = marker := by
    simp [targetBase]
  have targetHeadAgreement :=
    extensionTargetSuffix targetSuffix.head (by
      simp [targetSuffix, Word.toList])
  have suffixHeadEquality :
      (assignment sourceHead).1 = (assignment targetHead).1 := by
    have boundary := targetParts.2.1
    rw [targetBaseFinal, extensionMarker, targetHeadAgreement] at boundary
    simpa [sourceSuffix, targetSuffix] using boundary
  have outgoingEquality :=
    ((same.2 extension).2 sourceWholeCompatible).2
  rw [sourceShape, targetShape] at outgoingEquality
  simp only [Word.final_append] at outgoingEquality
  have sourceFinalAgreement :=
    extensionSourceSuffix sourceSuffix.final
      (word_final_mem_toList sourceSuffix)
  have targetFinalAgreement :=
    extensionTargetSuffix targetSuffix.final
      (word_final_mem_toList targetSuffix)
  have suffixFinalEquality :
      (assignment sourceSuffix.final).2 =
        (assignment targetSuffix.final).2 := by
    simpa [sourceFinalAgreement, targetFinalAgreement] using
      outgoingEquality
  refine ⟨?_, suffixHeadEquality, ?_⟩
  · simpa [targetSuffix] using targetSuffixCompatible
  · simpa [sourceSuffix, targetSuffix] using suffixFinalEquality

private theorem sameBrandtSignature_of_isolated_suffix
    {left right : Word Nat}
    {leftHead rightHead marker : Nat}
    {leftPrefix rightPrefix leftTail rightTail : List Nat}
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftHead :: leftTail)
    (rightFactorization :
      right.toList = rightPrefix ++ [marker] ++ rightHead :: rightTail)
    (markerNotLeftPrefix : marker ∉ leftPrefix)
    (markerNotLeftSuffix : marker ∉ leftHead :: leftTail)
    (leftDisjoint :
      ∀ letter,
        letter ∈ leftPrefix → letter ∉ leftHead :: leftTail)
    (markerNotRightPrefix : marker ∉ rightPrefix)
    (markerNotRightSuffix : marker ∉ rightHead :: rightTail)
    (rightDisjoint :
      ∀ letter,
        letter ∈ rightPrefix → letter ∉ rightHead :: rightTail)
    (suffixSupport :
      ∀ letter,
        letter ∈ leftHead :: leftTail ↔
          letter ∈ rightHead :: rightTail) :
    SameBrandtSignature
      (⟨leftHead, leftTail⟩ : Word Nat)
      (⟨rightHead, rightTail⟩ : Word Nat) := by
  refine ⟨?_, ?_⟩
  · intro letter
    simpa [Word.toList] using suffixSupport letter
  · intro assignment
    constructor
    · constructor
      · intro leftCompatible
        exact (isolatedSuffix_forward same leftFactorization
          rightFactorization markerNotLeftPrefix markerNotLeftSuffix
          leftDisjoint suffixSupport assignment leftCompatible).1
      · intro rightCompatible
        exact (isolatedSuffix_forward (sameBrandtSignature_symm same)
          rightFactorization leftFactorization markerNotRightPrefix
          markerNotRightSuffix rightDisjoint
          (fun letter => (suffixSupport letter).symm)
          assignment rightCompatible).1
    · intro leftCompatible
      exact (isolatedSuffix_forward same leftFactorization
        rightFactorization markerNotLeftPrefix markerNotLeftSuffix
        leftDisjoint suffixSupport assignment leftCompatible).2

/-- The prefix subidentity forced by an isolated semantic split.  Empty
prefixes are represented by `none`; nonempty prefixes inherit the complete
Brandt signature, including their marked initial and final coordinates. -/
theorem CorrespondingIsolatedSplit.prefixRecursiveSignature
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit
      leftPrefix marker leftSuffix right)
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    OptionalSameBrandtSignature
      (optionalWordOfList leftPrefix)
      (optionalWordOfList split.rightPrefix) := by
  cases leftPrefix with
  | nil =>
      have rightPrefixNil : split.rightPrefix = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have leftMember := (split.prefix_support letter).mpr member
        simpa using leftMember
      simpa [optionalWordOfList, rightPrefixNil] using
        OptionalSameBrandtSignature.none
  | cons leftHead leftTail =>
      cases rightPrefixShape : split.rightPrefix with
      | nil =>
          have rightMember : leftHead ∈ split.rightPrefix :=
            (split.prefix_support leftHead).mp (by simp)
          simp [rightPrefixShape] at rightMember
      | cons rightHead rightTail =>
          apply OptionalSameBrandtSignature.some
          exact sameBrandtSignature_of_isolated_prefix same
            leftFactorization
            (by simpa [rightPrefixShape] using split.factorization)
            markerNotPrefix markerNotSuffix supportsDisjoint
            (by simpa [rightPrefixShape] using split.marker_not_prefix)
            split.marker_not_suffix
            (by simpa [rightPrefixShape] using split.supports_disjoint)
            (fun letter => by
              simpa [rightPrefixShape] using split.prefix_support letter)
            split.suffix_support

/-- The suffix subidentity forced by an isolated semantic split.  This is the
dual boundary case of `prefixRecursiveSignature`. -/
theorem CorrespondingIsolatedSplit.suffixRecursiveSignature
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit
      leftPrefix marker leftSuffix right)
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    OptionalSameBrandtSignature
      (optionalWordOfList leftSuffix)
      (optionalWordOfList split.rightSuffix) := by
  cases leftSuffix with
  | nil =>
      have rightSuffixNil : split.rightSuffix = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have leftMember := (split.suffix_support letter).mpr member
        simpa using leftMember
      simpa [optionalWordOfList, rightSuffixNil] using
        OptionalSameBrandtSignature.none
  | cons leftHead leftTail =>
      cases rightSuffixShape : split.rightSuffix with
      | nil =>
          have rightMember : leftHead ∈ split.rightSuffix :=
            (split.suffix_support leftHead).mp (by simp)
          simp [rightSuffixShape] at rightMember
      | cons rightHead rightTail =>
          apply OptionalSameBrandtSignature.some
          exact sameBrandtSignature_of_isolated_suffix same
            leftFactorization
            (by simpa [rightSuffixShape] using split.factorization)
            markerNotPrefix markerNotSuffix supportsDisjoint
            split.marker_not_prefix
            (by simpa [rightSuffixShape] using split.marker_not_suffix)
            (by simpa [rightSuffixShape] using split.supports_disjoint)
            (fun letter => by
              simpa [rightSuffixShape] using split.suffix_support letter)

/-- The original Brandt signature restricts to both recursively smaller
subidentities selected by an isolated split.  The statement includes all four
empty/nonempty prefix and suffix combinations without introducing dummy
semigroup words. -/
theorem CorrespondingIsolatedSplit.recursiveSignatures
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (split : CorrespondingIsolatedSplit
      leftPrefix marker leftSuffix right)
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    split.RecursiveSignatures := by
  exact
    ⟨split.prefixRecursiveSignature same leftFactorization
        markerNotPrefix markerNotSuffix supportsDisjoint,
      split.suffixRecursiveSignature same leftFactorization
        markerNotPrefix markerNotSuffix supportsDisjoint⟩

end SemigroupBasis.CoRoots.S5_415
