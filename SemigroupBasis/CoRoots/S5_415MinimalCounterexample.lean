import SemigroupBasis.CoRoots.S5_415PairedInduction
import SemigroupBasis.CoRoots.S5_415SemanticSplitCompleteness

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Equal Brandt signatures are symmetric. -/
theorem SameBrandtSignature.symm
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

private theorem nodup_length_le_of_subset
    {source target : List Nat}
    (nodup : source.Nodup)
    (subset : ∀ value, value ∈ source → value ∈ target) :
    source.length ≤ target.length := by
  induction source generalizing target with
  | nil => simp
  | cons head tail induction =>
      have nodupParts := List.pairwise_cons.mp nodup
      have headNotTail : head ∉ tail := by
        intro member
        exact (nodupParts.1 head member) rfl
      have headTarget : head ∈ target :=
        subset head (List.Mem.head tail)
      have tailSubset :
          ∀ value, value ∈ tail → value ∈ target.erase head := by
        intro value member
        have different : value ≠ head := by
          intro equality
          subst value
          exact headNotTail member
        exact (List.mem_erase_of_ne different).mpr
          (subset value (List.Mem.tail head member))
      have lengthBound := induction nodupParts.2 tailSubset
      rw [List.length_erase_of_mem headTarget] at lengthBound
      have targetPositive : 1 ≤ target.length := by
        apply List.length_pos_iff.mpr
        intro empty
        subst target
        simp at headTarget
      simp only [List.length_cons]
      omega

/-- A supported subword which omits one supported ambient letter has strictly
smaller distinct-letter support. -/
theorem brandtSupportCard_lt_of_support_subset_of_missing
    {smaller larger : Word Nat} {missing : Nat}
    (supportSubset :
      ∀ letter, letter ∈ smaller.toList → letter ∈ larger.toList)
    (missingInLarger : missing ∈ larger.toList)
    (missingFromSmaller : missing ∉ smaller.toList) :
    brandtSupportCard smaller < brandtSupportCard larger := by
  have augmentedNodup :
      (missing :: deduplicateBrandtLetters smaller.toList).Nodup := by
    simp only [List.nodup_cons]
    refine ⟨?_, deduplicateBrandtLetters_nodup smaller.toList⟩
    intro member
    exact missingFromSmaller
      ((mem_deduplicateBrandtLetters missing smaller.toList).mp member)
  have augmentedSubset :
      ∀ letter,
        letter ∈ missing :: deduplicateBrandtLetters smaller.toList →
          letter ∈ deduplicateBrandtLetters larger.toList := by
    intro letter member
    rw [mem_deduplicateBrandtLetters]
    rcases List.mem_cons.mp member with equality | tailMember
    · subst letter
      exact missingInLarger
    · exact supportSubset letter
        ((mem_deduplicateBrandtLetters letter smaller.toList).mp
          tailMember)
  have lengthBound :=
    nodup_length_le_of_subset augmentedNodup augmentedSubset
  simp only [List.length_cons] at lengthBound
  simpa [brandtSupportCard] using (show
    (deduplicateBrandtLetters smaller.toList).length <
      (deduplicateBrandtLetters larger.toList).length by omega)

/-- A nonempty optional word represented by a list inherits the strict
support decrease witnessed by a missing ambient letter. -/
theorem brandtSupportCard_lt_of_optionalWordOfList_of_missing
    {larger smaller : Word Nat} {letters : List Nat} {missing : Nat}
    (shape : optionalWordOfList letters = some smaller)
    (lettersSupported :
      ∀ letter, letter ∈ letters → letter ∈ larger.toList)
    (missingInLarger : missing ∈ larger.toList)
    (missingFromLetters : missing ∉ letters) :
    brandtSupportCard smaller < brandtSupportCard larger := by
  have lettersEq : letters = smaller.toList := by
    calc
      letters = optionalWordLetters (optionalWordOfList letters) :=
        (optionalWordLetters_optionalWordOfList letters).symm
      _ = optionalWordLetters (some smaller) :=
        congrArg optionalWordLetters shape
      _ = smaller.toList := rfl
  apply brandtSupportCard_lt_of_support_subset_of_missing
    (missing := missing)
  · intro letter member
    apply lettersSupported letter
    rw [lettersEq]
    exact member
  · exact missingInLarger
  · intro member
    apply missingFromLetters
    rw [lettersEq]
    exact member

/-- Rebuild a word around one mandatory isolated marker.  Both surrounding
words remain genuinely optional. -/
private def isolatedRebuild
    (marker : Nat) (leadingWord suffix : Option (Word Nat)) : Word Nat :=
  match leadingWord, suffix with
  | none, none => Word.singleton marker
  | none, some suffixWord => Word.singleton marker ++ suffixWord
  | some prefixWord, none => prefixWord ++ Word.singleton marker
  | some prefixWord, some suffixWord =>
      (prefixWord ++ Word.singleton marker) ++ suffixWord

@[simp]
private theorem isolatedRebuild_toList
    (marker : Nat) (leadingWord suffix : Option (Word Nat)) :
    (isolatedRebuild marker leadingWord suffix).toList =
      optionalWordLetters leadingWord ++ [marker] ++
        optionalWordLetters suffix := by
  cases leadingWord <;> cases suffix <;>
    simp [isolatedRebuild, optionalWordLetters,
      Word.toList, Word.toList_append, List.append_assoc]

/-- Basis-parameterized optional derivability used only by the generic
minimal-counterexample argument below. -/
private inductive OptionalGapDerivesFor
    (laws : List (Identity Nat)) :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalGapDerivesFor laws none none
  | some {left right : Word Nat} :
      Derives laws left right →
      OptionalGapDerivesFor laws (some left) (some right)

/-- Recursive derivations lift through both optional contexts around the
same isolated marker. -/
private theorem derives_isolatedRebuild
    (basis : List (Identity Nat)) (marker : Nat)
    {leftPrefix rightPrefix leftSuffix rightSuffix :
      Option (Word Nat)}
    (prefixDerivation :
      OptionalGapDerivesFor basis leftPrefix rightPrefix)
    (suffixDerivation :
      OptionalGapDerivesFor basis leftSuffix rightSuffix) :
    Derives basis
      (isolatedRebuild marker leftPrefix leftSuffix)
      (isolatedRebuild marker rightPrefix rightSuffix) := by
  cases leftPrefix with
  | none =>
      cases rightPrefix with
      | none =>
          cases prefixDerivation
          cases leftSuffix with
          | none =>
              cases rightSuffix with
              | none =>
                  cases suffixDerivation
                  exact Derives.refl _
              | some rightSuffixWord =>
                  cases suffixDerivation
          | some leftSuffixWord =>
              cases rightSuffix with
              | none =>
                  cases suffixDerivation
              | some rightSuffixWord =>
                  cases suffixDerivation with
                  | some derivation =>
                      simpa [isolatedRebuild] using
                        Derives.prepend (Word.singleton marker) derivation
      | some rightPrefixWord =>
          cases prefixDerivation
  | some leftPrefixWord =>
      cases rightPrefix with
      | none =>
          cases prefixDerivation
      | some rightPrefixWord =>
          cases prefixDerivation with
          | some prefixWordDerivation =>
              cases leftSuffix with
              | none =>
                  cases rightSuffix with
                  | none =>
                      cases suffixDerivation
                      simpa [isolatedRebuild] using
                        Derives.appendRight prefixWordDerivation
                          (Word.singleton marker)
                  | some rightSuffixWord =>
                      cases suffixDerivation
              | some leftSuffixWord =>
                  cases rightSuffix with
                  | none =>
                      cases suffixDerivation
                  | some rightSuffixWord =>
                      cases suffixDerivation with
                      | some suffixWordDerivation =>
                          have prefixInContext :=
                            Derives.appendRight
                              (Derives.appendRight prefixWordDerivation
                                (Word.singleton marker))
                              leftSuffixWord
                          have suffixInContext :=
                            Derives.prepend
                              (rightPrefixWord ++ Word.singleton marker)
                              suffixWordDerivation
                          simpa [isolatedRebuild] using
                            prefixInContext.trans suffixInContext

private theorem optionalGapDerives_of_optionalSame_of_smaller
    {basis : List (Identity Nat)} {larger : Word Nat}
    {left right : Option (Word Nat)}
    (same : OptionalSameBrandtSignature left right)
    (leftSmaller :
      ∀ word, left = some word →
        brandtSupportCard word < brandtSupportCard larger)
    (smallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameBrandtSignature smallerLeft smallerRight →
          brandtSupportCard smallerLeft < brandtSupportCard larger →
            Derives basis smallerLeft smallerRight) :
    OptionalGapDerivesFor basis left right := by
  cases same with
  | none => exact OptionalGapDerivesFor.none
  | some signature =>
      exact OptionalGapDerivesFor.some
        (smallerDerivable signature (leftSmaller _ rfl))

private theorem repeatedWord_left_of_minimalSupport
    {basis : List (Identity Nat)} {left right : Word Nat}
    (same : SameBrandtSignature left right)
    (notDerivable : ¬ Derives basis left right)
    (smallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameBrandtSignature smallerLeft smallerRight →
          brandtSupportCard smallerLeft < brandtSupportCard left →
            Derives basis smallerLeft smallerRight) :
    RepeatedWord left := by
  apply Classical.byContradiction
  intro notRepeated
  obtain ⟨marker, leftPrefix, leftSuffix, leftFactorization,
      markerNotPrefix, markerNotSuffix, supportsDisjoint⟩ :=
    exists_isolated_split_of_not_repeated notRepeated
  let split :=
    correspondingIsolatedSplit_of_sameBrandtSignature same
      leftFactorization markerNotPrefix markerNotSuffix supportsDisjoint
  have recursive : split.RecursiveSignatures :=
    split.recursiveSignatures same leftFactorization markerNotPrefix
      markerNotSuffix supportsDisjoint
  have markerMember : marker ∈ left.toList := by
    rw [leftFactorization]
    simp
  have prefixSmaller :
      ∀ prefixWord,
        optionalWordOfList leftPrefix = some prefixWord →
          brandtSupportCard prefixWord < brandtSupportCard left := by
    intro prefixWord shape
    apply brandtSupportCard_lt_of_optionalWordOfList_of_missing
      (larger := left) (missing := marker) shape
    · intro letter member
      rw [leftFactorization]
      simp [member]
    · exact markerMember
    · exact markerNotPrefix
  have suffixSmaller :
      ∀ suffixWord,
        optionalWordOfList leftSuffix = some suffixWord →
          brandtSupportCard suffixWord < brandtSupportCard left := by
    intro suffixWord shape
    apply brandtSupportCard_lt_of_optionalWordOfList_of_missing
      (larger := left) (missing := marker) shape
    · intro letter member
      rw [leftFactorization]
      simp [member]
    · exact markerMember
    · exact markerNotSuffix
  have prefixDerivation :
      OptionalGapDerivesFor basis
        (optionalWordOfList leftPrefix)
        (optionalWordOfList split.rightPrefix) :=
    optionalGapDerives_of_optionalSame_of_smaller recursive.1
      prefixSmaller smallerDerivable
  have suffixDerivation :
      OptionalGapDerivesFor basis
        (optionalWordOfList leftSuffix)
        (optionalWordOfList split.rightSuffix) :=
    optionalGapDerives_of_optionalSame_of_smaller recursive.2
      suffixSmaller smallerDerivable
  have leftShape :
      left =
        isolatedRebuild marker
          (optionalWordOfList leftPrefix)
          (optionalWordOfList leftSuffix) := by
    apply Word.toList_injective
    rw [leftFactorization, isolatedRebuild_toList]
    simp
  have rightShape :
      right =
        isolatedRebuild marker
          (optionalWordOfList split.rightPrefix)
          (optionalWordOfList split.rightSuffix) := by
    apply Word.toList_injective
    rw [split.factorization, isolatedRebuild_toList]
    simp
  have wholeDerivation :=
    derives_isolatedRebuild basis marker prefixDerivation suffixDerivation
  rw [← leftShape, ← rightShape] at wholeDerivation
  exact notDerivable wholeDerivation

/-- A support-minimal nonderivable Brandt identity has repeated words on both
sides.  Minimality is measured by the distinct-letter support of the left
word; signature symmetry and support-card equality supply the right branch. -/
theorem minimalCounterexample_repeated
    {basis : List (Identity Nat)} {left right : Word Nat}
    (same : SameBrandtSignature left right)
    (notDerivable : ¬ Derives basis left right)
    (smallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameBrandtSignature smallerLeft smallerRight →
          brandtSupportCard smallerLeft < brandtSupportCard left →
            Derives basis smallerLeft smallerRight) :
    RepeatedWord left ∧ RepeatedWord right := by
  have leftRepeated :=
    repeatedWord_left_of_minimalSupport same notDerivable
      smallerDerivable
  have supportCardEq :=
    brandtSupportCard_eq_of_sameBrandtSignature same
  have reverseNotDerivable : ¬ Derives basis right left := by
    intro reverseDerivation
    exact notDerivable reverseDerivation.symm
  have rightSmallerDerivable :
      ∀ {smallerLeft smallerRight : Word Nat},
        SameBrandtSignature smallerLeft smallerRight →
          brandtSupportCard smallerLeft < brandtSupportCard right →
            Derives basis smallerLeft smallerRight := by
    intro smallerLeft smallerRight smallerSame smallerBound
    apply smallerDerivable smallerSame
    rw [supportCardEq]
    exact smallerBound
  have rightRepeated :=
    repeatedWord_left_of_minimalSupport same.symm reverseNotDerivable
      rightSmallerDerivable
  exact ⟨leftRepeated, rightRepeated⟩

end SemigroupBasis.CoRoots.S5_415
