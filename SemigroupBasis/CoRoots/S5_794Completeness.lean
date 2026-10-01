import SemigroupBasis.CoRoots.S5_794Segmentation

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis
open SemigroupBasis.Examples

/-- Endpoint capping preserves the complete sequence of first occurrences. -/
theorem firstOccurrenceSequence_endpointCap
    (letters : List Nat) :
    firstOccurrenceSequence (uniqueSeparatorEndpointCap letters) =
      firstOccurrenceSequence letters := by
  cases letters with
  | nil => rfl
  | cons head tail =>
      have derivation := listDerivesEndpointCap (head :: tail)
      obtain
        ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
          derivation.from_cons
      rw [targetShape]
      simpa [S5_107.listWordOfCons, Word.toList] using
        (derives_sameSignature wordDerivation).firstSequence.symm

/-- Edmunds' twelve deletion-closure laws are complete for the explicit
five-element monoid `M14`. -/
theorem m14Completeness : M14CompletenessObligation := by
  rintro ⟨left, right⟩ valid
  have signature : SameSignature left right :=
    sameSignature_of_valid ⟨left, right⟩ valid
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
          have capCounts :
              ∀ letter,
                leftCap.toList.count letter =
                  rightCap.toList.count letter := by
            intro letter
            rw [leftCapToList, rightCapToList,
              uniqueSeparatorEndpointCap_count,
              uniqueSeparatorEndpointCap_count]
            simpa [S5_107.cappedMultiplicity] using
              signature.block.capped letter
          have leftLimited :
              UniqueSeparatorTwoLimited leftCap.toList := by
            rw [leftCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk leftHead leftTail).toList
          have rightLimited :
              UniqueSeparatorTwoLimited rightCap.toList := by
            rw [rightCapToList]
            exact
              uniqueSeparatorEndpointCap_twoLimited
                (Word.mk rightHead rightTail).toList
          have capFirstSequence :
              firstOccurrenceSequence leftCap.toList =
                firstOccurrenceSequence rightCap.toList := by
            rw [leftCapToList, rightCapToList,
              firstOccurrenceSequence_endpointCap,
              firstOccurrenceSequence_endpointCap]
            exact signature.firstSequence
          have originalEquivalent :
              M14ListEquivalent
                (Word.mk leftHead leftTail).toList
                (Word.mk rightHead rightTail).toList :=
            m14ListEquivalent_of_valid
              (Word.mk leftHead leftTail)
              (Word.mk rightHead rightTail) valid
          have capEquivalent :
              M14ListEquivalent leftCap.toList rightCap.toList := by
            rw [leftCapToList, rightCapToList]
            exact
              (M14ListEquivalent.of_derives leftListDerivation).symm.trans
                (originalEquivalent.trans
                  (M14ListEquivalent.of_derives rightListDerivation))
          have capListDerivation :=
            listDerivesCappedOfCountsFirstSequence
              leftCap rightCap leftLimited rightLimited
              capCounts capFirstSequence capEquivalent
          have capWordDerivation :
              Derives basis leftCap rightCap := by
            have represented :
                S5_107.ListDerives basis
                  (leftCapHead :: leftCapTail)
                  (rightCapHead :: rightCapTail) := by
              simpa [leftCap, rightCap, S5_107.listWordOfCons,
                Word.toList] using capListDerivation
            simpa [leftCap, rightCap] using represented.toWord
          exact
            leftCapDerivation.trans
              (capWordDerivation.trans rightCapDerivation.symm)

theorem publishedM14BasisFor :
    BasisFor publishedM14Table.semigroup basis :=
  publishedM14BasisFor_of_completeness m14Completeness

theorem catalogueS5_802BasisFor :
    BasisFor Generated.Catalogue.S5_802.table.semigroup basis :=
  catalogueS5_802BasisFor_of_publishedCompleteness m14Completeness

end SemigroupBasis.CoRoots.S5_794
