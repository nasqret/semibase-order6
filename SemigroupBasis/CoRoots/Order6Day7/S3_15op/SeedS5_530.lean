import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530FinalSemantics
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Independent unrestricted S3_15op × S5_530 rank-103 seed

This is the genuinely order-six Section 24.5 three-law basis. Actual opposite
left-factor validity fixes final variable and support; independently complete
`S5_530` validity fixes first-occurrence order and every multiplicity capped
at three. Finals with multiplicity at least three may be duplicated using the
exact anchored cap/gather calculus. For multiplicity one or two, the common
terminal letter is removed before unrestricted lower normalization: freshness
uses the true factor identity, while multiplicity two uses the separate
first-occurrence/capped-count stem invariant.

These exhaustive cases prove the exact unrestricted factor intersection
BEFORE quotient normalization and both authenticated S6_9739 orientations.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank103.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_530.table.semigroup

private theorem rank103_leftTable_eq :
    Rank103.leftTable =
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable := by
  change
    SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S3_15.table =
      SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.S3_15.table
  rw [SemigroupBasis.Generated.S3_15.table_eq_canonical_catalogue]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

set_option maxRecDepth 100000 in
/-- Check all three exact frozen laws on the canonical opposite left factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank103.basis toFinThree (by decide)

/-- Reuse the immutable three-law right-factor witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank103.rightModels

private theorem listWordOfCons_append_final
    (first : Nat) (rest : List Nat) (final : Nat) :
    SemigroupBasis.CoRoots.S5_107.listWordOfCons first rest ++
        Word.singleton final =
      wordOfPrefixFinal (first :: rest) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

/-- Genuine unrestricted completeness for the exact Section 24.5 system. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have lower :=
    SemigroupBasis.CoRoots.S5_530.representative_basis.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
      identity leftValid
  have finalEq := same.final_eq
  have capped := finalCappedCounts_of_valid identity rightValid finalEq
  by_cases leftHeavy : 3 ≤ identity.lhs.toList.count identity.lhs.final
  · have rightHeavy : 3 ≤ identity.rhs.toList.count identity.rhs.final := by
      apply Decidable.byContradiction
      intro notHeavy
      have rightLow : identity.rhs.toList.count identity.rhs.final < 3 := by
        omega
      simp only [Nat.min_def] at capped
      split at capped <;> split at capped <;> omega
    have leftDuplicate :=
      derivesDuplicateFinalOfThree identity.lhs leftHeavy
    have rightDuplicate :=
      derivesDuplicateFinalOfThree identity.rhs rightHeavy
    have lifted :=
      liftLowerUnderGuardIdentity lower
        (Word.singleton identity.lhs.final)
    have aligned :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans (aligned.trans rightDuplicate.symm)
  · have leftLow : identity.lhs.toList.count identity.lhs.final < 3 := by
      omega
    have rightLow : identity.rhs.toList.count identity.rhs.final < 3 := by
      apply Decidable.byContradiction
      intro notLow
      have rightHeavy : 3 ≤ identity.rhs.toList.count identity.rhs.final := by
        omega
      simp only [Nat.min_def] at capped
      split at capped <;> split at capped <;> omega
    have wholeCounts :
        identity.lhs.toList.count identity.lhs.final =
          identity.rhs.toList.count identity.rhs.final := by
      simp only [Nat.min_def] at capped
      split at capped <;> split at capped <;> omega
    have simpleIff := finalCountOneIff_of_valid
      identity rightValid finalEq
    cases leftStem : (splitPrefixFinal identity.lhs).1 with
    | nil =>
        have leftSimple :
            identity.lhs.toList.count identity.lhs.final = 1 := by
          rw [toList_eq_splitPrefixFinal, leftStem, split_final_eq]
          simp
        have rightSimple :
            identity.rhs.toList.count identity.rhs.final = 1 :=
          simpleIff.mp leftSimple
        have rightStem : (splitPrefixFinal identity.rhs).1 = [] :=
          splitStem_nil_of_sameLastSupport same rightSimple leftStem
        have leftReconstructed := wordOfPrefixFinal_split identity.lhs
        have rightReconstructed := wordOfPrefixFinal_split identity.rhs
        rw [leftStem] at leftReconstructed
        rw [rightStem] at rightReconstructed
        simp only [wordOfPrefixFinal_nil] at leftReconstructed
        simp only [wordOfPrefixFinal_nil] at rightReconstructed
        have splitFinals :
            (splitPrefixFinal identity.lhs).2 =
              (splitPrefixFinal identity.rhs).2 :=
          (split_final_eq identity.lhs).trans <|
            finalEq.trans (split_final_eq identity.rhs).symm
        rw [← leftReconstructed, ← rightReconstructed, splitFinals]
        exact Derives.refl _
    | cons leftFirst leftRest =>
        cases rightStem : (splitPrefixFinal identity.rhs).1 with
        | nil =>
            have rightSimple :
                identity.rhs.toList.count identity.rhs.final = 1 := by
              rw [toList_eq_splitPrefixFinal, rightStem, split_final_eq]
              simp
            have leftSimple :
                identity.lhs.toList.count identity.lhs.final = 1 :=
              simpleIff.mpr rightSimple
            have impossible :=
              splitStem_nil_of_sameLastSupport
                same.symm leftSimple rightStem
            rw [leftStem] at impossible
            contradiction
        | cons rightFirst rightRest =>
            let leftStemWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                leftFirst leftRest
            let rightStemWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                rightFirst rightRest
            let final := (splitPrefixFinal identity.lhs).2
            have splitFinals :
                (splitPrefixFinal identity.lhs).2 =
                  (splitPrefixFinal identity.rhs).2 :=
              (split_final_eq identity.lhs).trans <|
                finalEq.trans (split_final_eq identity.rhs).symm
            have finalIsLeft : final = identity.lhs.final :=
              split_final_eq identity.lhs
            have finalIsRight : final = identity.rhs.final :=
              finalIsLeft.trans finalEq
            have leftShape :
                leftStemWord ++ Word.singleton final = identity.lhs := by
              calc
                leftStemWord ++ Word.singleton final =
                    wordOfPrefixFinal (leftFirst :: leftRest) final := by
                  simpa [leftStemWord] using
                    listWordOfCons_append_final leftFirst leftRest final
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.lhs).1
                    (splitPrefixFinal identity.lhs).2 := by
                  rw [leftStem]
                _ = identity.lhs := wordOfPrefixFinal_split identity.lhs
            have rightShape :
                rightStemWord ++ Word.singleton final = identity.rhs := by
              calc
                rightStemWord ++ Word.singleton final =
                    rightStemWord ++ Word.singleton
                      (splitPrefixFinal identity.rhs).2 := by
                  simp only [final, splitFinals]
                _ = wordOfPrefixFinal
                    (rightFirst :: rightRest)
                    (splitPrefixFinal identity.rhs).2 := by
                  simpa [rightStemWord] using
                    listWordOfCons_append_final rightFirst rightRest
                      (splitPrefixFinal identity.rhs).2
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.rhs).1
                    (splitPrefixFinal identity.rhs).2 := by
                  rw [rightStem]
                _ = identity.rhs := wordOfPrefixFinal_split identity.rhs
            have wholeValid :
                (Identity.mk
                  (leftStemWord ++ Word.singleton final)
                  (rightStemWord ++ Word.singleton final)).SatisfiedBy
                    rightFactor := by
              simpa only [leftShape, rightShape] using rightValid
            have leftStemCount :
                leftStemWord.toList.count final + 1 =
                  identity.lhs.toList.count identity.lhs.final := by
              have counted :=
                congrArg (fun word : Word Nat =>
                  word.toList.count final) leftShape
              simpa [Word.toList_append, Word.toList_singleton,
                List.count_append, finalIsLeft] using counted
            have rightStemCount :
                rightStemWord.toList.count final + 1 =
                  identity.rhs.toList.count identity.rhs.final := by
              have counted :=
                congrArg (fun word : Word Nat =>
                  word.toList.count final) rightShape
              simpa [Word.toList_append, Word.toList_singleton,
                List.count_append, finalIsRight] using counted
            have sameStemCount :
                leftStemWord.toList.count final =
                  rightStemWord.toList.count final := by
              omega
            have lowStem : leftStemWord.toList.count final < 2 := by
              omega
            have stemDerivation :=
              lowFinal_stem_derivation final
                leftStemWord rightStemWord sameStemCount lowStem wholeValid
            have lifted :=
              liftLowerUnderGuardIdentity
                stemDerivation (Word.singleton final)
            simpa only [leftShape, rightShape] using lifted

/-- The exact unrestricted factor intersection, constructed independently. -/
def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Identify the independently proved intersection with the frozen envelope. -/
def intersectionBasis :
    IntersectionBasis
      Rank103.leftTable.semigroup
      Rank103.rightTable.semigroup
      Rank103.basis := by
  rw [rank103_leftTable_eq]
  exact displayedIntersectionBasis

/-- Introduce quotient normalization only after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank103.leftTable.semigroup
      Rank103.rightTable.semigroup
      Rank103.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Exact authenticated Section 24.5 representative endpoint. -/
theorem representative_basis_S6_9739 :
    BasisFor Rank103.S6_9739.table.semigroup Rank103.basis :=
  Rank103.S6_9739.representative_basis_of_normalizer intersectionNormalizer

/-- Exact literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_9739 :
    BasisFor Rank103.S6_9739.table.semigroup.opposite
      (reversedBasis Rank103.basis) :=
  Rank103.S6_9739.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530
