import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_516RelativeLift
import SemigroupBasis.CoRoots.S5_516Completeness
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Independent unrestricted S3_15op × S5_516 rank-057 seed

The exact existing S5_516 semantic classification says every valid identity
is either literally identical or both words have length at least three.
For long words the target's explicit three-step macro duplicates the final,
the target's four-step guarded suffix-swap lifts every complete lower-order
derivation, and the left factor fixes the common final. This proves the
unrestricted intersection before its quotient normalizer.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_516

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank057.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_516.table.semigroup

private theorem rank057_leftTable_eq :
    Rank057.leftTable =
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

theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank057.basis toFinThree (by decide)

theorem modelsRight : Models rightFactor targetBasis :=
  Rank057.rightModels

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem splitStem_length_ge_two
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    2 ≤ (splitPrefixFinal word).1.length := by
  have lengths := congrArg List.length
    (toList_eq_splitPrefixFinal word)
  simp only [List.length_append, List.length_singleton] at lengths
  omega

/-- Frozen laws 06, 02, and 06 duplicate the final variable of every word
with at least three letters; no multiplicity assumption is needed. -/
theorem derivesDuplicateFinalOfLong
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives targetBasis word
      (word ++ Word.singleton word.final) := by
  have stemLong := splitStem_length_ge_two word long
  cases stemShape : (splitPrefixFinal word).1 with
  | nil =>
      simp [stemShape] at stemLong
  | cons first rest =>
      cases rest with
      | nil =>
          simp [stemShape] at stemLong
      | cons middleHead middleTail =>
          let firstWord := Word.singleton first
          let middleWord := Word.mk middleHead middleTail
          have shape :
              (firstWord ++ middleWord) ++
                  Word.singleton (splitPrefixFinal word).2 = word := by
            apply Word.toList_injective
            rw [Word.toList_append, Word.toList_append,
              Word.toList_singleton, Word.toList_singleton,
              toList_eq_splitPrefixFinal word, stemShape]
            simp [middleWord, Word.toList]
          have duplicated :=
            derivesFinalDuplicationTriple firstWord middleWord
              (Word.singleton (splitPrefixFinal word).2)
          rw [shape] at duplicated
          simpa only [split_final_eq] using duplicated

/-- Independent unrestricted completeness for the exact seven-law S5_516
rank block, using its already proved full lower-order word problem. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have exactClass :=
    SemigroupBasis.CoRoots.S5_516.valid_exactBasisClass
      identity rightValid
  rcases exactClass with literal |
    ⟨leftLong, rightLong, _sameSupport, _sameSimpleInitial⟩
  · rw [literal]
    exact Derives.refl _
  · have sourceDerivation :=
      SemigroupBasis.CoRoots.S5_516.representative_basis.2
        identity rightValid
    have same :=
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
        identity leftValid
    have finalEq := same.final_eq
    have leftDuplicate :=
      derivesDuplicateFinalOfLong identity.lhs leftLong
    have rightDuplicate :=
      derivesDuplicateFinalOfLong identity.rhs rightLong
    have lifted :=
      liftS5_516UnderGuardIdentity sourceDerivation
        (Word.singleton identity.lhs.final)
    have guarded :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans <| guarded.trans rightDuplicate.symm

def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Exact unrestricted intersection basis for the frozen rank-057 block. -/
def intersectionBasis :
    IntersectionBasis
      Rank057.leftTable.semigroup
      Rank057.rightTable.semigroup
      Rank057.basis := by
  rw [rank057_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization follows the independent unrestricted proof. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank057.leftTable.semigroup
      Rank057.rightTable.semigroup
      Rank057.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated S6_9639 representative endpoint. -/
theorem representative_basis_S6_9639 :
    BasisFor Rank057.S6_9639.table.semigroup Rank057.basis :=
  Rank057.S6_9639.representative_basis_of_normalizer
    intersectionNormalizer

/-- Its exact literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_9639 :
    BasisFor Rank057.S6_9639.table.semigroup.opposite
      (reversedBasis Rank057.basis) :=
  Rank057.S6_9639.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_516
