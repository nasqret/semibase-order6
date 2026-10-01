import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595TerminalCancellation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595HeavyCompletion
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Unrestricted completeness of the unchanged raw8, proved through its six-law subset.
Every word is in the simple, double, or heavy terminal stratum. Only after
closing all three branches are C1 and the reviewed basis transport applied. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595

open SemigroupBasis
open S4_71Suffix

theorem core_lower_models : Models lowerTable.semigroup coreBasis :=
  fun identity member => lower_valid_of_valid identity (core_models identity member)

theorem derives_of_valid_words (left right : Word Nat)
    (valid : ∀ valuation, table.semigroup.eval valuation left = table.semigroup.eval valuation right) :
    Derives coreBasis left right := by
  obtain ⟨leftFront, leftLast, rfl⟩ := existsEndWord left
  obtain ⟨rightFront, rightLast, rfl⟩ := existsEndWord right
  have equivalent : EndEquivalent leftFront leftLast rightFront rightLast := valid
  by_cases leftSimple : leftFront.count leftLast = 0
  · obtain ⟨lastEqual, rightSimple⟩ := simple_terminal_preserved leftFront rightFront leftLast rightLast equivalent leftSimple
    subst rightLast
    exact coreSuffixRules.derivesLists leftFront rightFront (Word.singleton leftLast)
      (simple_prefix_lower_equivalent leftFront rightFront leftLast equivalent leftSimple rightSimple)
  · by_cases leftDouble : leftFront.count leftLast = 1
    · obtain ⟨lastEqual, rightDouble⟩ := double_terminal_preserved leftFront rightFront leftLast rightLast equivalent leftDouble
      subst rightLast
      exact coreSuffixRules.derivesLists leftFront rightFront (Word.singleton leftLast)
        (double_prefix_lower_equivalent leftFront rightFront leftLast equivalent leftDouble rightDouble)
    · by_cases rightSimple : rightFront.count rightLast = 0
      · obtain ⟨lastEqual, impossible⟩ := simple_terminal_preserved rightFront leftFront rightLast leftLast equivalent.symm rightSimple
        subst leftLast
        exact False.elim (leftSimple impossible)
      · by_cases rightDouble : rightFront.count rightLast = 1
        · obtain ⟨lastEqual, impossible⟩ := double_terminal_preserved rightFront leftFront rightLast leftLast equivalent.symm rightDouble
          subst leftLast
          exact False.elim (leftDouble impossible)
        · have leftHeavy : 2 ≤ leftFront.count leftLast := by omega
          have rightHeavy : 2 ≤ rightFront.count rightLast := by omega
          obtain ⟨leftStem, leftDerivation⟩ := coreRules.derivesHeavyExtraction leftFront leftLast leftHeavy
          obtain ⟨rightStem, rightDerivation⟩ := coreRules.derivesHeavyExtraction rightFront rightLast rightHeavy
          have lowerOriginal : ∀ valuation,
              lowerTable.semigroup.eval valuation (endWord leftFront leftLast) =
              lowerTable.semigroup.eval valuation (endWord rightFront rightLast) :=
            lower_valid_of_valid ⟨endWord leftFront leftLast, endWord rightFront rightLast⟩ valid
          have lowerCubes : ∀ valuation,
              lowerTable.semigroup.eval valuation (cubicWord leftStem leftLast) =
              lowerTable.semigroup.eval valuation (cubicWord rightStem rightLast) := by
            intro valuation
            exact (Derives.sound core_lower_models leftDerivation valuation).symm.trans
              ((lowerOriginal valuation).trans (Derives.sound core_lower_models rightDerivation valuation))
          exact leftDerivation.trans
            ((coreRules.derivesCubeEndings leftStem rightStem leftLast rightLast lowerCubes).trans rightDerivation.symm)

theorem core_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives coreBasis identity.lhs identity.rhs := derives_of_valid_words identity.lhs identity.rhs valid

theorem core_representative_basis : BasisFor table.semigroup coreBasis := ⟨core_models, core_complete⟩

theorem raw_laws_derive_from_core (identity : Identity Nat) (member : identity ∈ basis) :
    Derives coreBasis identity.lhs identity.rhs := core_complete identity (models_raw identity member)

def coreIntersection : IntersectionBasis table.semigroup table.semigroup coreBasis where
  leftModels := core_models
  rightModels := core_models
  complete := fun identity valid _ => core_complete identity valid

noncomputable def coreNormalizer : IntersectionNormalizer table.semigroup table.semigroup coreBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer coreIntersection

noncomputable def normalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    coreNormalizer (fun identity member => Derives.fromBasis (core_subset_raw identity member))
    (fun _ valid => valid) (fun _ valid => valid)

def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup basis :=
  normalizer.toIntersectionBasis models_raw models_raw

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs := diagonalIntersection.complete identity valid valid

theorem representative_basis : BasisFor table.semigroup basis := ⟨models_raw, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

def oppositeIntersection : IntersectionBasis table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) where
  leftModels := models_opposite_raw
  rightModels := models_opposite_raw
  complete := fun identity valid _ => opposite_basis.2 identity valid

noncomputable def oppositeNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5595
