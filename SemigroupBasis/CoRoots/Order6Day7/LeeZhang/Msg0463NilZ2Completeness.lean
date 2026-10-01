import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463BalancedExtraction
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2Power
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-! Unrestricted completeness of the exact msg0463 twelve-law basis.
First prove actual derivability by exact-count separator extraction and
triple-guarded bank alignment. Only afterward expose the C1 normalizer
interface from that established completeness; the quotient wrapper is not
used as a premise of the derivation theorem. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

open SemigroupBasis

abbrev renderSquareBank := BalancedCore.renderSquareBank

noncomputable def separatorSkeleton (word : Word Nat) : List Nat :=
  S5_254.renderCanonicalSeparatorSkeleton
    (S5_254.canonicalSeparatorDecompositionData word.toList).1
    (S5_254.canonicalSeparatorDecompositionData word.toList).2

theorem rawAssembly (word : Word Nat) :
    ∃ labels, S5_107.ListDerives basis word.toList
        (separatorSkeleton word ++ renderSquareBank labels) ∧
      ∀ tested, (separatorSkeleton word ++ renderSquareBank labels).count tested =
        word.toList.count tested := by
  obtain ⟨labels, derivation, counts⟩ :=
    BalancedCore.listDerivesRawSeparatorAssembly (S5_254.canonicalSeparatorDecompositionData_spec word.toList)
  refine ⟨labels, ?_, ?_⟩
  · simpa [separatorSkeleton, renderSquareBank] using transportBalancedList derivation
  · simpa [separatorSkeleton, renderSquareBank] using counts

theorem separatorSkeleton_eq_of_sameSignature {left right : Word Nat}
    (same : Msg0446NilZ2.SameSignature left right) :
    separatorSkeleton left = separatorSkeleton right :=
  S5_254.canonicalSeparatorSkeletonAlignment left right same.toM18
    (S5_254.canonicalSeparatorDecompositionData left.toList).1
    (S5_254.canonicalSeparatorDecompositionData right.toList).1
    (S5_254.canonicalSeparatorDecompositionData left.toList).2
    (S5_254.canonicalSeparatorDecompositionData right.toList).2
    (S5_254.canonicalSeparatorDecompositionData_spec left.toList)
    (S5_254.canonicalSeparatorDecompositionData_spec right.toList)

/-- All words and substitutions are unrestricted; no screen bound occurs
in this theorem or any of its premises. -/
theorem derivesOfSameSignature {left right : Word Nat}
    (same : Msg0446NilZ2.SameSignature left right) : Derives basis left right := by
  obtain ⟨leftLabels, leftDerivation, leftCounts⟩ := rawAssembly left
  obtain ⟨rightLabels, rightDerivation, rightCounts⟩ := rawAssembly right
  have skeletonEq := separatorSkeleton_eq_of_sameSignature same
  rw [← skeletonEq] at rightDerivation rightCounts
  have capped : CapThreeBank.SameCaps
      (separatorSkeleton left ++ renderSquareBank leftLabels)
      (separatorSkeleton left ++ renderSquareBank rightLabels) := by
    intro letter
    rw [leftCounts letter, rightCounts letter]
    exact same.counts letter
  have middle := listDerivesAlignBanks (separatorSkeleton left) leftLabels rightLabels capped
  have derivation := leftDerivation.trans (middle.trans rightDerivation.symm)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord derivation

theorem complete9386 (identity : Identity Nat) (valid : identity.SatisfiedBy target.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature (Msg0446NilZ2.sameSignature_of_valid9386 identity valid)

theorem m18Models : Models Msg0446NilZ2.m18Table.semigroup basis := by
  intro identity member
  exact Msg0446NilZ2.m18Projection9386.pushforwardIdentity identity (models9386 identity member)

theorem exponentModels : Models Msg0446NilZ2.exponentTable.semigroup basis := by
  intro identity member
  exact Msg0446NilZ2.exponentProjection9386.pushforwardIdentity identity (models9386 identity member)

/-- The actual S5_254 by S4_40 intersection, with a proved unrestricted converse. -/
def intersection : IntersectionBasis
    Msg0446NilZ2.m18Table.semigroup Msg0446NilZ2.exponentTable.semigroup basis where
  leftModels := m18Models
  rightModels := exponentModels
  complete := by
    intro identity leftValid rightValid
    exact complete9386 identity ((Msg0446NilZ2.valid9386_iff_factors identity).2 ⟨leftValid, rightValid⟩)

noncomputable def normalizer : IntersectionNormalizer
    Msg0446NilZ2.m18Table.semigroup Msg0446NilZ2.exponentTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection

noncomputable def oppositeNormalizer : IntersectionNormalizer
    Msg0446NilZ2.m18Table.semigroup.opposite Msg0446NilZ2.exponentTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersection.oppositeReversed

theorem representative_basis : BasisFor target.semigroup basis :=
  normalizer.basisFor m18Models exponentModels Msg0446NilZ2.subdirect9386

theorem opposite_basis : BasisFor target.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2
