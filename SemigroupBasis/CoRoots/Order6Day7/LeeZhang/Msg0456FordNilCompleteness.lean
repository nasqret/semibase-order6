import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilAlignment
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Unrestricted completeness of the exact msg0456 B23 for both literal
nil extensions. First establish arbitrary-word derivability by anchored
gap extraction, literal skeleton alignment, and guarded cap-two banks.
Only then expose the reviewed C1 normalizers. The second table uses the
proved unrestricted M18 same-theory transport, not a finite equality stamp. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

/-- Exact first order, capped multiplicity, and simple-prefix parity suffice
for arbitrary words over Nat. Every movement is discharged by B23 derivations. -/
theorem derivesOfSameSignature {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  obtain ⟨leftLabels, leftDerivation, leftCounts, leftSeen⟩ := rawAssembly left
  obtain ⟨rightLabels, rightDerivation, rightCounts, rightSeen⟩ := rawAssembly right
  have skeletonEq := separatorSkeleton_eq_of_sameSignature same
  rw [← skeletonEq] at rightDerivation rightCounts rightSeen
  have capped : CapTwoGuardedBank.SameCaps
      (separatorSkeleton left ++ S5_254.renderSquareBank leftLabels)
      (separatorSkeleton left ++ S5_254.renderSquareBank rightLabels) := by
    intro tested
    rw [leftCounts tested, rightCounts tested]
    exact same.counts tested
  have middle := listDerivesAlignBanks (separatorSkeleton left) leftLabels rightLabels leftSeen rightSeen capped
  have derived := leftDerivation.trans (middle.trans rightDerivation.symm)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord derived

theorem complete6543 (identity : Identity Nat) (valid : identity.SatisfiedBy table6543.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature (sameSignature_of_valid6543 identity valid)

theorem complete6605 (identity : Identity Nat) (valid : identity.SatisfiedBy table6605.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature ((valid6605_iff_sameSignature identity).1 valid)

def intersection6543 : IntersectionBasis fordTable.semigroup m18Table.semigroup basis where
  leftModels := fordModels
  rightModels := m18Models
  complete := by
    intro identity fordValid m18Valid
    exact complete6543 identity ((valid6543_iff_factors identity).2 ⟨fordValid, m18Valid⟩)

noncomputable def normalizer6543 : IntersectionNormalizer fordTable.semigroup m18Table.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection6543

/-- Reuse the established seed normal word and transport the actual factor
theory from M18.opposite to M18 using lower-factor completeness. -/
noncomputable def normalizer6605 :
    IntersectionNormalizer fordTable.semigroup m18Table.semigroup.opposite basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer normalizer6543
    (by intro law member; exact Derives.fromBasis member)
    (by intro identity valid; exact valid)
    (by intro identity valid; exact (m18_valid_iff_opposite identity).2 valid)

def intersection6605 : IntersectionBasis fordTable.semigroup m18Table.semigroup.opposite basis :=
  normalizer6605.toIntersectionBasis fordModels m18OppositeModels

noncomputable def oppositeNormalizer6543 :
    IntersectionNormalizer fordTable.semigroup.opposite m18Table.semigroup.opposite (reversedBasis basis) :=
  Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersection6543.oppositeReversed

noncomputable def oppositeNormalizer6605 :
    IntersectionNormalizer fordTable.semigroup.opposite m18Table.semigroup.opposite.opposite (reversedBasis basis) :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer oppositeNormalizer6543
    (by intro law member; exact Derives.fromBasis member)
    (by intro identity valid; exact valid)
    (by
      intro identity valid
      change identity.SatisfiedBy m18Table.semigroup at valid
      exact (m18_valid_iff_opposite identity).1 valid)

theorem normalizers_share_normal (word : Word Nat) :
    normalizer6605.normal word = normalizer6543.normal word := rfl

theorem oppositeNormalizers_share_normal (word : Word Nat) :
    oppositeNormalizer6605.normal word = oppositeNormalizer6543.normal word := rfl

theorem representative_basis6543 : BasisFor table6543.semigroup basis :=
  normalizer6543.basisFor fordModels m18Models subdirect6543

theorem representative_basis6605 : BasisFor table6605.semigroup basis :=
  normalizer6605.basisFor fordModels m18OppositeModels subdirect6605

theorem opposite_basis6543 : BasisFor table6543.semigroup.opposite (reversedBasis basis) :=
  representative_basis6543.oppositeReversed

theorem opposite_basis6605 : BasisFor table6605.semigroup.opposite (reversedBasis basis) :=
  representative_basis6605.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
