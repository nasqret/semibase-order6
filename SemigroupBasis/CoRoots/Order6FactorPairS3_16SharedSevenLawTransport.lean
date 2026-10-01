import SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLawNormal
import SemigroupBasis.Generated.Order4RootTransfersLayer1
import SemigroupBasis.Nonfinite

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw

open SemigroupBasis
open SemigroupBasis.Examples

/-- Complete presentations by the same basis identify the full, unrestricted
identity theories of two semigroups. -/
private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {leftSemigroup : Semigroup A} {rightSemigroup : Semigroup B}
    {commonBasis : List (Identity X)}
    (leftBasis : BasisFor leftSemigroup commonBasis)
    (rightBasis : BasisFor rightSemigroup commonBasis) :
    SameIdentityTheoryOver leftSemigroup rightSemigroup X := by
  intro identity
  constructor
  · intro validInLeft valuation
    exact Derives.sound rightBasis.1
      (leftBasis.2 identity validInLeft) valuation
  · intro validInRight valuation
    exact Derives.sound leftBasis.1
      (rightBasis.2 identity validInRight) valuation

/-- Replace the right factor by a semigroup with exactly the same unrestricted
identity theory. -/
private def transportRightTheory
    {A : Type u} {B : Type v} {C : Type w} {X : Type z}
    {leftSemigroup : Semigroup A}
    {sourceRight : Semigroup B} {targetRight : Semigroup C}
    {candidate : List (Identity X)}
    (source : IntersectionBasis leftSemigroup sourceRight candidate)
    (sameTheory :
      SameIdentityTheoryOver sourceRight targetRight X) :
    IntersectionBasis leftSemigroup targetRight candidate where
  leftModels := source.leftModels
  rightModels :=
    source.rightModels.transportIdentityTheory sameTheory
  complete := by
    intro identity validLeft validTargetRight
    exact source.complete identity validLeft
      ((sameTheory identity).mpr validTargetRight)

theorem s5_779OppositeBasis_eq_s5_809Basis :
    reversedBasis
        SemigroupBasis.Generated.Order4RootTransfers.S5_779.targetBasis =
      SemigroupBasis.CoRoots.S5_809.basis := by
  rfl

/-- `S5_809` and `S5_779ᵒᵖ` have the same complete two-law presentation,
so their full identity theories agree. -/
theorem s5_809SameTheoryS5_779Opposite :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_809.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_779.table.semigroup.opposite
      Nat := by
  apply sameIdentityTheoryOverOfCommonBasis
    (commonBasis := SemigroupBasis.CoRoots.S5_809.basis)
  · exact SemigroupBasis.CoRoots.S5_809.representative_basis
  · rw [← s5_779OppositeBasis_eq_s5_809Basis]
    exact
      SemigroupBasis.Generated.Order4RootTransfers.S5_779.opposite_basis

/-- Transported endpoint for the `S3_16 × S5_779ᵒᵖ` factor obligation
associated with `S6_12776`. -/
def s3_16S5_779OppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_779.table.semigroup.opposite
      basis :=
  transportRightTheory s3_16S5_809IntersectionBasis
    s5_809SameTheoryS5_779Opposite

theorem s5_902Basis_eq_edmundsBasis :
    SemigroupBasis.Generated.Order4RootTransfers.S5_902.targetBasis =
      edmundsFiveTwoFourBasis := by
  rfl

/-- `S4_75` and `S5_902` have the same complete Edmunds presentation,
again yielding exact unrestricted theory equality rather than a bounded
fingerprint match. -/
theorem s4_75SameTheoryS5_902 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S4_75.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_902.table.semigroup
      Nat := by
  apply sameIdentityTheoryOverOfCommonBasis
    (commonBasis := edmundsFiveTwoFourBasis)
  · exact SemigroupBasis.Generated.S4_75.representative_basis
  · rw [← s5_902Basis_eq_edmundsBasis]
    exact
      SemigroupBasis.Generated.Order4RootTransfers.S5_902.representative_basis

/-- Transported endpoint for the `S3_16ᵒᵖ × S5_902` factor obligation
associated with `S6_14262`. -/
def s3_16OppositeS5_902IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_902.table.semigroup
      basis :=
  transportRightTheory s3_16OppositeS4_75IntersectionBasis
    s4_75SameTheoryS5_902

end SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw
