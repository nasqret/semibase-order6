import SemigroupBasis.CoRoots.Order6Day14.TwinsA.TwinsAPadding

namespace SemigroupBasis.CoRoots.Order6Day14.TwinsA

open SemigroupBasis

/-- Identity-coordinate identification of the literal left factor. -/
def leftIdentification : SplitSurjection
    Generated.Catalogue.S2_4.table.semigroup Examples.leftZeroTwo.semigroup where
  toFun := fun value => value
  map_mul := by decide
  preimage := fun value => value
  right_inverse := by intro value; rfl

/-- The right factor and the complete example both use the opposite table. -/
def rightIdentification : SplitSurjection
    Generated.Catalogue.S4_95.table.semigroup.opposite
    Examples.parityInitialFour.semigroup.opposite where
  toFun := fun value => value
  map_mul := by decide
  preimage := fun value => value
  right_inverse := by intro value; rfl

theorem anchorLeftValid (e : Identity Nat)
    (valid : e.SatisfiedBy
      Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup) :
    e.SatisfiedBy Examples.leftZeroTwo.semigroup := by
  have factorValid :=
    Order6Sunday.LateFinite.SigmaF137a.S6_14814.ontoLeft.pushforwardIdentity e valid
  exact leftIdentification.pushforwardIdentity e factorValid

theorem anchorRightValid (e : Identity Nat)
    (valid : e.SatisfiedBy
      Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup) :
    e.SatisfiedBy Examples.parityInitialFour.semigroup.opposite := by
  have factorValid :=
    Order6Sunday.LateFinite.SigmaF137a.S6_14814.ontoRight.pushforwardIdentity e valid
  exact rightIdentification.pushforwardIdentity e factorValid

theorem anchorBasis :
    BasisFor Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup basis := by
  refine ⟨Order6Sunday.TwinTwoLawFinite.A.S6_14814.models, ?_⟩
  intro e valid
  exact derives_of_factorValidity e (anchorLeftValid e valid) (anchorRightValid e valid)

theorem anchorBasisOpposite :
    BasisFor Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup.opposite
      (reversedBasis basis) :=
  anchorBasis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day14.TwinsA
