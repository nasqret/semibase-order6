import SemigroupBasis.CoRoots.S5_841CompletenessBridge
import SemigroupBasis.CoRoots.S5_841Segmentation

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis

/-- Edmunds' twelve-law system is complete for the historical `M20` table.
The unrestricted endpoint follows from the concrete six-case block witness
and the unconditional two-limited segmentation theorem. -/
theorem m20Completeness : M20CompletenessObligation :=
  m20Completeness_of_segmentation
    quadraticBlockPermutationSixCase m20SegmentationCompleteness

/-- Unconditional basis endpoint for Edmunds' historical `M20` table. -/
theorem publishedM20BasisFor :
    BasisFor publishedM20Table.semigroup basis :=
  publishedM20BasisFor_of_completeness m20Completeness

/-- Unconditional direct basis endpoint for catalogue representative
`S5_841`. -/
theorem catalogueS5_841BasisFor :
    BasisFor table.semigroup basis :=
  catalogueS5_841BasisFor_of_publishedCompleteness m20Completeness

/-- Unconditional endpoint for the opposite catalogue table and the
literal reversed basis. -/
theorem catalogueS5_841OppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using catalogueS5_841BasisFor.oppositeReversed

/-- Aggregate audit surface exposing both anti-isomorphism orientations. -/
structure FamilyBasisEndpoints : Prop where
  direct : BasisFor table.semigroup basis
  opposite : BasisFor table.semigroup.opposite oppositeBasis

/-- The direct and opposite `S5_841` basis endpoints. -/
theorem endpoints : FamilyBasisEndpoints where
  direct := catalogueS5_841BasisFor
  opposite := catalogueS5_841OppositeBasisFor

end SemigroupBasis.CoRoots.S5_841
