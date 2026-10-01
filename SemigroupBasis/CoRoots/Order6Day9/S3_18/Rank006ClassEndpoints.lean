import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection
import SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006

/-!
# Rank006: the approved thirteen-law Sigma+ sigmaPlus for both actual classes

The unrestricted canonical-tile converse is combined with S3's unchanged
finite pairs, independently recorded by carrier 21353715. Both classes use
the actual direct C3 / S4_69 pair. This introduces only the representative
and opposite class endpoints; it does not alter any finite witness.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection

namespace S6_14937

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_14937.table

theorem basisFor : BasisFor table.semigroup sigmaPlus :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_14937.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis sigmaPlus) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_14937.pairOpposite

theorem models : Models table.semigroup sigmaPlus := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis sigmaPlus) := basisForOpposite.1

end S6_14937

namespace S6_15924

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_15924.table

theorem basisFor : BasisFor table.semigroup sigmaPlus :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_15924.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis sigmaPlus) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank006.S6_15924.pairOpposite

theorem models : Models table.semigroup sigmaPlus := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis sigmaPlus) := basisForOpposite.1

end S6_15924

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006ClassEndpoints
