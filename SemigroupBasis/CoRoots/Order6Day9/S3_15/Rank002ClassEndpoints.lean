import SemigroupBasis.CoRoots.Order6Day8.S3_15.Rank002Intersection
import SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13385
import SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13612

/-!
# The two exact Rank002 classes, in both orientations

The original eight-law intersection is S1's msg-0538 proof. S3 owns the
unchanged finite witnesses, independently recorded by carrier 21297675.
Representative and opposite endpoints retain the displayed/reversed basis
distinction and do not reuse a different historical class as a witness.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_15.Rank002ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day8.S3_15.Rank002Intersection

namespace S6_13385

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13385.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13385.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13385.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13385

namespace S6_13612

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13612.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13612.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank002.S6_13612.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13612

end SemigroupBasis.CoRoots.Order6Day9.S3_15.Rank002ClassEndpoints
