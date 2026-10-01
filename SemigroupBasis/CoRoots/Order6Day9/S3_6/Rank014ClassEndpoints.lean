import SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014IntersectionCompleteness
import SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6239
import SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506
import SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_9880

/-!
# The three exact Rank014 classes, in both orientations

The unrestricted eleven-law intersection is S1's msg-0537 proof. The exact
finite tables and subdirect pairs are S3's independently recorded carrier
21297675. This module only assembles these already separated proof inputs;
it introduces neither a finite witness nor a completeness assumption.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_6.Rank014ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014SemanticBoundary

theorem intersectionBasis :
    IntersectionBasis Generated.S3_6.table.semigroup
      SemigroupBasis.CoRoots.S5_636.table.semigroup basis where
  leftModels := markerModels
  rightModels := lowerModels
  complete :=
    SemigroupBasis.CoRoots.Order6Day8.S3_6.Rank014IntersectionCompleteness.derivesOfFactorValid

namespace S6_6239

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6239.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6239.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6239.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_6239

namespace S6_6506

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_6506

namespace S6_9880

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_9880.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_9880.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_9880.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_9880

end SemigroupBasis.CoRoots.Order6Day9.S3_6.Rank014ClassEndpoints
