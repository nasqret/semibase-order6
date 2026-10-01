import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005Intersection
import SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005

/-!
# Rank005: the original eleven-law basis for both exact classes

S1's unrestricted raw-eleven-law intersection is combined with S3's
unchanged finite pairs, independently recorded by carrier 21302898.
The seven historical extensions remain derived consequences, not axioms.
Only representative/opposite class endpoints are introduced here.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005GuardedReplay
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005Intersection

namespace S6_14933

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_14933.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_14933.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_14933.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_14933

namespace S6_15933

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_15933.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_15933.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank005.S6_15933.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_15933

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005ClassEndpoints
