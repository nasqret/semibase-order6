import SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026Intersection
import SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026

/-!
# Rank026: the corrected ten-law basis for both exact classes

S1's unrestricted guarded-replay B10 intersection is combined with S3's
unchanged finite pairs, independently recorded by carrier 21354504.
Both classes use the common S3_6-opposite / S5_1099-direct pair. The
retired D026 scanner and S6_13549's older S4_76 wrapper are not imported.
Only representative/opposite class endpoints are introduced here.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026GuardedReplay
open SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026Intersection

namespace S6_13501

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13501.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13501.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13501.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13501

namespace S6_13549

abbrev table :=
  SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13549.table

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13549.pair

theorem basisForOpposite :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor
    SemigroupBasis.CoRoots.Order6Day9.S3FiniteWitnesses.Rank026.S6_13549.pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite :
    Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13549

end SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026ClassEndpoints
