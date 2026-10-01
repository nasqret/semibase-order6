import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeNormal
import SemigroupBasis.CoRoots.Order6FactorPairS5_83S5_84Transport

/-!
# Transporting the four-law intersection from `S5_83^op` to `S5_84^op`

`S5_83` and `S5_84` have the same unrestricted identity theory.  The shared
normal-form theorem therefore gives the same four-law intersection basis when
the second factor is replaced by `S5_84^op`.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeTransport

open SemigroupBasis

/-- The four-law `S3_16` / `S5_84^op` intersection basis obtained by exact
identity-theory transport on the second coordinate. -/
def intersectionBasisS5_84Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.intersectionBasis.transferTheories
    (fun _ => Iff.rfl)
    SemigroupBasis.CoRoots.Order6FactorPairS5_83S5_84Transport.sameTheoryS5_83OppositeS5_84Opposite

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeTransport
