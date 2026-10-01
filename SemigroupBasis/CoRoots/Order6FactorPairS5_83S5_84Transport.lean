import SemigroupBasis.CoRoots.Order6FactorPairOppositeRightWidening
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.CoRoots.S5_83Family

/-!
# Transporting the `S5_83` factor-pair intersections to `S5_84`

The semigroups `S5_83` and `S5_84` have the same complete basis, as do
their opposites.  Their unrestricted identity theories therefore coincide,
so the existing intersections with `S5_83` transport directly to `S5_84`.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS5_83S5_84Transport

open SemigroupBasis

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

/-- `S5_83` and `S5_84` share their complete unrestricted identity theory. -/
theorem sameTheoryS5_83S5_84 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_83Family.S5_83.basis_complete
    SemigroupBasis.CoRoots.S5_83Family.S5_84.basis_complete

/-- The opposite semigroups also share their complete identity theory. -/
theorem sameTheoryS5_83OppositeS5_84Opposite :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite
      Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_83Family.S5_83.opposite_basis_complete
    SemigroupBasis.CoRoots.S5_83Family.S5_84.opposite_basis_complete

/-- The existing `S2_2`/`S5_83` intersection with `S5_84` substituted. -/
def s2_2S5_84IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.factorIntersectionBasis.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_83S5_84

/-- The widened `S3_11`/`S5_83` intersection with `S5_84` substituted. -/
def s3_11S5_84IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.intersectionBasisS5_83.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_83S5_84

/-- The reversed `S2_2`/`S5_83^op` intersection with `S5_84^op` substituted. -/
def s2_2S5_84OppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis) :=
  SemigroupBasis.CoRoots.Order6FactorPairOppositeRightWidening.intersectionBasisS2_2S5_83Opposite.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_83OppositeS5_84Opposite

end SemigroupBasis.CoRoots.Order6FactorPairS5_83S5_84Transport
