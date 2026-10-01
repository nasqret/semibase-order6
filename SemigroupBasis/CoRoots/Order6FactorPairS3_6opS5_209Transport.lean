import SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers
import SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Corrected.Shared
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers

/-!
# Transporting the corrected `S3_6^op` / `S5_209` intersection

`S5_209`, `S5_211`, and `S5_500` have the same already-complete four-law
basis.  This module records the resulting unrestricted theory equivalences and
uses `IntersectionBasis.transferTheories` to transport the repaired thirteen-law
intersection basis.  It deliberately contains no order-six target tables.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Transport

open SemigroupBasis

/-- `S5_209` and `S5_211` have the same unrestricted identity theory because
the existing lower-order proofs give them the same complete basis. -/
theorem sameTheoryS5_209S5_211 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S5_209.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.Generated.S5_209.representative_basis
    SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers.S5_211.representative_basis

/-- `S5_209` and `S5_500` have the same unrestricted identity theory because
the existing lower-order proofs give them the same complete basis. -/
theorem sameTheoryS5_209S5_500 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S5_209.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.Generated.S5_209.representative_basis
    SemigroupBasis.Generated.DualCappedMultipleBlockFiveTransfers.S5_500.representative_basis

abbrev correctedBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness.correctedBasis

/-- The corrected `S3_6^op` / `S5_209` intersection transported to `S5_211`. -/
def intersectionS3_6opS5_211 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness.correctedIntersectionBasis.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_211

/-- The corrected `S3_6^op` / `S5_209` intersection transported to `S5_500`. -/
def intersectionS3_6opS5_500 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness.correctedIntersectionBasis.transferTheories
    (fun _ => Iff.rfl)
    sameTheoryS5_209S5_500

end SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Transport
