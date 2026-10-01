import SemigroupBasis.CoRoots.Order6FinalMarkerM2

namespace SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  reversedBasis SemigroupBasis.CoRoots.Order6FinalMarkerM2.basis

/-- Dualizing the already-proved `S3_6 x S5_213^op` intersection gives the
`S3_6^op x S5_213` intersection needed by two order-six roots. -/
def s3_6OppositeS5_213IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup
      basis :=
  SemigroupBasis.IntersectionBasis.oppositeLeftOfOppositeRight
    SemigroupBasis.CoRoots.Order6FinalMarkerM2.s3_6_s5_213OppositeIntersectionBasis

/-- `S5_213` and `S5_498` have the same already-certified complete basis. -/
theorem sameTheoryS5_213S5_498 (identity : Identity Nat) :
    identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup ↔
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup := by
  constructor
  · intro valid valuation
    exact Derives.sound
      SemigroupBasis.CoRoots.S5_213Family.S5_498.basis_complete.1
      (SemigroupBasis.CoRoots.S5_213Family.S5_213.basis_complete.2
        identity valid)
      valuation
  · intro valid valuation
    exact Derives.sound
      SemigroupBasis.CoRoots.S5_213Family.S5_213.basis_complete.1
      (SemigroupBasis.CoRoots.S5_213Family.S5_498.basis_complete.2
        identity valid)
      valuation

/-- Replace the right factor by its identity-equivalent `S5_498` sibling. -/
def s3_6OppositeS5_498IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup
      basis :=
  s3_6OppositeS5_213IntersectionBasis.transferTheories
    (fun _ => Iff.rfl) sameTheoryS5_213S5_498

end SemigroupBasis.CoRoots.Order6FinalMarkerM2OppositeLeft
