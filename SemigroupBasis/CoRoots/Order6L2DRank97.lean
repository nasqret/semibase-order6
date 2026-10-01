import SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening
import SemigroupBasis.CoRoots.S5_516Completeness

/-!
# Unrestricted L2D rank-97 root: `S3_15 × S5_516`

The exact seven-law system is the delivery-rank-97 design packet with SHA-256
`aa774f5bcbcf191e9a6a1573e665143631a7f6f65daa535e78af13bf74d7eada`.
It is literally the existing unrestricted basis for
`S2_4 × S5_196ᵒᵖ`.

The proof first dualizes the established `S3_15ᵒᵖ × S5_196`
intersection.  It then replaces `S5_196ᵒᵖ` by the identity-equivalent
`S5_516`, using their common complete `initialMarkerBasis`.  No bounded
closure result, new normalizer, or finite certificate is used.
-/

namespace SemigroupBasis.CoRoots.Order6L2DRank97

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

def displayedBasisSHA256 : String :=
  "aa774f5bcbcf191e9a6a1573e665143631a7f6f65daa535e78af13bf74d7eada"

theorem basis_length : basis.length = 7 := by
  decide

private theorem s5_196OppositeInitialMarkerBasis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_516.initialMarkerBasis := by
  simpa only [
    SemigroupBasis.CoRoots.S5_516.initialMarkerBasis_eq_reversedS5_196,
    SemigroupBasis.CoRoots.S5_196.reversedBasis_eq_expected] using
      SemigroupBasis.CoRoots.S5_196Family.S5_196.opposite_basis_complete

private theorem s5_516InitialMarkerBasis :
    BasisFor
      SemigroupBasis.CoRoots.S5_516.table.semigroup
      SemigroupBasis.CoRoots.S5_516.initialMarkerBasis :=
  SemigroupBasis.CoRoots.S5_516.representative_basis.replace
    (by
      intro identity member valuation
      exact
        (SemigroupBasis.CoRoots.S5_516.initialMarkerAxiomsDeriveBasis
          identity member).sound
            SemigroupBasis.CoRoots.S5_516.representative_basis.1 valuation)
    SemigroupBasis.CoRoots.S5_516.basisAxiomsDeriveInitialMarker

private theorem sameTheoryS5_196OppositeS5_516
    (identity : Identity Nat) :
    identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite ↔
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_516.table.semigroup := by
  constructor
  · intro valid valuation
    exact
      (s5_196OppositeInitialMarkerBasis.2 identity valid).sound
        s5_516InitialMarkerBasis.1 valuation
  · intro valid valuation
    exact
      (s5_516InitialMarkerBasis.2 identity valid).sound
        s5_196OppositeInitialMarkerBasis.1 valuation

private abbrev sourceIntersection :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening.intersectionBasisS5_196

/-- Unrestricted basis for the intersection of the identity theories of
`S3_15` and `S5_516`. -/
def factorIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.CoRoots.S5_516.table.semigroup
      basis := by
  simpa only [Semigroup.opposite, reversedBasis_reversedBasis] using
    (SemigroupBasis.IntersectionBasis.oppositeReversed
      sourceIntersection).transferTheories
        (fun _ => Iff.rfl)
        sameTheoryS5_196OppositeS5_516

/-- Compatibility name consumed by generated order-six endpoints. -/
abbrev intersectionBasis := factorIntersectionBasis

end SemigroupBasis.CoRoots.Order6L2DRank97
