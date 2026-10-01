import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15S4_96RelativeLift
import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Examples.LeftNormalBandFifteen

/-!
# Unrestricted C3 completeness for the bridge-patched `S3_15 × S4_96` pair

The left factor supplies the common first letter. The complete affine-parity
theory supplies an arbitrary-word derivation; its three axioms are lifted
under a parity-neutral, nonempty double copy of that first letter. The frozen
seventh bridge remains a named literal displayed-law derivation and is
handled directly by the public factor-valid completeness theorem.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15S4_96

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15S4_96

/-- The exact undermerge witness is discharged by its frozen seventh law,
not by a finite window or the superseded six-law source contract. -/
theorem bridge_factor_valid_derivation :
    Derives targetBasis
      (Word.mk 0 [0, 1, 2, 0, 1])
      (Word.mk 0 [1, 0, 2, 0, 1]) := by
  simpa [bridgeIdentity] using derivesBridge

/-- Both exact factor theories imply a derivation from the displayed seven
laws for every identity over arbitrary nonempty natural-variable words. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_96.table.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  by_cases bridgeCase : identity = bridgeIdentity
  · subst identity
    exact derivesBridge
  · have leftTransparent :
        identity.SatisfiedBy leftNormalBandFifteen.semigroup := by
      simpa only [SemigroupBasis.Generated.S3_15.table_eq_catalogue_model]
        using leftValid
    have heads : identity.lhs.head = identity.rhs.head :=
      leftNormalBandFifteenValid_head_eq identity leftTransparent
    have affineValid :
        identity.SatisfiedBy affineParityFour.semigroup := by
      simpa only [SemigroupBasis.Generated.S4_96.table] using rightValid
    have affineDerivation :
        Derives affineParityFourBasis identity.lhs identity.rhs :=
      affineParityFourBasis_complete.2 identity affineValid
    let initial : Word Nat :=
      Word.singleton identity.lhs.head ++
        Word.singleton identity.lhs.head
    have expandedLeft :
        Derives targetBasis identity.lhs
          (initial ++ identity.lhs) := by
      simpa [initial] using derivesHeadDoubleExpansion identity.lhs
    have expandedRight :
        Derives targetBasis identity.rhs
          (initial ++ identity.rhs) := by
      simpa [initial, heads] using derivesHeadDoubleExpansion identity.rhs
    have transported :
        Derives targetBasis
          (initial ++ identity.lhs)
          (initial ++ identity.rhs) :=
      liftAffineUnderPrefixIdentity affineDerivation initial
    exact expandedLeft.trans (transported.trans expandedRight.symm)

/-- The bridge-patched seven-law basis is unrestrictedly complete for the
intersection of the two exact stored factor theories. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_96.table.semigroup
      targetBasis where
  leftModels := basisS3_15S4_96_left_models
  rightModels := basisS3_15S4_96_right_models
  complete := derives_of_factor_valid

/-- Public proof-producing C3 normalizer with both arbitrary-word fields;
the quotient construction is applied only after independent completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_96.table.semigroup
      targetBasis :=
  LayerCCommon.IntersectionBasis.toQuotientNormalizer intersectionBasis

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15S4_96

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2

open SemigroupBasis

/-- The sixth unrestricted Layer-C normalizer, isolated from the opposite-left
and `S3_11` families and bound to the exact seven-law bridge contract. -/
noncomputable def normalizerS3_15S4_96 :
    IntersectionNormalizer
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_96.table.semigroup
      basisS3_15S4_96 :=
  S3_15S4_96.intersectionNormalizer

end SemigroupBasis.CoRoots.Order6L3HeavyRank2
