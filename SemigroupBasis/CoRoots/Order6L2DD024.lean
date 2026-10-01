import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

/-!
# Stable d024 cut/initial completeness surface

The implementation module proves the literal B10 basis complete for the
direct factor intersection `S3_16 × S5_804`.  This thin module gives that
root the stable L2D delivery names consumed by generated target witnesses and
regression modules.  It contains no copied normalization proof, theory
transfer, or bounded-search certificate.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD024

open SemigroupBasis

abbrev B10 : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.B10

abbrev B10ListDerives :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.B10ListDerives

abbrev SameCutInitialSignature :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.SameCutInitialSignature

abbrev cutInitialNormalList :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.cutInitialNormalList

abbrev cutInitialNormal :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.cutInitialNormal

/-- Every word's list derives to the deterministic global cut/initial normal
list under literal B10. -/
theorem listDerivesCutInitialNormal (word : Word Nat) :
    B10ListDerives word.toList (cutInitialNormalList word) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.listDerivesCutInitialNormal
    word

/-- Every word derives to its deterministic global cut/initial normal word. -/
theorem derivesCutInitialNormal (word : Word Nat) :
    Derives B10 word (cutInitialNormal word) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.derivesCutInitialNormal
    word

/-- Equality of the exact cut/initial signature is sufficient for a literal
B10 derivation. -/
theorem derivesOfSameCutInitialSignature
    {left right : Word Nat}
    (same : SameCutInitialSignature left right) :
    Derives B10 left right :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.derivesOfSameCutInitialSignature
    same

/-- Joint validity in the selected direct factors is complete for literal
B10. -/
theorem derivesOfFactorValidity
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup) :
    Derives B10 identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.derivesOfFactorValidity
    identity leftValid rightValid

/-- Stable direct `S3_16 × S5_804` intersection root for d024. -/
abbrev intersectionBasisS3_16S5_804 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup
      B10 :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial.intersectionBasisS3_16S5_804

end SemigroupBasis.CoRoots.Order6L2DD024
