import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83OppositeNormal
import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196OppositeNormal
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Subdirect

/-!
# Widening right-zero factor-pair bases to `S3_15^op`

The opposite of `S3_15` contains the opposite of `S2_4` on the elements
with zero-based indices `1` and `2`. This module uses that embedding to
replace the `S2_4^op` factor in three existing unrestricted intersection
bases.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening

open SemigroupBasis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def s3_15OppositeTable : FiniteTable where
  order := SemigroupBasis.Generated.S3_15.table.order
  mul := fun left right =>
    SemigroupBasis.Generated.S3_15.table.mul right left
  assoc := fun left middle right =>
    (SemigroupBasis.Generated.S3_15.table.assoc
      right middle left).symm

private theorem s3_15OppositeTable_semigroup :
    s3_15OppositeTable.semigroup =
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite :=
  rfl

def s2_4OppositeIntoS3_15Opposite (value : Fin 2) : Fin 3 :=
  if value = 0 then (1 : Fin 3) else (2 : Fin 3)

theorem s2_4OppositeIntoS3_15Opposite_values :
    List.ofFn
      (fun value : Fin 2 =>
        (s2_4OppositeIntoS3_15Opposite value).val) = [1, 2] := by
  decide

/-- The right-zero semigroup `S2_4^op` on the nonzero elements of
`S3_15^op`. -/
def s2_4OppositeEmbeddingS3_15Opposite :
    Embedding
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := s2_4OppositeIntoS3_15Opposite
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

private theorem modelsS3_15OppositeDualBasis :
    Models
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.dualBasis := by
  simpa only [s3_15OppositeTable_semigroup] using
    (FiniteCertificate.checkModels_sound
      s3_15OppositeTable
      SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.dualBasis
      toFinThree
      (by decide))

private theorem modelsS3_15OppositeReversedS5_196Basis :
    Models
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis) := by
  simpa only [s3_15OppositeTable_semigroup] using
    (FiniteCertificate.checkModels_sound
      s3_15OppositeTable
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis)
      toFinThree
      (by decide))

private def widenLeftFactor
    {A : Type u} {B : Type v} {C : Type w} {X : Type z}
    {sourceLeft : Semigroup A} {targetLeft : Semigroup B}
    {rightFactor : Semigroup C}
    {candidate : List (Identity X)}
    (source : IntersectionBasis sourceLeft rightFactor candidate)
    (targetModels : Models targetLeft candidate)
    (into : Embedding sourceLeft targetLeft) :
    IntersectionBasis targetLeft rightFactor candidate where
  leftModels := targetModels
  rightModels := source.rightModels
  complete := by
    intro identity targetValid rightValid
    exact source.complete identity
      (into.pullback_identity identity targetValid) rightValid

/-- Unrestricted joint basis for `S3_15^op` and `S5_83`, retaining the
existing six-law `dualBasis`. -/
def intersectionBasisS5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.dualBasis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.DualNormal.dualIntersectionS5_83
    modelsS3_15OppositeDualBasis
    s2_4OppositeEmbeddingS3_15Opposite

/-- Unrestricted joint basis for `S3_15^op` and `S5_84`, retaining the
existing six-law `dualBasis`. -/
def intersectionBasisS5_84 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.dualBasis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite.DualNormal.dualIntersectionS5_84
    modelsS3_15OppositeDualBasis
    s2_4OppositeEmbeddingS3_15Opposite

/-- Unrestricted joint basis for `S3_15^op` and `S5_196`. The source
`S2_4`/`S5_196^op` basis is transported by reversing every identity before
the left factor is widened. -/
def intersectionBasisS5_196 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis) :=
  widenLeftFactor
    (SemigroupBasis.IntersectionBasis.oppositeLeftOfOppositeRight
      SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.factorIntersectionBasis)
    modelsS3_15OppositeReversedS5_196Basis
    s2_4OppositeEmbeddingS3_15Opposite

end SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening
