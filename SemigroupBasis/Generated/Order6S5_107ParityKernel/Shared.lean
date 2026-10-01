import SemigroupBasis.CoRoots.Order6FactorPairS2S5107ParityKernel
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_11

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared

open SemigroupBasis

private abbrev candidateBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis

abbrev basis : List (Identity Nat) := candidateBasis

theorem basis_length : basis.length = 19 :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.basis_length

/-- The source-complete parity-kernel theorem closes the direct
`S2_2`/`S5_107` intersection. -/
def s2S5IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      basis where
  leftModels :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.modelsS2_2
  rightModels :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.modelsS5_107
  complete := by
    intro identity leftValid rightValid
    have same :=
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameFactorSignatureOfFactorValid
        identity leftValid rightValid
    exact
      SemigroupBasis.CoRoots.Order6FactorPairS2S5107ParityKernel.parityKernelLift_proved
        (SemigroupBasis.CoRoots.Order6FactorPairS2S5107ParityKernel.sealedS5DerivationOfSameFactorSignature
          same)
        same.parity

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem s3Checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.S3_11.table basis toFinThree = true := by
  decide

/-- Every displayed candidate law also holds in `S3_11`. -/
theorem modelsS3_11 :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table basis toFinThree s3Checked

private def cyclicIntoS3_11 (value : Fin 2) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else (1 : Fin 3)

/-- The nonzero group part of `S3_11 = C2^0` is an explicit copy of the
`S2_2` cyclic factor. This is the lane-local instance of the existing
order-six widening argument. -/
private def cyclicEmbeddingS3_11 :
    Embedding SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := cyclicIntoS3_11
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

/-- Widen the cyclic factor to `S3_11 = C2^0`. -/
def s3S5IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      basis where
  leftModels := modelsS3_11
  rightModels := s2S5IntersectionBasis.rightModels
  complete := by
    intro identity leftValid rightValid
    have cyclicValid :=
      cyclicEmbeddingS3_11.pullback_identity identity leftValid
    exact s2S5IntersectionBasis.complete identity cyclicValid rightValid

end SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared
