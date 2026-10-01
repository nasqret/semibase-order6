import SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12.Completeness
import SemigroupBasis.Examples.FirstLetterThreeNilpotentFour
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Generated.S4_13
import SemigroupBasis.Generated.S4_39

/-!
# Rank-10 target factor variants

The seven authenticated order-six targets use three concrete subdirect
factor pairs with the same intersection theory.  This file transports the
kernel-green `S3_15 / S4_12` proof to `S3_15 / S4_13`, and replays its long
head/support/parity macro for `S3_11 / S4_39`.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Cyclic representative variant -/

theorem basis_s4_13_models :
    Models SemigroupBasis.Generated.S4_13.table.semigroup basis := by
  intro identity member
  have validOnS4_12 := basis_s4_12_models identity member
  have derivation :=
    SemigroupBasis.Generated.S4_12.representative_basis.2
      identity validOnS4_12
  exact derivation.sound
    SemigroupBasis.Generated.S4_13.representative_basis.1

theorem derives_of_s3_15_s4_13_valid
    (identity : Identity Nat)
    (headSupportValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup)
    (cyclicValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_13.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have derivation :=
    SemigroupBasis.Generated.S4_13.representative_basis.2
      identity cyclicValid
  have s4_12Valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_12.table.semigroup :=
    derivation.sound
      SemigroupBasis.Generated.S4_12.representative_basis.1
  exact derives_of_s3_15_s4_12_valid
    identity headSupportValid s4_12Valid

def intersectionBasisS4_13 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_13.table.semigroup basis where
  leftModels := basis_s3_15_models
  rightModels := basis_s4_13_models
  complete := derives_of_s3_15_s4_13_valid

/-! ## Parity-zero / first-letter-nilpotent variant -/

private def variantToFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def variantToFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basis_s3_11_models :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table basis variantToFinThree (by decide)

set_option maxRecDepth 100000 in
theorem basis_s4_39_models :
    Models SemigroupBasis.Generated.S4_39.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_39.table basis variantToFinFour (by decide)

theorem derives_of_s3_11_s4_39_valid
    (identity : Identity Nat)
    (parityValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup)
    (headLengthValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_39.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have parityValid' :
      identity.SatisfiedBy parityZeroThree.semigroup := by
    change identity.SatisfiedBy parityZeroThree.semigroup at parityValid
    exact parityValid
  have headLengthValid' :
      identity.SatisfiedBy firstLetterThreeNilpotentFour.semigroup := by
    change identity.SatisfiedBy
      firstLetterThreeNilpotentFour.semigroup at headLengthValid
    exact headLengthValid
  rcases firstLetterThreeNilpotentValid_class
      identity headLengthValid' with shortOne | shortTwo | long
  · rw [shortOne.2.2]
    exact Derives.refl _
  · rw [shortTwo.2.2]
    exact Derives.refl _
  · exact derivesLongHeadSupportParity identity.lhs identity.rhs
      long.1 long.2.1 long.2.2
      (parityZeroValid_support identity parityValid')
      (parityZeroValid_parity identity parityValid')

def intersectionBasisS3_11S4_39 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.S4_39.table.semigroup basis where
  leftModels := basis_s3_11_models
  rightModels := basis_s4_39_models
  complete := derives_of_s3_11_s4_39_valid

end SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12
