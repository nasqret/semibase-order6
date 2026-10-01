import SemigroupBasis.CoRoots.Order6L3Root7.Bridge
import SemigroupBasis.CoRoots.S4_123
import SemigroupBasis.Generated.NormalBandTransfersLayer1
import SemigroupBasis.Generated.S3_11

/-!
# Factor variants for the rank-7 FCLP target family

The ten order-six representatives use six authenticated subdirect factor
pairs.  This module transfers the same FCLP completeness theorem across the
parity-zero, opposite-normal-band, rectangular-band, and promoted normal-band
factors used by those witnesses.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3Root7

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_s3_11_models :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table basis toFinThree (by decide)

theorem basis_s5_1053_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_1053.table
    basis toFinFive (by decide)

theorem basis_s5_1113_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_1113.table
    basis toFinFive (by decide)

theorem basis_s5_1133_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_1133.table
    basis toFinFive (by decide)

theorem basis_s4_123_models :
    Models SemigroupBasis.CoRoots.S4_123.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.S4_123.table basis toFinFour (by decide)

/-- Exact finite-table presentation of `S4_110ᵒᵖ`, used by the recorded
`S6_11914` subdirect witness. -/
def s4_110OppositeTable : FiniteTable where
  order := 4
  mul := fun left right =>
    SemigroupBasis.Generated.S4_110.table.mul right left
  assoc := by decide

theorem s4_110OppositeTable_semigroup :
    s4_110OppositeTable.semigroup =
      SemigroupBasis.Generated.S4_110.table.semigroup.opposite := rfl

theorem basis_s4_110Opposite_models :
    Models s4_110OppositeTable.semigroup basis :=
  FiniteCertificate.checkModels_sound
    s4_110OppositeTable basis toFinFour (by decide)

private theorem oppositeNormalBasis_models_normal :
    Models normalBandFour.semigroup normalBandFourOppositeBasis :=
  FiniteCertificate.checkModels_sound
    normalBandFour normalBandFourOppositeBasis toFinThree (by decide)

private theorem normalValid_of_oppositeNormalValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy s4_110OppositeTable.semigroup) :
    identity.SatisfiedBy normalBandFour.semigroup := by
  have oppositeValid :
      identity.SatisfiedBy normalBandFour.semigroup.opposite := by
    simpa [s4_110OppositeTable,
      SemigroupBasis.Generated.S4_110.table] using valid
  have derivation :=
    normalBandFourOppositeBasis_complete.2 identity oppositeValid
  intro valuation
  exact derivation.sound oppositeNormalBasis_models_normal valuation

private theorem normalValid_of_normalBasis
    {carrier : Type}
    {factor : Semigroup carrier}
    (factorBasis : BasisFor factor normalBandBasis)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy factor) :
    identity.SatisfiedBy normalBandFour.semigroup := by
  have derivation := factorBasis.2 identity valid
  intro valuation
  exact derivation.sound normalBandFourBasis_models valuation

private theorem derivesOfS3_11NormalValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (normalValid :
      identity.SatisfiedBy normalBandFour.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have parityValid :
      identity.SatisfiedBy parityZeroThree.semigroup := by
    rw [← SemigroupBasis.Generated.S3_11.table_eq_catalogue_model]
    exact s3Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (normalBandValid_head_eq identity normalValid)
    (normalBandValid_final_eq identity normalValid)
    (normalBandValid_support_eq identity normalValid)
    (parityZeroValid_parity identity parityValid)

theorem derivesOfS3_11S4_110Valid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_110.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfS3_11NormalValid identity s3Valid <| by
    simpa [SemigroupBasis.Generated.S4_110.table] using s4Valid

def intersectionBasisS3_11S4_110 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.S4_110.table.semigroup
      basis where
  leftModels := basis_s3_11_models
  rightModels := basis_s4_110_models
  complete := derivesOfS3_11S4_110Valid

theorem derivesOfS3_11S4_110OppositeValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy s4_110OppositeTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfS3_11NormalValid identity s3Valid
    (normalValid_of_oppositeNormalValid identity s4Valid)

def intersectionBasisS3_11S4_110Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      s4_110OppositeTable.semigroup
      basis where
  leftModels := basis_s3_11_models
  rightModels := basis_s4_110Opposite_models
  complete := derivesOfS3_11S4_110OppositeValid

theorem derivesOfS2_2S5_1053Valid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have normalValid :=
    normalValid_of_normalBasis
      SemigroupBasis.Generated.NormalBandTransfers.S5_1053.representative_basis
      identity s5Valid
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (normalBandValid_head_eq identity normalValid)
    (normalBandValid_final_eq identity normalValid)
    (normalBandValid_support_eq identity normalValid)
    (cyclicValid_parity_eq identity cyclicValid)

def intersectionBasisS2_2S5_1053 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1053.table.semigroup
      basis where
  leftModels := basis_s2_2_models
  rightModels := basis_s5_1053_models
  complete := derivesOfS2_2S5_1053Valid

theorem derivesOfS2_2S5_1113Valid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have normalValid :=
    normalValid_of_normalBasis
      SemigroupBasis.Generated.NormalBandTransfers.S5_1113.representative_basis
      identity s5Valid
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (normalBandValid_head_eq identity normalValid)
    (normalBandValid_final_eq identity normalValid)
    (normalBandValid_support_eq identity normalValid)
    (cyclicValid_parity_eq identity cyclicValid)

def intersectionBasisS2_2S5_1113 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1113.table.semigroup
      basis where
  leftModels := basis_s2_2_models
  rightModels := basis_s5_1113_models
  complete := derivesOfS2_2S5_1113Valid

theorem derivesOfS2_2S5_1133Valid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have normalValid :=
    normalValid_of_normalBasis
      SemigroupBasis.Generated.NormalBandTransfers.S5_1133.representative_basis
      identity s5Valid
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (normalBandValid_head_eq identity normalValid)
    (normalBandValid_final_eq identity normalValid)
    (normalBandValid_support_eq identity normalValid)
    (cyclicValid_parity_eq identity cyclicValid)

def intersectionBasisS2_2S5_1133 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1133.table.semigroup
      basis where
  leftModels := basis_s2_2_models
  rightModels := basis_s5_1133_models
  complete := derivesOfS2_2S5_1133Valid

theorem derivesOfS3_11S4_123Valid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S4_123.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have parityValid :
      identity.SatisfiedBy parityZeroThree.semigroup := by
    rw [← SemigroupBasis.Generated.S3_11.table_eq_catalogue_model]
    exact s3Valid
  have rectangularValid :
      identity.SatisfiedBy rectangularBandFour.semigroup := s4Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (rectangularBandFourValid_head_eq identity rectangularValid)
    (rectangularBandFourValid_final_eq identity rectangularValid)
    (parityZeroValid_support identity parityValid)
    (parityZeroValid_parity identity parityValid)

def intersectionBasisS3_11S4_123 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.CoRoots.S4_123.table.semigroup
      basis where
  leftModels := basis_s3_11_models
  rightModels := basis_s4_123_models
  complete := derivesOfS3_11S4_123Valid

end SemigroupBasis.CoRoots.Order6L3Root7
