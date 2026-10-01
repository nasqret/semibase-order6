import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.EndpointCompleteness
import SemigroupBasis.Generated.BandEmbeddingTransfers
import SemigroupBasis.Generated.S4_64TransfersLayer1

/-!
# Exact factor variants for L1R group `43fb00e0b3bdd469`

Three members use the selected `S4_116op x S4_64` factor pair.  The five
remaining members use four authenticated theory-equal pairs:

* `S6_12324`: `S4_116op x S5_719`;
* `S6_12392`: `S4_116op x S5_728`;
* `S6_14080`: `S3_16op x S4_64`;
* `S6_14222` and `S6_14223`: `S3_16op x S5_891`.

The opposite left factors have the same complete right-regular-band theory,
and each order-five right factor has the same complete Edmunds `S4_64`
theory.  Hence every alternate pair transports to the fresh endpoint
completeness interface without changing the seven displayed identities.

Static source draft only: it is conditional on the imported endpoint route
becoming kernel-green on Helios and is not itself kernel evidence.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L1RRank1

/-! ## Exact alternate factor tables -/

abbrev s3_16 : FiniteTable :=
  SemigroupBasis.Generated.S3_16.table

/-- Exact opposite orientation used by `S6_14080`, `S6_14222`, and
`S6_14223`. -/
def s3_16op : FiniteTable :=
  FactorTables.oppositeTable s3_16

theorem s3_16op_semigroup :
    s3_16op.semigroup = s3_16.semigroup.opposite :=
  FactorTables.oppositeTable_semigroup s3_16

abbrev s5_719 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_719.table

abbrev s5_728 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_728.table

abbrev s5_891 : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_891.table

/-! ## Exact right-regular-band theory transfer -/

private theorem s4_116op_models_rightRegularBandBasis :
    Models FactorTables.s4_116op.semigroup
      (reversedBasis leftRegularBandThreeBasis) := by
  simpa only [FactorTables.s4_116op_semigroup] using
    SemigroupBasis.Generated.BandEmbeddingTransfers.S4_116.opposite_basis.1

private theorem s3_16op_models_rightRegularBandBasis :
    Models s3_16op.semigroup
      (reversedBasis leftRegularBandThreeBasis) := by
  simpa only [s3_16op_semigroup,
    leftRegularBandThreeOppositeBasis] using
    SemigroupBasis.Generated.S3_16.opposite_basis.1

/-- Every displayed G43 law valid in `S4_116op` is also valid in the
theory-equal `S3_16op` factor. -/
theorem basis_s3_16op_models :
    Models s3_16op.semigroup basis := by
  intro identity member
  have selectedValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup :=
    left_models identity member
  have catalogueOppositeValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_116.table.semigroup.opposite := by
    simpa only [FactorTables.s4_116op_semigroup] using selectedValid
  have derivation :=
    SemigroupBasis.Generated.BandEmbeddingTransfers.S4_116.opposite_basis.2
      identity catalogueOppositeValid
  exact derivation.sound s3_16op_models_rightRegularBandBasis

/-- Validity in `S3_16op` transports to validity in the selected
`S4_116op` coordinate. -/
private theorem s3_16op_valid_to_s4_116op
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s3_16op.semigroup) :
    identity.SatisfiedBy FactorTables.s4_116op.semigroup := by
  have generatedOppositeValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup.opposite := by
    simpa only [s3_16op_semigroup] using valid
  have derivation :
      Derives (reversedBasis leftRegularBandThreeBasis)
        identity.lhs identity.rhs := by
    simpa only [leftRegularBandThreeOppositeBasis] using
      SemigroupBasis.Generated.S3_16.opposite_basis.2
        identity generatedOppositeValid
  exact derivation.sound s4_116op_models_rightRegularBandBasis

/-! ## Exact `S4_64`-theory transfers -/

private theorem s5_719_models_s4_64_basis :
    Models s5_719.semigroup edmundsFourSixtyFourBasis := by
  simpa only
      [SemigroupBasis.Generated.S4_64Transfers.S5_719.transferBasis_eq_source]
    using
      SemigroupBasis.Generated.S4_64Transfers.S5_719.transferred_basis.1

private theorem s5_728_models_s4_64_basis :
    Models s5_728.semigroup edmundsFourSixtyFourBasis := by
  simpa only
      [SemigroupBasis.Generated.S4_64Transfers.S5_728.transferBasis_eq_source]
    using
      SemigroupBasis.Generated.S4_64Transfers.S5_728.transferred_basis.1

private theorem s5_891_models_s4_64_basis :
    Models s5_891.semigroup edmundsFourSixtyFourBasis := by
  simpa only
      [SemigroupBasis.Generated.S4_64Transfers.S5_891.transferBasis_eq_source]
    using
      SemigroupBasis.Generated.S4_64Transfers.S5_891.transferred_basis.1

theorem basis_s5_719_models :
    Models s5_719.semigroup basis := by
  intro identity member
  have derivation :=
    SemigroupBasis.Generated.S4_64.representative_basis.2
      identity (right_models identity member)
  exact derivation.sound s5_719_models_s4_64_basis

theorem basis_s5_728_models :
    Models s5_728.semigroup basis := by
  intro identity member
  have derivation :=
    SemigroupBasis.Generated.S4_64.representative_basis.2
      identity (right_models identity member)
  exact derivation.sound s5_728_models_s4_64_basis

theorem basis_s5_891_models :
    Models s5_891.semigroup basis := by
  intro identity member
  have derivation :=
    SemigroupBasis.Generated.S4_64.representative_basis.2
      identity (right_models identity member)
  exact derivation.sound s5_891_models_s4_64_basis

private theorem s5_719_valid_to_s4_64
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_719.semigroup) :
    identity.SatisfiedBy FactorTables.s4_64.semigroup := by
  have derivation :=
    SemigroupBasis.Generated.S4_64Transfers.S5_719.transferred_basis.2
      identity valid
  have sourceDerivation :
      Derives edmundsFourSixtyFourBasis identity.lhs identity.rhs := by
    simpa only
        [SemigroupBasis.Generated.S4_64Transfers.S5_719.transferBasis_eq_source]
      using derivation
  exact sourceDerivation.sound
    SemigroupBasis.Generated.S4_64.representative_basis.1

private theorem s5_728_valid_to_s4_64
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_728.semigroup) :
    identity.SatisfiedBy FactorTables.s4_64.semigroup := by
  have derivation :=
    SemigroupBasis.Generated.S4_64Transfers.S5_728.transferred_basis.2
      identity valid
  have sourceDerivation :
      Derives edmundsFourSixtyFourBasis identity.lhs identity.rhs := by
    simpa only
        [SemigroupBasis.Generated.S4_64Transfers.S5_728.transferBasis_eq_source]
      using derivation
  exact sourceDerivation.sound
    SemigroupBasis.Generated.S4_64.representative_basis.1

private theorem s5_891_valid_to_s4_64
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_891.semigroup) :
    identity.SatisfiedBy FactorTables.s4_64.semigroup := by
  have derivation :=
    SemigroupBasis.Generated.S4_64Transfers.S5_891.transferred_basis.2
      identity valid
  have sourceDerivation :
      Derives edmundsFourSixtyFourBasis identity.lhs identity.rhs := by
    simpa only
        [SemigroupBasis.Generated.S4_64Transfers.S5_891.transferBasis_eq_source]
      using derivation
  exact sourceDerivation.sound
    SemigroupBasis.Generated.S4_64.representative_basis.1

/-! ## Four authenticated alternate intersections -/

/-- Explicit selected-pair name used by the per-class endpoint generator for
`S6_12185`, `S6_12462`, and `S6_12492`. -/
def intersectionBasisS4_116opS4_64 :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      FactorTables.s4_64.semigroup
      basis :=
  intersectionBasis

theorem derivesOfFactorValidS4_116opS5_719
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (rightValid : identity.SatisfiedBy s5_719.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity leftValid
    (s5_719_valid_to_s4_64 identity rightValid)

def intersectionBasisS4_116opS5_719 :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      s5_719.semigroup
      basis where
  leftModels := left_models
  rightModels := basis_s5_719_models
  complete := derivesOfFactorValidS4_116opS5_719

theorem derivesOfFactorValidS4_116opS5_728
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy FactorTables.s4_116op.semigroup)
    (rightValid : identity.SatisfiedBy s5_728.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity leftValid
    (s5_728_valid_to_s4_64 identity rightValid)

def intersectionBasisS4_116opS5_728 :
    IntersectionBasis
      FactorTables.s4_116op.semigroup
      s5_728.semigroup
      basis where
  leftModels := left_models
  rightModels := basis_s5_728_models
  complete := derivesOfFactorValidS4_116opS5_728

theorem derivesOfFactorValidS3_16opS4_64
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_16op.semigroup)
    (rightValid :
      identity.SatisfiedBy FactorTables.s4_64.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity
    (s3_16op_valid_to_s4_116op identity leftValid) rightValid

def intersectionBasisS3_16opS4_64 :
    IntersectionBasis
      s3_16op.semigroup
      FactorTables.s4_64.semigroup
      basis where
  leftModels := basis_s3_16op_models
  rightModels := right_models
  complete := derivesOfFactorValidS3_16opS4_64

theorem derivesOfFactorValidS3_16opS5_891
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy s3_16op.semigroup)
    (rightValid : identity.SatisfiedBy s5_891.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity
    (s3_16op_valid_to_s4_116op identity leftValid)
    (s5_891_valid_to_s4_64 identity rightValid)

/-- Shared exact alternate intersection used independently by both
`S6_14222` and `S6_14223`. -/
def intersectionBasisS3_16opS5_891 :
    IntersectionBasis
      s3_16op.semigroup
      s5_891.semigroup
      basis where
  leftModels := basis_s3_16op_models
  rightModels := basis_s5_891_models
  complete := derivesOfFactorValidS3_16opS5_891

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
