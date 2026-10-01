import SemigroupBasis.CoRoots.Order6L3Root3.Bridge60
import SemigroupBasis.Generated.S4_62
import SemigroupBasis.Generated.S4_60TransfersLayer1

/-!
# Equationally equivalent `S4_60`-family factor variants

`S4_62` and `S5_585` have the same complete four-law Edmunds basis as
`S4_60`.  Their intersection theorems reuse the single protected
derivation bridge.
-/

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis

private def toFinThree60Variants : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis60_s4_62_models :
    Models SemigroupBasis.Generated.S4_62.table.semigroup basis60 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_62.table
    basis60 toFinThree60Variants (by decide)

theorem derivesOfFactorValid62
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_62.table.semigroup) :
    Derives basis60 identity.lhs identity.rhs := by
  have factorDerivation :=
    SemigroupBasis.Generated.S4_62.representative_basis.2
      identity s4Valid
  have transferred :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup := by
    intro valuation
    exact factorDerivation.sound
      SemigroupBasis.Generated.S4_60.representative_basis.1
      valuation
  exact derivesOfFactorValid60 identity s3Valid transferred

def intersectionBasis62 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_62.table.semigroup
      basis60 where
  leftModels := basis60_s3_4_models
  rightModels := basis60_s4_62_models
  complete := derivesOfFactorValid62

theorem basis60_s5_585_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup
      basis60 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_585.table
    basis60 toFinThree60Variants (by decide)

theorem derivesOfFactorValid585
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup) :
    Derives basis60 identity.lhs identity.rhs := by
  have factorDerivation :
      Derives
        SemigroupBasis.Examples.edmundsFourSixtyBasis
        identity.lhs identity.rhs := by
    have transferred :=
      SemigroupBasis.Generated.S4_60Transfers.S5_585.transferred_basis.2
        identity s5Valid
    simpa only [
      SemigroupBasis.Generated.S4_60Transfers.S5_585.transferBasis_eq_source
    ] using transferred
  have factorValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup := by
    intro valuation
    exact factorDerivation.sound
      SemigroupBasis.Generated.S4_60.representative_basis.1
      valuation
  exact derivesOfFactorValid60 identity s3Valid factorValid

def intersectionBasis585 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup
      basis60 where
  leftModels := basis60_s3_4_models
  rightModels := basis60_s5_585_models
  complete := derivesOfFactorValid585

end SemigroupBasis.CoRoots.Order6L3Root3
