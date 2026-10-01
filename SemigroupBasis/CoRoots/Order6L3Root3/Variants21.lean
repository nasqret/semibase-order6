import SemigroupBasis.CoRoots.Order6L3Root3.Bridge21
import SemigroupBasis.Generated.S4_23

/-!
# Equationally equivalent `S4_21`-family factor variant

`S4_23` has the same complete Edmunds basis as `S4_21`.  This module
transfers the intersection theorem without duplicating the derivation bridge.
-/

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis

private def toFinThree23 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis21_s4_23_models :
    Models SemigroupBasis.Generated.S4_23.table.semigroup basis21 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_23.table
    basis21 toFinThree23 (by decide)

theorem derivesOfFactorValid23
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_23.table.semigroup) :
    Derives basis21 identity.lhs identity.rhs := by
  have factorDerivation :=
    SemigroupBasis.Generated.S4_23.representative_basis.2
      identity s4Valid
  have transferred :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_21.table.semigroup := by
    intro valuation
    exact factorDerivation.sound
      SemigroupBasis.Generated.S4_21.representative_basis.1
      valuation
  exact derivesOfFactorValid21 identity s3Valid transferred

def intersectionBasis23 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_23.table.semigroup
      basis21 where
  leftModels := basis21_s3_4_models
  rightModels := basis21_s4_23_models
  complete := derivesOfFactorValid23

end SemigroupBasis.CoRoots.Order6L3Root3
