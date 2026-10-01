import SemigroupBasis.CoRoots.Order6L3RootS3_18.BridgeS4_9
import SemigroupBasis.Generated.S4_35

/-!
# Equationally equivalent `S4_9`-family factor variant

`S4_35` has the same complete three-nilpotent basis as `S4_9`.  This module
transfers the rank-9 intersection theorem without duplicating the guarded
derivation bridge.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis

private def toFinFour35 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basisS4_9_s4_35_models :
    Models SemigroupBasis.Generated.S4_35.table.semigroup basisS4_9 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_35.table
    basisS4_9 toFinFour35 (by decide)

theorem derivesOfFactorValidS4_35
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_18.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_35.table.semigroup) :
    Derives basisS4_9 identity.lhs identity.rhs := by
  have factorDerivation :=
    SemigroupBasis.Generated.S4_35.representative_basis.2
      identity s4Valid
  have transferred :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_9.table.semigroup := by
    intro valuation
    exact factorDerivation.sound
      SemigroupBasis.Generated.S4_9.representative_basis.1
      valuation
  exact derivesOfFactorValidS4_9 identity s3Valid transferred

def intersectionBasisS4_35 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_18.table.semigroup
      SemigroupBasis.Generated.S4_35.table.semigroup
      basisS4_9 where
  leftModels := basisS4_9_s3_18_models
  rightModels := basisS4_9_s4_35_models
  complete := derivesOfFactorValidS4_35

end SemigroupBasis.CoRoots.Order6L3RootS3_18
