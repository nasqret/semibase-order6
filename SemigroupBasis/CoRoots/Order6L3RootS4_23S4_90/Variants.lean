import SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90.Bridge
import SemigroupBasis.Generated.S4_21
import SemigroupBasis.Generated.S4_90TransfersLayer1

/-!
# Rank-13 factor variants

The four authenticated order-six representatives use three concrete factor
pairs.  `S4_21` and `S4_23` have the same complete Edmunds basis, while
`S4_93` and `S4_90` have the same complete suffix-parity basis.  This file
transports the kernel proof for `S4_23 / S4_90` to the two additional pairs.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90

open SemigroupBasis

private def variantToFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

set_option maxRecDepth 100000 in
theorem basis_s4_21_models :
    Models SemigroupBasis.Generated.S4_21.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_21.table basis variantToFinFour (by decide)

set_option maxRecDepth 100000 in
theorem basis_s4_93_models :
    Models
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S4_93.table
    basis variantToFinFour (by decide)

private theorem s4_21_valid_to_s4_23
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_21.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S4_23.table.semigroup := by
  have derivation :=
    SemigroupBasis.Generated.S4_21.representative_basis.2 identity valid
  exact derivation.sound
    SemigroupBasis.Generated.S4_23.representative_basis.1

private theorem s4_93_valid_to_s4_90
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S4_90.table.semigroup := by
  have derivation :=
    SemigroupBasis.Generated.S4_90Transfers.S4_93.representative_basis.2
      identity valid
  exact derivation.sound
    SemigroupBasis.Generated.S4_90.representative_basis.1

theorem derivesOfFactorValidS4_21S4_93
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_21.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity
    (s4_21_valid_to_s4_23 identity leftValid)
    (s4_93_valid_to_s4_90 identity rightValid)

def intersectionBasisS4_21S4_93 :
    IntersectionBasis
      SemigroupBasis.Generated.S4_21.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      basis where
  leftModels := basis_s4_21_models
  rightModels := basis_s4_93_models
  complete := derivesOfFactorValidS4_21S4_93

theorem derivesOfFactorValidS4_23S4_93
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_23.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity leftValid
    (s4_93_valid_to_s4_90 identity rightValid)

def intersectionBasisS4_23S4_93 :
    IntersectionBasis
      SemigroupBasis.Generated.S4_23.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      basis where
  leftModels := basis_s4_23_models
  rightModels := basis_s4_93_models
  complete := derivesOfFactorValidS4_23S4_93

end SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90
