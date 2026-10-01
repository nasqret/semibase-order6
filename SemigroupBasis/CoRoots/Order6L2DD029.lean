import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Normalization
import SemigroupBasis.Generated.CommutativePositiveModThreeTransfersLayer1
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers

/-!
# Stable d029 mod-three/component completeness surface

The implementation module proves the literal B16 basis complete for the
direct factor intersection `S4_124 × S4_70`.  This thin delivery facade
reexports the exact semantic and derivational gates, then transports only the
left factor from `S4_124` to `S4_125` through their common complete
commutative positive-mod-three basis.

No bounded-search certificate, embedding-only retarget, or metadata transfer
is used here.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029

open SemigroupBasis

abbrev B16 : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.B16

abbrev B16ListDerives :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.B16ListDerives

abbrev SameModThreeComponentSignature :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.SameModThreeComponentSignature

/-- Every literal B16 law is valid in the direct `S4_124` factor. -/
theorem s4_124_models :
    Models SemigroupBasis.Generated.S4_124.table.semigroup B16 :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.s4_124_models

/-- Every literal B16 law is valid in the direct `S4_70` factor. -/
theorem s4_70_models :
    Models SemigroupBasis.Generated.S4_70.table.semigroup B16 :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.s4_70_models

/-- The selected direct-product factor semantics are exactly the d029
mod-three/component signature. -/
theorem factorValidity_iff_sameModThreeComponentSignature
    (identity : Identity Nat) :
    (identity.SatisfiedBy
          SemigroupBasis.Generated.S4_124.table.semigroup ∧
      identity.SatisfiedBy
          SemigroupBasis.Generated.S4_70.table.semigroup) ↔
      SameModThreeComponentSignature identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.factorValidity_iff_sameModThreeComponentSignature
    identity

/-- Equality of the exact d029 signature is sufficient for a literal B16
derivation. -/
theorem derivesOfSameModThreeComponentSignature
    {left right : Word Nat}
    (same : SameModThreeComponentSignature left right) :
    Derives B16 left right :=
  SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.derivesOfSameModThreeComponentSignature
    same

/-- Stable direct `S4_124 × S4_70` intersection root for d029. -/
def intersectionBasisS4_124S4_70 :
    IntersectionBasis
      SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup
      B16 where
  leftModels := s4_124_models
  rightModels := s4_70_models
  complete := by
    intro identity leftValid rightValid
    exact derivesOfSameModThreeComponentSignature
      (SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16.sameModThreeComponentSignature_of_factorValidity
        identity leftValid rightValid)

/-- `S4_124` and `S4_125` have the same unrestricted identity theory because
both have the exact complete `commutativePositiveModThreeBasis`. -/
theorem sameTheoryS4_124S4_125 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.Generated.S4_124.representative_basis
    SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis

/-- The sibling d029 intersection after the exact common-basis transfer on
the left factor. -/
def intersectionBasisS4_125S4_70 :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup
      B16 :=
  intersectionBasisS4_124S4_70.transferTheories
    sameTheoryS4_124S4_125 (fun _ => Iff.rfl)

end SemigroupBasis.CoRoots.Order6L2DD029
