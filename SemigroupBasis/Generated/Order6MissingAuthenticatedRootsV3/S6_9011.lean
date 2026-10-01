import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011.Shards

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011

open SemigroupBasis

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 17) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_9011`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_9011
