import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773.Shards

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773

open SemigroupBasis

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.sourceSemigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis_complete.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 44) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_12773`. -/
theorem representative_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis_complete
  simpa only [oppositeTable_semigroup] using transferred


theorem opposite_basis :
    BasisFor table.semigroup (reversedBasis SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12773
