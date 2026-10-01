import SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3304

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6DivisorTransfers.S6_3304.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Examples.edmundsFiveTwoFourBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal.S6_3304.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3304

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3304.basis_complete
