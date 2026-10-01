import SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7382

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6ExtensionTransfersV1.S6_7382.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6ExtensionTransfersV1.S6_7382.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal.S6_7382.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7382

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_7382.basis_complete
