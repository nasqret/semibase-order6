import SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3200

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6ExtensionTransfersV2.S6_3200.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6ExtensionTransfersV2.S6_3200.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6DirectPowerSourceEndpoints.Preseal.S6_3200.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3200

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3200.basis_complete
