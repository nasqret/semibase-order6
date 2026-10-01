import Order6FinalL5TransferV3.Part092
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4117

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.targetLaw3

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4117.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4117

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_4117.basis_complete
