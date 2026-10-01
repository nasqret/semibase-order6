import Order6FinalL5TransferV3.Part353
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15857

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15857.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15857.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15857.targetLaw1

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15857.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15857.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15857

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15857.basis_complete
