import Order6FinalL5TransferV3.Part340
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15091

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15091.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15091.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15091.targetLaw1

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15091.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_15091.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15091

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_15091.basis_complete
