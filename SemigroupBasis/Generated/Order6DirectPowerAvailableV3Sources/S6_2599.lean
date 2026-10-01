import Order6FinalL5TransferV3.Part045
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2599

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw3

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw4

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw5

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw6

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetLaw7

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_2599.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2599

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2599.basis_complete
