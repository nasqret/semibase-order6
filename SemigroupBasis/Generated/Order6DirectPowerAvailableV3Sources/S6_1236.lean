import SemigroupBasis.Generated.Order6FactorIntersection.PositiveParityBulkShort.S6_1236
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1236

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FactorIntersection.PositiveParityBulkShort.S6_1236.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1, 1, 1]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw5 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨1, [0, 0]⟩⟩

def sourceLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def sourceLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityBulkShort.basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FactorIntersection.PositiveParityBulkShort.S6_1236.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1236

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1236.basis_complete
