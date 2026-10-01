import SemigroupBasis.CoRoots.Order6ContentFirstTailRoots
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6173

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.S6_6173.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.S6_6173.direct_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6173

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6173.basis_complete
