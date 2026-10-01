import SemigroupBasis.CoRoots.Order6ContentFirstTailRoots
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6155

open SemigroupBasis

abbrev sourceSemigroup := (SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.S6_6155.table.semigroup).opposite

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨1, [1, 0]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 0]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4]

theorem sourceBasis_eq_upstream :
    sourceBasis = (reversedBasis (SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.basis)) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.Order6ContentFirstTailRoots.S6_6155.direct_basis.oppositeReversed

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6155

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_6155.basis_complete
