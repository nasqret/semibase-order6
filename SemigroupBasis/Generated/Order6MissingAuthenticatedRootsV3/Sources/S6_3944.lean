import SemigroupBasis.CoRoots.S6_3944
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.CoRoots.S6_3944.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev law2 : Identity Nat := sourceLaw2
abbrev law3 : Identity Nat := sourceLaw3
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.S6_3944.basis) := by
  rfl

theorem representative_basis :
    BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.S6_3944.representative_basis

theorem basis_complete :
    BasisFor sourceSemigroup sourceBasis :=
  representative_basis

theorem opposite_basis :
    BasisFor sourceSemigroup.opposite (reversedBasis sourceBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944
