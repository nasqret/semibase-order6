import SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_11390
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_11390.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6211Opposite.sourceBasis) := by
  rfl

theorem representative_basis :
    BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_11390.representative_basis

theorem basis_complete :
    BasisFor sourceSemigroup sourceBasis :=
  representative_basis

theorem opposite_basis :
    BasisFor sourceSemigroup.opposite (reversedBasis sourceBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390
