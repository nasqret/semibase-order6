import SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_10399
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_10399

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_10399.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨1, [0]⟩, ⟨1, [1, 1, 0]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def sourceLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def sourceLaw6 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [1, 2, 1, 0]⟩⟩

def sourceLaw7 : Identity Nat :=
  ⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def sourceLaw8 : Identity Nat :=
  ⟨⟨1, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def sourceLaw9 : Identity Nat :=
  ⟨⟨1, [0, 2, 1, 0]⟩, ⟨0, [1, 2, 1, 0]⟩⟩

def sourceLaw10 : Identity Nat :=
  ⟨⟨2, [0, 2, 1, 0]⟩, ⟨0, [2, 2, 1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev law2 : Identity Nat := sourceLaw2
abbrev law3 : Identity Nat := sourceLaw3
abbrev law4 : Identity Nat := sourceLaw4
abbrev law5 : Identity Nat := sourceLaw5
abbrev law6 : Identity Nat := sourceLaw6
abbrev law7 : Identity Nat := sourceLaw7
abbrev law8 : Identity Nat := sourceLaw8
abbrev law9 : Identity Nat := sourceLaw9
abbrev law10 : Identity Nat := sourceLaw10
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis) := by
  rfl

theorem representative_basis :
    BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_10399.representative_basis

theorem basis_complete :
    BasisFor sourceSemigroup sourceBasis :=
  representative_basis

theorem opposite_basis :
    BasisFor sourceSemigroup.opposite (reversedBasis sourceBasis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_10399
