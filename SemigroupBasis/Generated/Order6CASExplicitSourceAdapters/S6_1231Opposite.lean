import Order6FinalL5TransferV3.Part028
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_1231Opposite

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1231.table.semigroup.opposite
abbrev oppositeTable := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1231.table

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨2, [0, 1]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev law2 : Identity Nat := sourceLaw2
abbrev law3 : Identity Nat := sourceLaw3
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (reversedBasis SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1231.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1231.opposite_basis

end SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_1231Opposite
