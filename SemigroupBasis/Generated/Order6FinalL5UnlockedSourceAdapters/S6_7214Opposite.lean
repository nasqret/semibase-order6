import Order6FinalL5TransferV3.Part164

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite

open SemigroupBasis

abbrev sourceSemigroup := (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_7214.table.semigroup).opposite

def sourceLaw0 : Identity Nat :=
  ⟨⟨1, [0]⟩, ⟨1, [0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨2, [0, 1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (reversedBasis (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_7214.targetBasis)) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_7214.representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
