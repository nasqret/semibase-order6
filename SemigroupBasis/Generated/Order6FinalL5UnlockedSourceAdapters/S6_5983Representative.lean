import Order6FinalL5TransferV3.Part138

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5983.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1]

abbrev law0 : Identity Nat := sourceLaw0
abbrev law1 : Identity Nat := sourceLaw1
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5983.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5983.representative_basis

end SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_5983Representative
