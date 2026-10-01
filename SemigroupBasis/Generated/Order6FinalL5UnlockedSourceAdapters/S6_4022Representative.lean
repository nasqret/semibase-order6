import Order6FinalL5TransferV3.Part088

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4022.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 0, 1]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def sourceLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def sourceLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def sourceLaw7 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [0, 1, 0, 1]⟩⟩

def sourceLaw8 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [0, 1, 1, 0]⟩⟩

def sourceLaw9 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [1, 0, 0, 1]⟩⟩

def sourceLaw10 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [1, 0, 1, 0]⟩⟩

def sourceLaw11 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [1, 1, 0, 0]⟩⟩

def sourceLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 1, 0, 2]⟩⟩

def sourceLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 0, 2]⟩⟩

def sourceLaw14 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def sourceLaw15 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 1]⟩⟩

def sourceLaw16 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def sourceLaw17 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def sourceLaw18 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def sourceLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def sourceLaw20 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def sourceLaw21 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [1, 1, 2, 1]⟩⟩

def sourceLaw22 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11, sourceLaw12, sourceLaw13, sourceLaw14, sourceLaw15, sourceLaw16, sourceLaw17, sourceLaw18, sourceLaw19, sourceLaw20, sourceLaw21, sourceLaw22]

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
abbrev law11 : Identity Nat := sourceLaw11
abbrev law12 : Identity Nat := sourceLaw12
abbrev law13 : Identity Nat := sourceLaw13
abbrev law14 : Identity Nat := sourceLaw14
abbrev law15 : Identity Nat := sourceLaw15
abbrev law16 : Identity Nat := sourceLaw16
abbrev law17 : Identity Nat := sourceLaw17
abbrev law18 : Identity Nat := sourceLaw18
abbrev law19 : Identity Nat := sourceLaw19
abbrev law20 : Identity Nat := sourceLaw20
abbrev law21 : Identity Nat := sourceLaw21
abbrev law22 : Identity Nat := sourceLaw22
abbrev basis : List (Identity Nat) := sourceBasis

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4022.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_4022.representative_basis

end SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative
