import SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2604

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.table.semigroup

def sourceLaw0 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

def sourceLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [0, 1]⟩⟩

def sourceLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw3 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0]⟩⟩

def sourceLaw4 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩

def sourceLaw5 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩

def sourceLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def sourceLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩

def sourceLaw8 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [1, 1, 1]⟩⟩

def sourceLaw9 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def sourceLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20.basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.representative_basis

end SemigroupBasis.Generated.Order6FactorPairResidualV3Sources.S6_2604
