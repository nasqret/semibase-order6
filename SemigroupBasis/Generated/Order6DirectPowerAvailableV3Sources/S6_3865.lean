import Order6FinalL5TransferV3.Part084
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3865

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw3

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw4

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw5

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw6

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw7

def sourceLaw8 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw8

def sourceLaw9 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw9

def sourceLaw10 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw10

def sourceLaw11 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw11

def sourceLaw12 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw12

def sourceLaw13 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw13

def sourceLaw14 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw14

def sourceLaw15 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetLaw15

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11, sourceLaw12, sourceLaw13, sourceLaw14, sourceLaw15]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_3865.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3865

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_3865.basis_complete
