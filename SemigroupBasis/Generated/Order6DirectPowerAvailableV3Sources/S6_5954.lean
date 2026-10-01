import Order6FinalL5TransferV3.Part138
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw3

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw4

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw5

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw6

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw7

def sourceLaw8 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw8

def sourceLaw9 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw9

def sourceLaw10 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw10

def sourceLaw11 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw11

def sourceLaw12 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw12

def sourceLaw13 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw13

def sourceLaw14 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw14

def sourceLaw15 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw15

def sourceLaw16 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw16

def sourceLaw17 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw17

def sourceLaw18 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw18

def sourceLaw19 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw19

def sourceLaw20 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw20

def sourceLaw21 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw21

def sourceLaw22 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetLaw22

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11, sourceLaw12, sourceLaw13, sourceLaw14, sourceLaw15, sourceLaw16, sourceLaw17, sourceLaw18, sourceLaw19, sourceLaw20, sourceLaw21, sourceLaw22]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_5954.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_5954.basis_complete
