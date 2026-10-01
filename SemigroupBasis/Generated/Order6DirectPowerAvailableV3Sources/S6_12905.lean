import Order6FinalL5TransferV3.Part296
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_12905

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw3

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw4

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw5

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw6

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw7

def sourceLaw8 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw8

def sourceLaw9 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw9

def sourceLaw10 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw10

def sourceLaw11 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw11

def sourceLaw12 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw12

def sourceLaw13 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw13

def sourceLaw14 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw14

def sourceLaw15 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw15

def sourceLaw16 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw16

def sourceLaw17 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw17

def sourceLaw18 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw18

def sourceLaw19 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw19

def sourceLaw20 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw20

def sourceLaw21 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw21

def sourceLaw22 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw22

def sourceLaw23 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetLaw23

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11, sourceLaw12, sourceLaw13, sourceLaw14, sourceLaw15, sourceLaw16, sourceLaw17, sourceLaw18, sourceLaw19, sourceLaw20, sourceLaw21, sourceLaw22, sourceLaw23]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_12905.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_12905

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_12905.basis_complete
