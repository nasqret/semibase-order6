import Order6FinalL5TransferV3.Part029
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1276

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw0

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw1

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw2

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw3

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw4

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw5

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw6

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw7

def sourceLaw8 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw8

def sourceLaw9 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw9

def sourceLaw10 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw10

def sourceLaw11 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw11

def sourceLaw12 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw12

def sourceLaw13 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw13

def sourceLaw14 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw14

def sourceLaw15 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw15

def sourceLaw16 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw16

def sourceLaw17 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw17

def sourceLaw18 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw18

def sourceLaw19 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw19

def sourceLaw20 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw20

def sourceLaw21 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw21

def sourceLaw22 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw22

def sourceLaw23 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw23

def sourceLaw24 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw24

def sourceLaw25 : Identity Nat :=
  SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetLaw25

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11, sourceLaw12, sourceLaw13, sourceLaw14, sourceLaw15, sourceLaw16, sourceLaw17, sourceLaw18, sourceLaw19, sourceLaw20, sourceLaw21, sourceLaw22, sourceLaw23, sourceLaw24, sourceLaw25]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.targetBasis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.Generated.Order6FinalL5TransferV3.S6_1276.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1276

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_1276.basis_complete
