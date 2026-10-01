import SemigroupBasis.CoRoots.S6_8874LeeLiCondition6
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_8874

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.CoRoots.S6_8874.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortGeneralRightLaw

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortFinalGapRightLaw

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.powerLaw

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sandwichContractionLaw

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.squareTransportLaw

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.gatherGeneralLaw

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortGeneralLeftLaw

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortFinalGapLeftLaw

def sourceLaw8 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortInitialGapRightLaw

def sourceLaw9 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortInitialGapLeftLaw

def sourceLaw10 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortBothEmptyRightLaw

def sourceLaw11 : Identity Nat :=
  SemigroupBasis.CoRoots.S6_8874.sortBothEmptyLeftLaw

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7, sourceLaw8, sourceLaw9, sourceLaw10, sourceLaw11]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.S6_8874.basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.S6_8874.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_8874

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_8874.basis_complete
