import SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoinTargets
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2612

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.S6_2612.table.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.unaryPowerLaw

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.contextualPowerLaw

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.repeatedMiddleLaw

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.repeatedPrefixLaw

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.prefixCommutationLaw

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.suffixCommutationLaw

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.S6_2612.representative_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2612

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_2612.basis_complete
