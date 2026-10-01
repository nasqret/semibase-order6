import SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_14916

open SemigroupBasis

abbrev sourceSemigroup := SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.S6_14916.sourceTable.semigroup

def sourceLaw0 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.powerLaw

def sourceLaw1 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap44Law

def sourceLaw2 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap33Law

def sourceLaw3 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap34Law

def sourceLaw4 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap22Law

def sourceLaw5 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap23Law

def sourceLaw6 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.swap24Law

def sourceLaw7 : Identity Nat :=
  SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.class471GatherLaw

def sourceBasis : List (Identity Nat) :=
  [sourceLaw0, sourceLaw1, sourceLaw2, sourceLaw3, sourceLaw4, sourceLaw5, sourceLaw6, sourceLaw7]

theorem sourceBasis_eq_upstream :
    sourceBasis = (SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.class471Basis) := by
  rfl

theorem basis_complete : BasisFor sourceSemigroup sourceBasis := by
  rw [sourceBasis_eq_upstream]
  exact SemigroupBasis.CoRoots.Order6PeriodThreeTraceRoots.S6_14916.source_basis

end SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_14916

#print axioms SemigroupBasis.Generated.Order6DirectPowerAvailableV3Sources.S6_14916.basis_complete
