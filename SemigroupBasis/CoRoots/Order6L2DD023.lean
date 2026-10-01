import SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3
import SemigroupBasis.Generated.S5_443TransfersLayer1
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers

/-!
# The transferred d023 guarded period-two intersection

The guarded B3 root is proved for `S2_4 × S5_614ᵒᵖ`.  The opposite
semigroups `S5_614ᵒᵖ` and `S5_635ᵒᵖ` have the same unrestricted
identity theory because both have the exact common complete basis
`reversedBasis S5_443Family.basis`.  This module transports only that right
factor theory; it does not use the bounded d023 oracle partition.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD023

open SemigroupBasis

private theorem leftTheoryRefl (identity : Identity Nat) :
    identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup ↔
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup :=
  Iff.rfl

/-- The two opposite right factors have the same unrestricted identity theory
because they share the exact complete reversed `S5_443Family` basis. -/
theorem s5_614op_sameTheory_s5_635op :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.opposite
      Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.CoRoots.S5_443Family.S5_614.opposite_basis_complete
    SemigroupBasis.Generated.S5_443Transfers.S5_635.opposite_basis

/-- The d023 B3 intersection after replacing `S5_614ᵒᵖ` by the
identity-theory-equivalent factor `S5_635ᵒᵖ`. -/
def intersectionBasisS2_4S5_635op :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3.B3 :=
  SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3.intersectionBasisS2_4S5_614op.transferTheories
    leftTheoryRefl s5_614op_sameTheory_s5_635op

end SemigroupBasis.CoRoots.Order6L2DD023
