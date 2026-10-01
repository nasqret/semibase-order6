import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierValidity
import SemigroupBasis.CoRoots.Order6Sunday.IntersectionFinite

/-! Four-class unrestricted completion of the exact Parity808 three-law basis.
The finite parent is reused unchanged: two subdirect roots, two power-embedding
leaves, and their actual Models proofs. No finite screen is a proof premise. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808FamilyCompleteness

open SemigroupBasis
open Msg0524Parity808Gather (basis)
open Msg0524Parity808LastNecessary (rightFactor)
open Msg0534Parity808BarrierValidity (actual_factors_complete)

theorem basis_eq : basis = IntersectionFinite.SigmaParity808.basis := rfl

theorem intersection : IntersectionBasis Msg0524Parity808FactorEval.factor rightFactor basis where
  leftModels := IntersectionFinite.SigmaParity808.leftModels
  rightModels := IntersectionFinite.SigmaParity808.rightModels
  complete := actual_factors_complete

namespace S6_8866
theorem representative_basis : BasisFor IntersectionFinite.SigmaParity808.S6_8866.table.semigroup basis :=
  intersection.basisFor IntersectionFinite.SigmaParity808.S6_8866.pair
theorem opposite_basis : BasisFor IntersectionFinite.SigmaParity808.S6_8866.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_8866

namespace S6_8877
theorem representative_basis : BasisFor IntersectionFinite.SigmaParity808.S6_8877.table.semigroup basis :=
  S6_8866.representative_basis.inheritAlongPowerEmbedding
    IntersectionFinite.SigmaParity808.S6_8877.rootIntoPower IntersectionFinite.SigmaParity808.S6_8877.models
theorem opposite_basis : BasisFor IntersectionFinite.SigmaParity808.S6_8877.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_8877

namespace S6_9010
theorem representative_basis : BasisFor IntersectionFinite.SigmaParity808.S6_9010.table.semigroup basis :=
  intersection.basisFor IntersectionFinite.SigmaParity808.S6_9010.pair
theorem opposite_basis : BasisFor IntersectionFinite.SigmaParity808.S6_9010.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_9010

namespace S6_9020
theorem representative_basis : BasisFor IntersectionFinite.SigmaParity808.S6_9020.table.semigroup basis :=
  S6_9010.representative_basis.inheritAlongPowerEmbedding
    IntersectionFinite.SigmaParity808.S6_9020.rootIntoPower IntersectionFinite.SigmaParity808.S6_9020.models
theorem opposite_basis : BasisFor IntersectionFinite.SigmaParity808.S6_9020.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_9020

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808FamilyCompleteness
