import SemigroupBasis.CoRoots.Order6Day15.B16.B16M5Bridge
import SemigroupBasis.CoRoots.Order6Day15.B16.B16NormalizerObservation
import SemigroupBasis.CoRoots.Order6Day15.B16.B16SemanticSufficiency
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Complete

open Literal Necessity Reach
open SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

/-- Unrestricted semantic characterization of the literal S6_6432 table. -/
theorem valid_iff_observation6432 (e : Identity Nat) :
    e.SatisfiedBy s6432 ↔ SameObservation e.lhs e.rhs :=
  ⟨valid_observation6432 e,identity_of_observation6432 e⟩

/-- Unrestricted semantic characterization of the literal S6_6439 table. -/
theorem valid_iff_observation6439 (e : Identity Nat) :
    e.SatisfiedBy s6439 ↔ SameObservation e.lhs e.rhs :=
  ⟨valid_observation6439 e,identity_of_observation6439 e⟩

/-- The exact repaired sixteen-law basis, with no supplied reach hypothesis. -/
theorem basisFor6432 : BasisFor s6432 basis :=
  ⟨S6_6432.tableModels,fun e h => sameObservation_derives (valid_observation6432 e h)⟩

theorem basisFor6439 : BasisFor s6439 basis :=
  ⟨S6_6439.tableModels,fun e h => sameObservation_derives (valid_observation6439 e h)⟩

/-- Literal opposite orientation with the literal reversed sixteen-law basis. -/
theorem basisFor6432_opposite : BasisFor s6432.opposite (reversedBasis basis) :=
  basisFor6432.oppositeReversed

theorem basisFor6439_opposite : BasisFor s6439.opposite (reversedBasis basis) :=
  basisFor6439.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day15.B16.Complete
