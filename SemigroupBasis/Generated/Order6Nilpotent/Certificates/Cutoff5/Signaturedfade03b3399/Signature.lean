/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399
import SemigroupBasis.FiniteNilpotentLongCollapse
import SemigroupBasis.FiniteNilpotentDecisionDAG
import SemigroupBasis.FiniteNilpotentCounterexample

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399

open SemigroupBasis

abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeCommon

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem basis_eq :
    basis =
      [
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩,
        ⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 0, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 1, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 2, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 2, 0]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 0, 1]⟩⟩
      ] ++
      [
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 1, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 2, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 0, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 0, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 2, 2]⟩⟩,
        ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨1, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨1, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨1, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨1, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨1, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 1, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [0, 2, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [2, 2, 0]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [2, 0, 1]⟩⟩
      ] ++
      [
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [1, 2, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [0, 0, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [1, 1, 2]⟩⟩,
        ⟨⟨2, [0, 1, 0]⟩, ⟨0, [2, 1, 2]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨1, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [2, 2, 0]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨2, [1, 1, 0]⟩, ⟨0, [1, 1, 2]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨2, [0, 1]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨0, [2, 1]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨0, [1, 2]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩
      ] ++
      [
        ⟨⟨0, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [2, 1, 0]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨1, [2, 1, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨2, [2, 1, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨2, [2, 1, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨2, [2, 1, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨2, [2, 1, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨2, [3, 1, 0]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨3, [1, 2, 0]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨1, [3, 2, 0]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨1, [2, 3, 0]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨3, [2, 0, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨2, [3, 0, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨3, [0, 2, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [3, 2, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨2, [0, 3, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [2, 3, 1]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨3, [0, 1, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [3, 1, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨1, [0, 3, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [1, 3, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [2, 1, 3]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨0, [1, 2, 3]⟩⟩,
        ⟨⟨4, [3, 2, 1, 0]⟩, ⟨9, [8, 7, 6, 5]⟩⟩
      ] := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem inventory_eq :
    inventory =
      [
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩,
        ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 0]⟩⟩,
        ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 0]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩,
        ⟨⟨0, [0, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 0, 2]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 2, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 0, 1]⟩⟩
      ] ++
      [
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨2, [0, 1]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨2, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨1, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 0, 2]⟩, ⟨0, [2, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩,
        ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩,
        ⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨2, [0, 1, 3]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨2, [1, 0, 3]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 3, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 3, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 1, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨1, [3, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 0, 2]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 2, 1]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨2, [3, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 0, 1]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 2, 0]⟩⟩,
        ⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 1, 0]⟩⟩
      ] := by
  decide

theorem inventoryIdentity000RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity001RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity002RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity003RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity004RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity005RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity006RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity007RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity008RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity009RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity010RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity011RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity012RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity013RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity014RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity015RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity016RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity017RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity018RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity019RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity020RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity021RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity022RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity023RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity024RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity025RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity026RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity027RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity028RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity029RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity030RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity031RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity032RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity033RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity034RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity035RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity036RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity037RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity038RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity039RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity040RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity041RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity042RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity043RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity044RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity045RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity046RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity047RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity048RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity049RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity050RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity051RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity052RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity053RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity054RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity055RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity056RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity057RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity058RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity059RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity060RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity061RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity062RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity063RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity064RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity065RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity066RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity067RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity068RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity069RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity070RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity071RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity072RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity073RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity074RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity075RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity076RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity077RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity078RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity079RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity080RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity081RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity082RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity083RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity084RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity085RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity086RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity087RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity088RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity089RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity090RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity091RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity092RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity093RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity094RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity095RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity096RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity097RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity098RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity099RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity100RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity101RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity102RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity103RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity104RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity105RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity106RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity107RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity108RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity109RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity110RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity111RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity112RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity113RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))))⟩

theorem inventoryIdentity114RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity115RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity116RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity117RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity118RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity119RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity120RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity121RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity122RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity123RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity124RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity125RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity126RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity127RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity128RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity129RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity130RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity131RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity132RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity133RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity134RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity135RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity136RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity137RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity138RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨2, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨2, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity139RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity140RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity141RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity142RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity143RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity144RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity145RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity146RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity147RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity148RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity149RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity150RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity151RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity152RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity153RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity154RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity155RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity156RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity157RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity158RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity159RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity160RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity161RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity162RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity163RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity164RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity165RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0, 2]⟩, ⟨0, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity166RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity167RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity168RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity169RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))))⟩

theorem inventoryIdentity170RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity171RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity172RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity173RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity174RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 3, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 3, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity175RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 3, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 3, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity176RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity177RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity178RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨1, [3, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨1, [3, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity179RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity180RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity181RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity182RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity183RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity184RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryIdentity185RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))))⟩

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory := by
  rw [inventory_eq]
  exact
    FiniteNilpotentCounterexample.allRestrictedGrowth_append
      (  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity000RestrictedGrowth <|
        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity001RestrictedGrowth <|
          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity002RestrictedGrowth <|
            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity003RestrictedGrowth <|
              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity004RestrictedGrowth <|
                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity005RestrictedGrowth <|
                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity006RestrictedGrowth <|
                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity007RestrictedGrowth <|
                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity008RestrictedGrowth <|
                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity009RestrictedGrowth <|
                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity010RestrictedGrowth <|
                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity011RestrictedGrowth <|
                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity012RestrictedGrowth <|
                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity013RestrictedGrowth <|
                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity014RestrictedGrowth <|
                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity015RestrictedGrowth <|
                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity016RestrictedGrowth <|
                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity017RestrictedGrowth <|
                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity018RestrictedGrowth <|
                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity019RestrictedGrowth <|
                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity020RestrictedGrowth <|
                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity021RestrictedGrowth <|
                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity022RestrictedGrowth <|
                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity023RestrictedGrowth <|
                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity024RestrictedGrowth <|
                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity025RestrictedGrowth <|
                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity026RestrictedGrowth <|
                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity027RestrictedGrowth <|
                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity028RestrictedGrowth <|
                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity029RestrictedGrowth <|
                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity030RestrictedGrowth <|
                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity031RestrictedGrowth <|
                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity032RestrictedGrowth <|
                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity033RestrictedGrowth <|
                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity034RestrictedGrowth <|
                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity035RestrictedGrowth <|
                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity036RestrictedGrowth <|
                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity037RestrictedGrowth <|
                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity038RestrictedGrowth <|
                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity039RestrictedGrowth <|
                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity040RestrictedGrowth <|
                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity041RestrictedGrowth <|
                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity042RestrictedGrowth <|
                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity043RestrictedGrowth <|
                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity044RestrictedGrowth <|
                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity045RestrictedGrowth <|
                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity046RestrictedGrowth <|
                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity047RestrictedGrowth <|
                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity048RestrictedGrowth <|
                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity049RestrictedGrowth <|
                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity050RestrictedGrowth <|
                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity051RestrictedGrowth <|
                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity052RestrictedGrowth <|
                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity053RestrictedGrowth <|
                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity054RestrictedGrowth <|
                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity055RestrictedGrowth <|
                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity056RestrictedGrowth <|
                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity057RestrictedGrowth <|
                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity058RestrictedGrowth <|
                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity059RestrictedGrowth <|
                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity060RestrictedGrowth <|
                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity061RestrictedGrowth <|
                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity062RestrictedGrowth <|
                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity063RestrictedGrowth <|
                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity064RestrictedGrowth <|
                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity065RestrictedGrowth <|
                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity066RestrictedGrowth <|
                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity067RestrictedGrowth <|
                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity068RestrictedGrowth <|
                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity069RestrictedGrowth <|
                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity070RestrictedGrowth <|
                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity071RestrictedGrowth <|
                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity072RestrictedGrowth <|
                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity073RestrictedGrowth <|
                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity074RestrictedGrowth <|
                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity075RestrictedGrowth <|
                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity076RestrictedGrowth <|
                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity077RestrictedGrowth <|
                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity078RestrictedGrowth <|
                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity079RestrictedGrowth <|
                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity080RestrictedGrowth <|
                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity081RestrictedGrowth <|
                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity082RestrictedGrowth <|
                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity083RestrictedGrowth <|
                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity084RestrictedGrowth <|
                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity085RestrictedGrowth <|
                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity086RestrictedGrowth <|
                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity087RestrictedGrowth <|
                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity088RestrictedGrowth <|
                                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity089RestrictedGrowth <|
                                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity090RestrictedGrowth <|
                                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity091RestrictedGrowth <|
                                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity092RestrictedGrowth <|
                                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity093RestrictedGrowth <|
                                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity094RestrictedGrowth <|
                                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity095RestrictedGrowth <|
                                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity096RestrictedGrowth <|
                                                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity097RestrictedGrowth <|
                                                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity098RestrictedGrowth <|
                                                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity099RestrictedGrowth <|
                                                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity100RestrictedGrowth <|
                                                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity101RestrictedGrowth <|
                                                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity102RestrictedGrowth <|
                                                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity103RestrictedGrowth <|
                                                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity104RestrictedGrowth <|
                                                                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity105RestrictedGrowth <|
                                                                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity106RestrictedGrowth <|
                                                                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity107RestrictedGrowth <|
                                                                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity108RestrictedGrowth <|
                                                                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity109RestrictedGrowth <|
                                                                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity110RestrictedGrowth <|
                                                                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity111RestrictedGrowth <|
                                                                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity112RestrictedGrowth <|
                                                                                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity113RestrictedGrowth <|
                                                                                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity114RestrictedGrowth <|
                                                                                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity115RestrictedGrowth <|
                                                                                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity116RestrictedGrowth <|
                                                                                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity117RestrictedGrowth <|
                                                                                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity118RestrictedGrowth <|
                                                                                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity119RestrictedGrowth <|
                                                                                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity120RestrictedGrowth <|
                                                                                                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity121RestrictedGrowth <|
                                                                                                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity122RestrictedGrowth <|
                                                                                                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity123RestrictedGrowth <|
                                                                                                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity124RestrictedGrowth <|
                                                                                                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity125RestrictedGrowth <|
                                                                                                                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity126RestrictedGrowth <|
                                                                                                                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity127RestrictedGrowth <|
                                                                                                                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_nil) <|
      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity128RestrictedGrowth <|
        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity129RestrictedGrowth <|
          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity130RestrictedGrowth <|
            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity131RestrictedGrowth <|
              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity132RestrictedGrowth <|
                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity133RestrictedGrowth <|
                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity134RestrictedGrowth <|
                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity135RestrictedGrowth <|
                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity136RestrictedGrowth <|
                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity137RestrictedGrowth <|
                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity138RestrictedGrowth <|
                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity139RestrictedGrowth <|
                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity140RestrictedGrowth <|
                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity141RestrictedGrowth <|
                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity142RestrictedGrowth <|
                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity143RestrictedGrowth <|
                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity144RestrictedGrowth <|
                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity145RestrictedGrowth <|
                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity146RestrictedGrowth <|
                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity147RestrictedGrowth <|
                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity148RestrictedGrowth <|
                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity149RestrictedGrowth <|
                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity150RestrictedGrowth <|
                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity151RestrictedGrowth <|
                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity152RestrictedGrowth <|
                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity153RestrictedGrowth <|
                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity154RestrictedGrowth <|
                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity155RestrictedGrowth <|
                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity156RestrictedGrowth <|
                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity157RestrictedGrowth <|
                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity158RestrictedGrowth <|
                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity159RestrictedGrowth <|
                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity160RestrictedGrowth <|
                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity161RestrictedGrowth <|
                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity162RestrictedGrowth <|
                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity163RestrictedGrowth <|
                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity164RestrictedGrowth <|
                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity165RestrictedGrowth <|
                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity166RestrictedGrowth <|
                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity167RestrictedGrowth <|
                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity168RestrictedGrowth <|
                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity169RestrictedGrowth <|
                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity170RestrictedGrowth <|
                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity171RestrictedGrowth <|
                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity172RestrictedGrowth <|
                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity173RestrictedGrowth <|
                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity174RestrictedGrowth <|
                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity175RestrictedGrowth <|
                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity176RestrictedGrowth <|
                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity177RestrictedGrowth <|
                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity178RestrictedGrowth <|
                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity179RestrictedGrowth <|
                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity180RestrictedGrowth <|
                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity181RestrictedGrowth <|
                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity182RestrictedGrowth <|
                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity183RestrictedGrowth <|
                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity184RestrictedGrowth <|
                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity185RestrictedGrowth <|
                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_nil

set_option maxRecDepth 100000 in
def derivationRoots :
    List SemigroupBasis.FiniteNilpotentDecisionDAG.Root :=
  [
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 1]⟩⟩
        basisIndex := 0
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 1]⟩⟩
        basisIndex := 1
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩
        basisIndex := 2
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
        basisIndex := 3
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 4
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 5
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 6
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
        basisIndex := 7
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩
        basisIndex := 8
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩
        basisIndex := 10
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨0, [1, 0, 0]⟩⟩
        basisIndex := 11
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩
        basisIndex := 12
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩
        basisIndex := 13
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩
        basisIndex := 14
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩
        basisIndex := 15
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩
        basisIndex := 16
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
        basisIndex := 18
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 19
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 20
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 21
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩
        basisIndex := 22
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩
        basisIndex := 23
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩
        basisIndex := 24
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩
        basisIndex := 25
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 1]⟩⟩
        basisIndex := 26
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
        basisIndex := 27
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 28
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 29
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
        basisIndex := 31
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 1, 0]⟩⟩
        basisIndex := 32
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [0, 1, 0]⟩⟩
        basisIndex := 33
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩
        basisIndex := 34
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 2]⟩⟩
        basisIndex := 35
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 2]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 1, 2]⟩⟩
        basisIndex := 37
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 2]⟩⟩
        basisIndex := 38
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 1, 2]⟩⟩
        basisIndex := 39
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 1, 2]⟩⟩
        basisIndex := 40
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 2]⟩⟩
        basisIndex := 41
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 2]⟩⟩
        basisIndex := 42
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 43
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 0, 2]⟩⟩
        basisIndex := 44
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 0, 2]⟩⟩
        basisIndex := 45
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 2, 1]⟩⟩
        basisIndex := 46
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 1]⟩⟩
        basisIndex := 47
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 2, 1]⟩⟩
        basisIndex := 48
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 1]⟩⟩
        basisIndex := 49
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 50
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩
        basisIndex := 51
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 1]⟩⟩
        basisIndex := 52
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 53
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 0, 1]⟩⟩
        basisIndex := 54
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 0, 1]⟩⟩
        basisIndex := 55
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 1]⟩⟩
        basisIndex := 56
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 0, 1]⟩⟩
        basisIndex := 57
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 2, 0]⟩⟩
        basisIndex := 58
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 2, 0]⟩⟩
        basisIndex := 59
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [1, 2, 0]⟩⟩
        basisIndex := 60
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
        basisIndex := 61
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [0, 2, 0]⟩⟩
        basisIndex := 62
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 63
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨1, [2, 1, 0]⟩⟩
        basisIndex := 64
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 0]⟩⟩
        basisIndex := 65
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 1, 0]⟩⟩
        basisIndex := 66
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [0, 1, 0]⟩⟩
        basisIndex := 67
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 2]⟩, ⟨2, [1, 0, 0]⟩⟩
        basisIndex := 68
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1]⟩⟩
        basisIndex := 69
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩
        basisIndex := 70
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩
        basisIndex := 71
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 72
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 73
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 74
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩
        basisIndex := 75
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 0]⟩, ⟨1, [1, 0, 1]⟩⟩
        basisIndex := 76
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 77
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 78
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 79
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
        basisIndex := 80
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 1, 0]⟩⟩
        basisIndex := 81
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 2, 1]⟩⟩
        basisIndex := 82
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 1]⟩⟩
        basisIndex := 83
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 2, 1]⟩⟩
        basisIndex := 84
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 85
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 1]⟩⟩
        basisIndex := 86
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 1]⟩⟩
        basisIndex := 87
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 88
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 0, 1]⟩⟩
        basisIndex := 89
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 0, 1]⟩⟩
        basisIndex := 90
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 1, 2]⟩⟩
        basisIndex := 91
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩
        basisIndex := 92
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 1, 2]⟩⟩
        basisIndex := 93
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [0, 1, 2]⟩⟩
        basisIndex := 94
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [0, 1, 2]⟩⟩
        basisIndex := 95
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 96
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 0, 2]⟩⟩
        basisIndex := 97
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 0, 2]⟩⟩
        basisIndex := 98
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 0, 2]⟩⟩
        basisIndex := 99
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 0, 2]⟩⟩
        basisIndex := 100
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 1, 0]⟩⟩
        basisIndex := 101
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 1, 0]⟩⟩
        basisIndex := 102
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 103
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 0]⟩⟩
        basisIndex := 104
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [1, 2, 0]⟩⟩
        basisIndex := 105
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨2, [1, 2, 0]⟩⟩
        basisIndex := 106
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 0]⟩⟩
        basisIndex := 107
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [2, 2, 0]⟩⟩
        basisIndex := 108
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 1]⟩, ⟨1, [0, 2, 0]⟩⟩
        basisIndex := 109
        symmetry := false
        mapping := [1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 0]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 110
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 1, 0]⟩, ⟨0, [0, 0, 1]⟩⟩
        basisIndex := 111
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩
        basisIndex := 112
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0, 1]⟩, ⟨1, [1, 1, 0]⟩⟩
        basisIndex := 113
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 1, 2]⟩⟩
        basisIndex := 114
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 1, 2]⟩⟩
        basisIndex := 115
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩
        basisIndex := 116
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 0, 2]⟩⟩
        basisIndex := 117
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 118
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩
        basisIndex := 119
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 0, 2]⟩⟩
        basisIndex := 120
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 2, 1]⟩⟩
        basisIndex := 121
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 2, 1]⟩⟩
        basisIndex := 122
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [0, 2, 1]⟩⟩
        basisIndex := 123
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 124
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 125
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 0, 1]⟩⟩
        basisIndex := 126
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 0, 1]⟩⟩
        basisIndex := 127
        symmetry := false
        mapping := [2, 1, 0]
      }
  ] ++
  [
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [0, 0, 1]⟩⟩
        basisIndex := 128
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 2, 0]⟩⟩
        basisIndex := 129
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [1, 2, 0]⟩⟩
        basisIndex := 130
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2, 0]⟩⟩
        basisIndex := 131
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 132
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨1, [2, 1, 0]⟩⟩
        basisIndex := 133
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨0, [2, 1, 0]⟩⟩
        basisIndex := 134
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1, 2]⟩, ⟨2, [1, 1, 0]⟩⟩
        basisIndex := 135
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩
        basisIndex := 136
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩
        basisIndex := 137
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨2, [0, 1]⟩⟩
        basisIndex := 138
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩
        basisIndex := 139
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 2, 0]⟩⟩
        basisIndex := 140
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 2, 0]⟩⟩
        basisIndex := 141
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩
        basisIndex := 142
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 143
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [2, 1, 0]⟩⟩
        basisIndex := 144
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2]⟩⟩
        basisIndex := 145
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [1, 0, 2]⟩⟩
        basisIndex := 146
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 147
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2]⟩⟩
        basisIndex := 148
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 1, 2]⟩⟩
        basisIndex := 149
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 1, 2]⟩⟩
        basisIndex := 150
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 0, 1]⟩⟩
        basisIndex := 151
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 152
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 153
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨2, [0, 2, 1]⟩⟩
        basisIndex := 154
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 2, 0]⟩, ⟨1, [0, 2, 1]⟩⟩
        basisIndex := 155
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 156
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩
        basisIndex := 157
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [0, 1, 2]⟩⟩
        basisIndex := 158
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨2, [1, 2, 0]⟩⟩
        basisIndex := 159
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [1, 2, 0]⟩⟩
        basisIndex := 160
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 161
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨1, [2, 1, 0]⟩⟩
        basisIndex := 162
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 163
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 164
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 0, 2]⟩, ⟨0, [2, 0, 1]⟩⟩
        basisIndex := 165
        symmetry := false
        mapping := [2, 0, 1]
      },
      {
        target := ⟨⟨0, [0, 1, 2]⟩, ⟨1, [1, 0, 2]⟩⟩
        basisIndex := 166
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩
        basisIndex := 167
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 0, 1]⟩⟩
        basisIndex := 168
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [0, 1, 2]⟩, ⟨2, [2, 1, 0]⟩⟩
        basisIndex := 169
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩
        basisIndex := 170
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩
        basisIndex := 171
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨2, [0, 1, 3]⟩⟩
        basisIndex := 172
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨2, [1, 0, 3]⟩⟩
        basisIndex := 173
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [1, 3, 2]⟩⟩
        basisIndex := 174
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 3, 2]⟩⟩
        basisIndex := 175
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 1, 2]⟩⟩
        basisIndex := 176
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 1, 2]⟩⟩
        basisIndex := 177
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨1, [3, 0, 2]⟩⟩
        basisIndex := 178
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 0, 2]⟩⟩
        basisIndex := 179
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [3, 2, 1]⟩⟩
        basisIndex := 180
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [0, 2, 1]⟩⟩
        basisIndex := 181
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨2, [3, 0, 1]⟩⟩
        basisIndex := 182
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 0, 1]⟩⟩
        basisIndex := 183
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [1, 2, 0]⟩⟩
        basisIndex := 184
        symmetry := false
        mapping := [3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 2, 3]⟩, ⟨3, [2, 1, 0]⟩⟩
        basisIndex := 185
        symmetry := false
        mapping := [3, 2, 1, 0]
      }
  ]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem listed : FiniteCertificate.DerivesAll basis inventory :=
  SemigroupBasis.FiniteNilpotentDecisionDAG.check_sound
    (basis := basis) (identities := inventory)
    (roots := derivationRoots) (by decide)

theorem toCommon :
    forall word : Word Nat,
      5 <= word.toList.length -> Derives basis word common :=
  SemigroupBasis.FiniteNilpotentLongCollapse.toCommonFive_of_check
    (by decide)

def certificate : SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.SignatureCertificate where
  toCommon := toCommon
  listed := listed

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399
