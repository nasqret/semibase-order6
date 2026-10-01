/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart06
import SemigroupBasis.Generated.Order6Nilpotent.S6_2582

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart06

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2582.table
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeInventoryIdentities
abbrev evidenceChunks := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart06.chunks

private theorem candidateSlice_eq :
    ((candidateDomain 6).drop 100000) = ((((((candidateDomain 6).drop 20000).drop 20000).drop 20000).drop 20000).drop 20000) := by
  simp only [List.drop_drop]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 262144 in
theorem evidenceCountChecked :
    FiniteNilpotentDecisionPartition.evidenceCount evidenceChunks = 20000 := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 262144 in
private theorem prefixCheckedDirect :
    FiniteNilpotentDecisionPartition.checkStreamChunksPrefix table.semigroup
      inventory ((((((candidateDomain 6).drop 20000).drop 20000).drop 20000).drop 20000).drop 20000) evidenceChunks = true := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 262144 in
theorem prefixChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunksPrefix table.semigroup
      inventory ((candidateDomain 6).drop 100000) evidenceChunks = true := by
  rw [candidateSlice_eq]
  exact prefixCheckedDirect

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart06
