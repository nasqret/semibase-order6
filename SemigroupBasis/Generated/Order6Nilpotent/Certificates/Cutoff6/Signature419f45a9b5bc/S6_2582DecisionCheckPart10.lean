/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart10
import SemigroupBasis.Generated.Order6Nilpotent.S6_2582

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart10

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2582.table
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeInventoryIdentities
abbrev evidenceChunks := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart10.chunks

private theorem shortPairDomainLength :
    (shortPairDomain 6).length = 175477 := by
  simp [shortPairDomain, positiveBelow,
    length_identitiesAtLengths]
  decide

private theorem candidateSlice_eq :
    ((candidateDomain 6).drop 180000) = ((exactCommonDomain 6).drop 4523) := by
  have offsetEq :
      180000 = (shortPairDomain 6).length + 4523 := by
    rw [shortPairDomainLength]
  rw [candidateDomain, offsetEq,
    List.drop_length_add_append]

set_option maxHeartbeats 1950400 in
set_option maxRecDepth 262144 in
theorem evidenceCountChecked :
    FiniteNilpotentDecisionPartition.evidenceCount evidenceChunks = 19504 := by
  decide

abbrev evidenceHeadChunks := evidenceChunks.take 76
abbrev evidenceTailChunks := evidenceChunks.drop 76

set_option maxRecDepth 262144 in
theorem headEvidenceCountChecked :
    FiniteNilpotentDecisionPartition.evidenceCount evidenceHeadChunks = 9728 := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 262144 in
private theorem exactHeadChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunksPrefix table.semigroup
      inventory ((exactCommonDomain 6).drop 4523) evidenceHeadChunks = true := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 262144 in
private theorem exactTailChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunks table.semigroup
      ((exactCommonDomain 6).drop 14251) inventory evidenceTailChunks = true := by
  decide

private theorem exactCheckedDirect :
    FiniteNilpotentDecisionPartition.checkStreamChunks table.semigroup
      ((exactCommonDomain 6).drop 4523) inventory evidenceChunks = true := by
  rw [(List.take_append_drop 76 evidenceChunks).symm]
  apply FiniteNilpotentDecisionPartition.checkStreamChunks_append_of_prefix
      table.semigroup inventory ((exactCommonDomain 6).drop 4523)
      evidenceHeadChunks evidenceTailChunks exactHeadChecked
  simpa only [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount,
    headEvidenceCountChecked, List.drop_drop] using exactTailChecked

set_option maxHeartbeats 1950400 in
set_option maxRecDepth 262144 in
theorem exactChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunks table.semigroup
      ((candidateDomain 6).drop 180000) inventory evidenceChunks = true := by
  rw [candidateSlice_eq]
  exact exactCheckedDirect

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart10
