/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.Signature
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582Counterexamples
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart01
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart02
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart03
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart04
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart05
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart06
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart07
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart08
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart09
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart10
import SemigroupBasis.CoRoots.Order6S6_2582CompactModels
import SemigroupBasis.Generated.Order6Nilpotent.S6_2582

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2582.table
abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeCommon
abbrev decisionChunks := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582Counterexamples.chunks

theorem models : Models table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6S6_2582CompactModels.models

set_option maxRecDepth 262144 in
theorem decisionPartitionChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunks table.semigroup
      (candidateDomain 6) inventory decisionChunks = true := by
  change
    FiniteNilpotentDecisionPartition.checkStreamChunksAux
      table.semigroup inventory
      (candidateDomain 6)
      (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart01.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart02.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart03.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart04.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart05.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart06.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart07.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart08.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart09.chunks ++
        (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582CounterexamplesPart10.chunks)))))))))) = true
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart01.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart01.evidenceCountChecked]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart02.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart02.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart03.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart03.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart04.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart04.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart05.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart05.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart06.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart06.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart07.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart07.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart08.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart08.evidenceCountChecked]
  simp only [List.drop_drop]
  rw [FiniteNilpotentDecisionPartition.checkStreamChunksAux_append]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart09.prefixChecked]
  simp only [Bool.true_and]
  rw [FiniteNilpotentDecisionPartition.dropStreamChunks_eq_drop_evidenceCount]
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart09.evidenceCountChecked]
  simp only [List.drop_drop]
  simpa only [FiniteNilpotentDecisionPartition.checkStreamChunks] using
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582DecisionCheckPart10.exactChecked

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.inventoryRestrictedGrowth

theorem inventoryTableValid :
    FiniteCertificate.AllTableValid table inventory := by
  intro identity member valuation
  exact Derives.sound models
    (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.listed identity member) valuation

def inventoryCertificate :
    FiniteNilpotentCertificate.Inventory table 6 common where
  identities := inventory
  restrictedGrowth := inventoryRestrictedGrowth
  tableValid := inventoryTableValid
  complete := FiniteNilpotentDecisionPartition.inventoryCompleteOfStreamChunksCheck
    (G := table.semigroup) (inventory := inventory)
    (evidenceChunks := decisionChunks) (by decide) (by decide)
    decisionPartitionChecked

def classCertificate : SemigroupBasis.Generated.Order6Nilpotent.S6_2582.ClassCertificate where
  models := models
  inventory := inventoryCertificate
  inventoryIdentities_eq := rfl

/-- Unconditional representative endpoint for this order-six class. -/
theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.representativeBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2582.representative_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.certificate classCertificate

/-- Unconditional anti-isomorphic endpoint from the same certificates. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6Nilpotent.Signature419f45a9b5bc.rootBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2582.opposite_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.certificate classCertificate

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff6.Signature419f45a9b5bc.S6_2582
