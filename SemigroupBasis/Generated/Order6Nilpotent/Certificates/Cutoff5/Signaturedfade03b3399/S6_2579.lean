/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.Signature
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579CounterexamplesPart01
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart01
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart02
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart03
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart04
import SemigroupBasis.Generated.Order6Nilpotent.S6_2579

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2579.table
abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeCommon
abbrev decisionChunks := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579CounterexamplesPart01.chunks

theorem models : Models table.semigroup basis := by
  change Models table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.basis
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.basis_eq]
  simpa only [List.append_assoc] using
    (FiniteNilpotentCounterexample.models_append
      SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart01.modelsLocal <|
      FiniteNilpotentCounterexample.models_append
        SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart02.modelsLocal <|
        FiniteNilpotentCounterexample.models_append
          SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart03.modelsLocal <|
          SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart04.modelsLocal)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem decisionPartitionChecked :
    FiniteNilpotentDecisionPartition.checkStreamChunks table.semigroup
      (candidateDomain 5) inventory decisionChunks = true := by
  decide

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.inventoryRestrictedGrowth

theorem inventoryTableValid :
    FiniteCertificate.AllTableValid table inventory := by
  intro identity member valuation
  exact Derives.sound models
    (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.listed identity member) valuation

def inventoryCertificate :
    FiniteNilpotentCertificate.Inventory table 5 common where
  identities := inventory
  restrictedGrowth := inventoryRestrictedGrowth
  tableValid := inventoryTableValid
  complete := FiniteNilpotentDecisionPartition.inventoryCompleteOfStreamChunksCheck
    (G := table.semigroup) (inventory := inventory)
    (evidenceChunks := decisionChunks) (by decide) (by decide)
    decisionPartitionChecked

def classCertificate : SemigroupBasis.Generated.Order6Nilpotent.S6_2579.ClassCertificate where
  models := models
  inventory := inventoryCertificate
  inventoryIdentities_eq := rfl

/-- Unconditional representative endpoint for this order-six class. -/
theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.representativeBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2579.representative_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.certificate classCertificate

/-- Unconditional anti-isomorphic endpoint from the same certificates. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6Nilpotent.Signaturedfade03b3399.rootBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2579.opposite_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.certificate classCertificate

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579
