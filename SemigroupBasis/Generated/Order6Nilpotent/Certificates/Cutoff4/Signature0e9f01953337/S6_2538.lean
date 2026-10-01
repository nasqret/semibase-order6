/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.Signature
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.S6_2538CounterexamplesPart01
import SemigroupBasis.Generated.Order6Nilpotent.S6_2538

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.S6_2538

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2538.table
abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeCommon
abbrev counterexamples := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.S6_2538CounterexamplesPart01.rows

def basisIdentity00ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity00FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity00Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat)
    basisIdentity00ToFinite basisIdentity00FromFinite (by decide) (by decide)

def basisIdentity01ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity01FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity01Valid :
    (⟨⟨1, [0, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat)
    basisIdentity01ToFinite basisIdentity01FromFinite (by decide) (by decide)

def basisIdentity02ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity02FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity02Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity02ToFinite basisIdentity02FromFinite (by decide) (by decide)

def basisIdentity03ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity03FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity03Valid :
    (⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat)
    basisIdentity03ToFinite basisIdentity03FromFinite (by decide) (by decide)

def basisIdentity04ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity04FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity04Valid :
    (⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩ : Identity Nat)
    basisIdentity04ToFinite basisIdentity04FromFinite (by decide) (by decide)

def basisIdentity05LeftToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity05LeftFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity05LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨3, [2, 1, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨3, [2, 1, 0]⟩ basisIdentity05LeftToFinite
    basisIdentity05LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity05RightToFinite : Nat -> Fin 4
  | 4 => ⟨0, by decide⟩
  | 5 => ⟨1, by decide⟩
  | 6 => ⟨2, by decide⟩
  | 7 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity05RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | _ => 4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity05RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨7, [6, 5, 4]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨7, [6, 5, 4]⟩ basisIdentity05RightToFinite
    basisIdentity05RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity05Valid :
    (⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity05LeftValue valuation).trans
    (basisIdentity05RightValue valuation).symm

theorem models : Models table.semigroup basis := by
  change Models table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.basis
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.basis_eq]
  exact
    FiniteNilpotentCounterexample.models_cons basisIdentity00Valid <|
      FiniteNilpotentCounterexample.models_cons basisIdentity01Valid <|
        FiniteNilpotentCounterexample.models_cons basisIdentity02Valid <|
          FiniteNilpotentCounterexample.models_cons basisIdentity03Valid <|
            FiniteNilpotentCounterexample.models_cons basisIdentity04Valid <|
              FiniteNilpotentCounterexample.models_cons basisIdentity05Valid <|
                FiniteNilpotentCounterexample.models_nil table.semigroup

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem counterexamplesChecked :
    FiniteNilpotentCounterexample.check table.semigroup
      (candidateDomain 4) inventory counterexamples = true := by
  decide

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.inventoryRestrictedGrowth

theorem inventoryTableValid :
    FiniteCertificate.AllTableValid table inventory := by
  intro identity member valuation
  exact Derives.sound models
    (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.listed identity member) valuation

def inventoryCertificate :
    FiniteNilpotentCertificate.Inventory table 4 common where
  identities := inventory
  restrictedGrowth := inventoryRestrictedGrowth
  tableValid := inventoryTableValid
  complete := FiniteNilpotentCounterexample.inventoryCompleteOfCheck
    (G := table.semigroup) (inventory := inventory)
    (rows := counterexamples) (by decide) (by decide)
    counterexamplesChecked

def classCertificate : SemigroupBasis.Generated.Order6Nilpotent.S6_2538.ClassCertificate where
  models := models
  inventory := inventoryCertificate
  inventoryIdentities_eq := rfl

/-- Unconditional representative endpoint for this order-six class. -/
theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2538.representative_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.certificate classCertificate

/-- Unconditional anti-isomorphic endpoint from the same certificates. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.rootBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_2538.opposite_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.certificate classCertificate

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337.S6_2538
