/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.Signature
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.S6_583CounterexamplesPart01
import SemigroupBasis.Generated.Order6Nilpotent.S6_583

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.S6_583

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_583.table
abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signaturea4ec0a4dda32.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signaturea4ec0a4dda32.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signaturea4ec0a4dda32.representativeCommon
abbrev counterexamples := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.S6_583CounterexamplesPart01.rows

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
    (⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity02ToFinite basisIdentity02FromFinite (by decide) (by decide)

def basisIdentity03ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity03FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity03Valid :
    (⟨⟨0, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity03ToFinite basisIdentity03FromFinite (by decide) (by decide)

def basisIdentity04ToFinite : Nat -> Fin 5
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | 4 => ⟨4, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity04FromFinite
    (index : Fin 5) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem basisIdentity04Valid :
    (⟨⟨0, [0, 0]⟩, ⟨4, [3, 2, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨4, [3, 2, 1]⟩⟩ : Identity Nat)
    basisIdentity04ToFinite basisIdentity04FromFinite (by decide) (by decide)

def basisIdentity05ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity05FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity05Valid :
    (⟨⟨1, [0, 0]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat)
    basisIdentity05ToFinite basisIdentity05FromFinite (by decide) (by decide)

def basisIdentity06ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity06FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity06Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity06ToFinite basisIdentity06FromFinite (by decide) (by decide)

def basisIdentity07ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity07FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity07Valid :
    (⟨⟨1, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity07ToFinite basisIdentity07FromFinite (by decide) (by decide)

def basisIdentity08ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity08FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity08Valid :
    (⟨⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat)
    basisIdentity08ToFinite basisIdentity08FromFinite (by decide) (by decide)

def basisIdentity09ToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity09FromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity09Valid :
    (⟨⟨1, [0, 0]⟩, ⟨3, [2, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨3, [2, 2]⟩⟩ : Identity Nat)
    basisIdentity09ToFinite basisIdentity09FromFinite (by decide) (by decide)

def basisIdentity10LeftToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity10LeftFromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity10LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨1, [0, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨1, [0, 0]⟩ basisIdentity10LeftToFinite
    basisIdentity10LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity10RightToFinite : Nat -> Fin 4
  | 2 => ⟨0, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨2, by decide⟩
  | 5 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity10RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity10RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨5, [4, 3, 2]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨5, [4, 3, 2]⟩ basisIdentity10RightToFinite
    basisIdentity10RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity10Valid :
    (⟨⟨1, [0, 0]⟩, ⟨5, [4, 3, 2]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity10LeftValue valuation).trans
    (basisIdentity10RightValue valuation).symm

def basisIdentity11ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity11FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity11Valid :
    (⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat)
    basisIdentity11ToFinite basisIdentity11FromFinite (by decide) (by decide)

def basisIdentity12LeftToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity12LeftFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity12LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨3, [2, 1, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨3, [2, 1, 0]⟩ basisIdentity12LeftToFinite
    basisIdentity12LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity12RightToFinite : Nat -> Fin 4
  | 4 => ⟨0, by decide⟩
  | 5 => ⟨1, by decide⟩
  | 6 => ⟨2, by decide⟩
  | 7 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity12RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | _ => 4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity12RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨7, [6, 5, 4]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨7, [6, 5, 4]⟩ basisIdentity12RightToFinite
    basisIdentity12RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity12Valid :
    (⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity12LeftValue valuation).trans
    (basisIdentity12RightValue valuation).symm

theorem models : Models table.semigroup basis := by
  change Models table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.basis
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.basis_eq]
  exact
    FiniteNilpotentCounterexample.models_cons basisIdentity00Valid <|
      FiniteNilpotentCounterexample.models_cons basisIdentity01Valid <|
        FiniteNilpotentCounterexample.models_cons basisIdentity02Valid <|
          FiniteNilpotentCounterexample.models_cons basisIdentity03Valid <|
            FiniteNilpotentCounterexample.models_cons basisIdentity04Valid <|
              FiniteNilpotentCounterexample.models_cons basisIdentity05Valid <|
                FiniteNilpotentCounterexample.models_cons basisIdentity06Valid <|
                  FiniteNilpotentCounterexample.models_cons basisIdentity07Valid <|
                    FiniteNilpotentCounterexample.models_cons basisIdentity08Valid <|
                      FiniteNilpotentCounterexample.models_cons basisIdentity09Valid <|
                        FiniteNilpotentCounterexample.models_cons basisIdentity10Valid <|
                          FiniteNilpotentCounterexample.models_cons basisIdentity11Valid <|
                            FiniteNilpotentCounterexample.models_cons basisIdentity12Valid <|
                              FiniteNilpotentCounterexample.models_nil table.semigroup

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem counterexamplesChecked :
    FiniteNilpotentCounterexample.check table.semigroup
      (candidateDomain 4) inventory counterexamples = true := by
  decide

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.inventoryRestrictedGrowth

theorem inventoryTableValid :
    FiniteCertificate.AllTableValid table inventory := by
  intro identity member valuation
  exact Derives.sound models
    (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.listed identity member) valuation

def inventoryCertificate :
    FiniteNilpotentCertificate.Inventory table 4 common where
  identities := inventory
  restrictedGrowth := inventoryRestrictedGrowth
  tableValid := inventoryTableValid
  complete := FiniteNilpotentCounterexample.inventoryCompleteOfCheck
    (G := table.semigroup) (inventory := inventory)
    (rows := counterexamples) (by decide) (by decide)
    counterexamplesChecked

def classCertificate : SemigroupBasis.Generated.Order6Nilpotent.S6_583.ClassCertificate where
  models := models
  inventory := inventoryCertificate
  inventoryIdentities_eq := rfl

/-- Unconditional representative endpoint for this order-six class. -/
theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Signaturea4ec0a4dda32.representativeBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_583.representative_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.certificate classCertificate

/-- Unconditional anti-isomorphic endpoint from the same certificates. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6Nilpotent.Signaturea4ec0a4dda32.rootBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_583.opposite_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.certificate classCertificate

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signaturea4ec0a4dda32.S6_583
