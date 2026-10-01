/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.Signature
import SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.S6_481CounterexamplesPart01
import SemigroupBasis.Generated.Order6Nilpotent.S6_481

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.S6_481

open SemigroupBasis
open SemigroupBasis.FiniteNilpotentRestrictedGrowthEnumerator

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_481.table
abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signatured2a3ad6afd4b.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signatured2a3ad6afd4b.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signatured2a3ad6afd4b.representativeCommon
abbrev counterexamples := SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.S6_481CounterexamplesPart01.rows

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
    (⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity03ToFinite basisIdentity03FromFinite (by decide) (by decide)

def basisIdentity04ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity04FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity04Valid :
    (⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity05ToFinite basisIdentity05FromFinite (by decide) (by decide)

def basisIdentity06ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity06FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity06Valid :
    (⟨⟨0, [0, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat)
    basisIdentity06ToFinite basisIdentity06FromFinite (by decide) (by decide)

def basisIdentity07ToFinite : Nat -> Fin 5
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | 4 => ⟨4, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity07FromFinite
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
theorem basisIdentity07Valid :
    (⟨⟨0, [0, 0]⟩, ⟨4, [3, 2, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [0, 0]⟩, ⟨4, [3, 2, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat)
    basisIdentity08ToFinite basisIdentity08FromFinite (by decide) (by decide)

def basisIdentity09ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity09FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity09Valid :
    (⟨⟨1, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat)
    basisIdentity09ToFinite basisIdentity09FromFinite (by decide) (by decide)

def basisIdentity10ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity10FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity10Valid :
    (⟨⟨1, [0, 0]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat)
    basisIdentity10ToFinite basisIdentity10FromFinite (by decide) (by decide)

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
    (⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat)
    basisIdentity11ToFinite basisIdentity11FromFinite (by decide) (by decide)

def basisIdentity12ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity12FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity12Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity12ToFinite basisIdentity12FromFinite (by decide) (by decide)

def basisIdentity13ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity13FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity13Valid :
    (⟨⟨1, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat)
    basisIdentity13ToFinite basisIdentity13FromFinite (by decide) (by decide)

def basisIdentity14ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity14FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity14Valid :
    (⟨⟨1, [0, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat)
    basisIdentity14ToFinite basisIdentity14FromFinite (by decide) (by decide)

def basisIdentity15ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity15FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity15Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat)
    basisIdentity15ToFinite basisIdentity15FromFinite (by decide) (by decide)

def basisIdentity16ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity16FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity16Valid :
    (⟨⟨1, [0, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat)
    basisIdentity16ToFinite basisIdentity16FromFinite (by decide) (by decide)

def basisIdentity17ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity17FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity17Valid :
    (⟨⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat)
    basisIdentity17ToFinite basisIdentity17FromFinite (by decide) (by decide)

def basisIdentity18ToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity18FromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity18Valid :
    (⟨⟨1, [0, 0]⟩, ⟨3, [2, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨3, [2, 2]⟩⟩ : Identity Nat)
    basisIdentity18ToFinite basisIdentity18FromFinite (by decide) (by decide)

def basisIdentity19ToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity19FromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity19Valid :
    (⟨⟨1, [0, 0]⟩, ⟨3, [3, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨3, [3, 2]⟩⟩ : Identity Nat)
    basisIdentity19ToFinite basisIdentity19FromFinite (by decide) (by decide)

def basisIdentity20LeftToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity20LeftFromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity20LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨1, [0, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨1, [0, 0]⟩ basisIdentity20LeftToFinite
    basisIdentity20LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity20RightToFinite : Nat -> Fin 4
  | 2 => ⟨0, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨2, by decide⟩
  | 5 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity20RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity20RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨5, [4, 3, 2]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨5, [4, 3, 2]⟩ basisIdentity20RightToFinite
    basisIdentity20RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity20Valid :
    (⟨⟨1, [0, 0]⟩, ⟨5, [4, 3, 2]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity20LeftValue valuation).trans
    (basisIdentity20RightValue valuation).symm

def basisIdentity21ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity21FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity21Valid :
    (⟨⟨1, [1, 0]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat)
    basisIdentity21ToFinite basisIdentity21FromFinite (by decide) (by decide)

def basisIdentity22ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity22FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity22Valid :
    (⟨⟨1, [1, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat)
    basisIdentity22ToFinite basisIdentity22FromFinite (by decide) (by decide)

def basisIdentity23ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity23FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity23Valid :
    (⟨⟨1, [1, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat)
    basisIdentity23ToFinite basisIdentity23FromFinite (by decide) (by decide)

def basisIdentity24ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity24FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity24Valid :
    (⟨⟨1, [1, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat)
    basisIdentity24ToFinite basisIdentity24FromFinite (by decide) (by decide)

def basisIdentity25ToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity25FromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity25Valid :
    (⟨⟨1, [1, 0]⟩, ⟨3, [3, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0]⟩, ⟨3, [3, 2]⟩⟩ : Identity Nat)
    basisIdentity25ToFinite basisIdentity25FromFinite (by decide) (by decide)

def basisIdentity26LeftToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity26LeftFromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity26LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨1, [1, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨1, [1, 0]⟩ basisIdentity26LeftToFinite
    basisIdentity26LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity26RightToFinite : Nat -> Fin 4
  | 2 => ⟨0, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨2, by decide⟩
  | 5 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity26RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity26RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨5, [4, 3, 2]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨5, [4, 3, 2]⟩ basisIdentity26RightToFinite
    basisIdentity26RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity26Valid :
    (⟨⟨1, [1, 0]⟩, ⟨5, [4, 3, 2]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity26LeftValue valuation).trans
    (basisIdentity26RightValue valuation).symm

def basisIdentity27ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity27FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity27Valid :
    (⟨⟨2, [1, 0]⟩, ⟨0, [1, 2]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0]⟩, ⟨0, [1, 2]⟩⟩ : Identity Nat)
    basisIdentity27ToFinite basisIdentity27FromFinite (by decide) (by decide)

def basisIdentity28LeftToFinite : Nat -> Fin 4
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity28LeftFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity28LeftValue :
    forall valuation,
      table.semigroup.eval valuation ⟨3, [2, 1, 0]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨3, [2, 1, 0]⟩ basisIdentity28LeftToFinite
    basisIdentity28LeftFromFinite (by decide) (0 : Fin 6)
    (by decide)

def basisIdentity28RightToFinite : Nat -> Fin 4
  | 4 => ⟨0, by decide⟩
  | 5 => ⟨1, by decide⟩
  | 6 => ⟨2, by decide⟩
  | 7 => ⟨3, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity28RightFromFinite
    (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | _ => 4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity28RightValue :
    forall valuation,
      table.semigroup.eval valuation ⟨7, [6, 5, 4]⟩ =
        (0 : Fin 6) :=
  FiniteNilpotentCounterexample.wordValueNat_of_fused_check
    table ⟨7, [6, 5, 4]⟩ basisIdentity28RightToFinite
    basisIdentity28RightFromFinite (by decide) (0 : Fin 6)
    (by decide)

theorem basisIdentity28Valid :
    (⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩ : Identity Nat).SatisfiedBy
      table.semigroup := by
  intro valuation
  exact (basisIdentity28LeftValue valuation).trans
    (basisIdentity28RightValue valuation).symm

theorem models : Models table.semigroup basis := by
  change Models table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.basis
  rw [SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.basis_eq]
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
                              FiniteNilpotentCounterexample.models_cons basisIdentity13Valid <|
                                FiniteNilpotentCounterexample.models_cons basisIdentity14Valid <|
                                  FiniteNilpotentCounterexample.models_cons basisIdentity15Valid <|
                                    FiniteNilpotentCounterexample.models_cons basisIdentity16Valid <|
                                      FiniteNilpotentCounterexample.models_cons basisIdentity17Valid <|
                                        FiniteNilpotentCounterexample.models_cons basisIdentity18Valid <|
                                          FiniteNilpotentCounterexample.models_cons basisIdentity19Valid <|
                                            FiniteNilpotentCounterexample.models_cons basisIdentity20Valid <|
                                              FiniteNilpotentCounterexample.models_cons basisIdentity21Valid <|
                                                FiniteNilpotentCounterexample.models_cons basisIdentity22Valid <|
                                                  FiniteNilpotentCounterexample.models_cons basisIdentity23Valid <|
                                                    FiniteNilpotentCounterexample.models_cons basisIdentity24Valid <|
                                                      FiniteNilpotentCounterexample.models_cons basisIdentity25Valid <|
                                                        FiniteNilpotentCounterexample.models_cons basisIdentity26Valid <|
                                                          FiniteNilpotentCounterexample.models_cons basisIdentity27Valid <|
                                                            FiniteNilpotentCounterexample.models_cons basisIdentity28Valid <|
                                                              FiniteNilpotentCounterexample.models_nil table.semigroup

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem counterexamplesChecked :
    FiniteNilpotentCounterexample.check table.semigroup
      (candidateDomain 4) inventory counterexamples = true := by
  decide

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory :=
  SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.inventoryRestrictedGrowth

theorem inventoryTableValid :
    FiniteCertificate.AllTableValid table inventory := by
  intro identity member valuation
  exact Derives.sound models
    (SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.listed identity member) valuation

def inventoryCertificate :
    FiniteNilpotentCertificate.Inventory table 4 common where
  identities := inventory
  restrictedGrowth := inventoryRestrictedGrowth
  tableValid := inventoryTableValid
  complete := FiniteNilpotentCounterexample.inventoryCompleteOfCheck
    (G := table.semigroup) (inventory := inventory)
    (rows := counterexamples) (by decide) (by decide)
    counterexamplesChecked

def classCertificate : SemigroupBasis.Generated.Order6Nilpotent.S6_481.ClassCertificate where
  models := models
  inventory := inventoryCertificate
  inventoryIdentities_eq := rfl

/-- Unconditional representative endpoint for this order-six class. -/
theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.Generated.Order6Nilpotent.Signatured2a3ad6afd4b.representativeBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_481.representative_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.certificate classCertificate

/-- Unconditional anti-isomorphic endpoint from the same certificates. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6Nilpotent.Signatured2a3ad6afd4b.rootBasis :=
  SemigroupBasis.Generated.Order6Nilpotent.S6_481.opposite_basis
    SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.certificate classCertificate

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signatured2a3ad6afd4b.S6_481
