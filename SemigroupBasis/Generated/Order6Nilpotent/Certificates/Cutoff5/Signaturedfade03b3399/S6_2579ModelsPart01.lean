/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6Nilpotent.S6_2579

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart01

open SemigroupBasis

abbrev table := SemigroupBasis.Generated.Order6Nilpotent.S6_2579.table

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
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity04ToFinite basisIdentity04FromFinite (by decide) (by decide)

def basisIdentity05ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity05FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity05Valid :
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity06ToFinite basisIdentity06FromFinite (by decide) (by decide)

def basisIdentity07ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity07FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity07Valid :
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity07ToFinite basisIdentity07FromFinite (by decide) (by decide)

def basisIdentity08ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity08FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity08Valid :
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity09ToFinite basisIdentity09FromFinite (by decide) (by decide)

def basisIdentity10ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity10FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity10Valid :
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0, 0]⟩, ⟨0, [1, 1, 1]⟩⟩ : Identity Nat)
    basisIdentity12ToFinite basisIdentity12FromFinite (by decide) (by decide)

def basisIdentity13ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity13FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity13Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat)
    basisIdentity13ToFinite basisIdentity13FromFinite (by decide) (by decide)

def basisIdentity14ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity14FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity14Valid :
    (⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat)
    basisIdentity14ToFinite basisIdentity14FromFinite (by decide) (by decide)

def basisIdentity15ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity15FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity15Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 0]⟩⟩ : Identity Nat)
    basisIdentity15ToFinite basisIdentity15FromFinite (by decide) (by decide)

def basisIdentity16ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity16FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity16Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity16ToFinite basisIdentity16FromFinite (by decide) (by decide)

def basisIdentity17ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity17FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity17Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity17ToFinite basisIdentity17FromFinite (by decide) (by decide)

def basisIdentity18ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity18FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity18Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity18ToFinite basisIdentity18FromFinite (by decide) (by decide)

def basisIdentity19ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity19FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity19Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity19ToFinite basisIdentity19FromFinite (by decide) (by decide)

def basisIdentity20ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity20FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity20Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity20ToFinite basisIdentity20FromFinite (by decide) (by decide)

def basisIdentity21ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity21FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity21Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat)
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
    (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity22ToFinite basisIdentity22FromFinite (by decide) (by decide)

def basisIdentity23ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity23FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity23Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity23ToFinite basisIdentity23FromFinite (by decide) (by decide)

def basisIdentity24ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity24FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity24Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat)
    basisIdentity24ToFinite basisIdentity24FromFinite (by decide) (by decide)

def basisIdentity25ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity25FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity25Valid :
    (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨0, [1, 0, 0]⟩, ⟨1, [0, 1, 1]⟩⟩ : Identity Nat)
    basisIdentity25ToFinite basisIdentity25FromFinite (by decide) (by decide)

def basisIdentity26ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity26FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity26Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity26ToFinite basisIdentity26FromFinite (by decide) (by decide)

def basisIdentity27ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity27FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity27Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity27ToFinite basisIdentity27FromFinite (by decide) (by decide)

def basisIdentity28ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity28FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity28Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity28ToFinite basisIdentity28FromFinite (by decide) (by decide)

def basisIdentity29ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity29FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity29Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity29ToFinite basisIdentity29FromFinite (by decide) (by decide)

def basisIdentity30ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity30FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity30Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity30ToFinite basisIdentity30FromFinite (by decide) (by decide)

def basisIdentity31ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity31FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity31Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity31ToFinite basisIdentity31FromFinite (by decide) (by decide)

def basisIdentity32ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity32FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity32Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨0, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity32ToFinite basisIdentity32FromFinite (by decide) (by decide)

def basisIdentity33ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity33FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity33Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨1, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity33ToFinite basisIdentity33FromFinite (by decide) (by decide)

def basisIdentity34ToFinite : Nat -> Fin 2
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity34FromFinite
    (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity34Valid :
    (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨1, [1, 0, 0]⟩, ⟨0, [0, 1, 1]⟩⟩ : Identity Nat)
    basisIdentity34ToFinite basisIdentity34FromFinite (by decide) (by decide)

def basisIdentity35ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity35FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity35Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 0, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 0, 0]⟩⟩ : Identity Nat)
    basisIdentity35ToFinite basisIdentity35FromFinite (by decide) (by decide)

def basisIdentity36ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity36FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity36Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity36ToFinite basisIdentity36FromFinite (by decide) (by decide)

def basisIdentity37ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity37FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity37Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity37ToFinite basisIdentity37FromFinite (by decide) (by decide)

def basisIdentity38ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity38FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity38Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨0, [2, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity38ToFinite basisIdentity38FromFinite (by decide) (by decide)

def basisIdentity39ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity39FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity39Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity39ToFinite basisIdentity39FromFinite (by decide) (by decide)

def basisIdentity40ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity40FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity40Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [2, 1, 0]⟩⟩ : Identity Nat)
    basisIdentity40ToFinite basisIdentity40FromFinite (by decide) (by decide)

def basisIdentity41ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity41FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity41Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨1, [0, 2, 0]⟩⟩ : Identity Nat)
    basisIdentity41ToFinite basisIdentity41FromFinite (by decide) (by decide)

def basisIdentity42ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity42FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity42Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨0, [1, 2, 0]⟩⟩ : Identity Nat)
    basisIdentity42ToFinite basisIdentity42FromFinite (by decide) (by decide)

def basisIdentity43ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity43FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity43Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨1, [1, 2, 0]⟩⟩ : Identity Nat)
    basisIdentity43ToFinite basisIdentity43FromFinite (by decide) (by decide)

def basisIdentity44ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity44FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity44Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 2, 0]⟩⟩ : Identity Nat)
    basisIdentity44ToFinite basisIdentity44FromFinite (by decide) (by decide)

def basisIdentity45ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity45FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity45Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨1, [2, 2, 0]⟩⟩ : Identity Nat)
    basisIdentity45ToFinite basisIdentity45FromFinite (by decide) (by decide)

def basisIdentity46ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity46FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity46Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity46ToFinite basisIdentity46FromFinite (by decide) (by decide)

def basisIdentity47ToFinite : Nat -> Fin 3
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨2, by decide⟩
  | _ => ⟨0, by decide⟩

def basisIdentity47FromFinite
    (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basisIdentity47Valid :
    (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat).SatisfiedBy table.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    table (⟨⟨2, [1, 0, 0]⟩, ⟨2, [1, 0, 1]⟩⟩ : Identity Nat)
    basisIdentity47ToFinite basisIdentity47FromFinite (by decide) (by decide)

theorem modelsLocal :
    Models table.semigroup
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
      ] := by
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
                                                              FiniteNilpotentCounterexample.models_cons basisIdentity29Valid <|
                                                                FiniteNilpotentCounterexample.models_cons basisIdentity30Valid <|
                                                                  FiniteNilpotentCounterexample.models_cons basisIdentity31Valid <|
                                                                    FiniteNilpotentCounterexample.models_cons basisIdentity32Valid <|
                                                                      FiniteNilpotentCounterexample.models_cons basisIdentity33Valid <|
                                                                        FiniteNilpotentCounterexample.models_cons basisIdentity34Valid <|
                                                                          FiniteNilpotentCounterexample.models_cons basisIdentity35Valid <|
                                                                            FiniteNilpotentCounterexample.models_cons basisIdentity36Valid <|
                                                                              FiniteNilpotentCounterexample.models_cons basisIdentity37Valid <|
                                                                                FiniteNilpotentCounterexample.models_cons basisIdentity38Valid <|
                                                                                  FiniteNilpotentCounterexample.models_cons basisIdentity39Valid <|
                                                                                    FiniteNilpotentCounterexample.models_cons basisIdentity40Valid <|
                                                                                      FiniteNilpotentCounterexample.models_cons basisIdentity41Valid <|
                                                                                        FiniteNilpotentCounterexample.models_cons basisIdentity42Valid <|
                                                                                          FiniteNilpotentCounterexample.models_cons basisIdentity43Valid <|
                                                                                            FiniteNilpotentCounterexample.models_cons basisIdentity44Valid <|
                                                                                              FiniteNilpotentCounterexample.models_cons basisIdentity45Valid <|
                                                                                                FiniteNilpotentCounterexample.models_cons basisIdentity46Valid <|
                                                                                                  FiniteNilpotentCounterexample.models_cons basisIdentity47Valid <|
                                                                                                    FiniteNilpotentCounterexample.models_nil table.semigroup

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff5.Signaturedfade03b3399.S6_2579ModelsPart01
