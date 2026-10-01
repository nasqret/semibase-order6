import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS4_11
import SemigroupBasis.CoRoots.S5_379Completeness
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Exact S3_16 × S5_379 system, workload rank 105

The displayed nine laws have SHA-256
`6d1cd71b01911e51c11448623747ad00be21a88eaea2ced1961fafb3fc4dbc5b`.
The current pinned fanout is S6_7954, S6_7984, S6_8134, S6_8140,
S6_11028 and S6_11086. This module supplies exact factor soundness and
necessary invariants only, not the missing unrestricted joint proof.

Per msg-0389, reuse the complete factor proofs and their actual signatures.
The S5_379 factor has connected-component/simple-letter semantics; adding
S3_16 fixes the full first-occurrence order. Arbitrary interior permutation
from the lower proof cannot be transported into this presentation.
The new pre-proof screen is bounded evidence, never a Derives premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105

open SemigroupBasis
open SemigroupBasis.Examples

abbrev leftTable : FiniteTable := Generated.Catalogue.S3_16.table
abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.S5_379.table

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 2, 0, 1]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08]

def displayedBasisSHA256 : String :=
  "6d1cd71b01911e51c11448623747ad00be21a88eaea2ced1961fafb3fc4dbc5b"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

structure SameSignature (left right : Word Nat) : Prop where
  firstOrder : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList
  componentSimple : SemigroupBasis.CoRoots.S5_379.SameComponentSimpleSignature left right

theorem sameSignature_of_factorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  exact ⟨Rank018.Seed.firstOccurrences_of_leftValid identity leftValid,
    SemigroupBasis.CoRoots.S5_379.valid_sameSignature identity rightValid⟩

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-- Actual derivations preserve the independently detected first order. -/
theorem listDerives_firstOrder {left right : List Nat} (derivation : ListDerives left right) :
    firstOccurrenceSequence left = firstOccurrenceSequence right := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail proof =>
      exact Rank018.Seed.firstOccurrences_of_leftValid
        (Identity.mk (SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftTail)
          (SemigroupBasis.CoRoots.S5_107.listWordOfCons rightHead rightTail))
        (fun valuation => proof.sound leftModels valuation)

/-- Multiplicity is capped at two by the actual lower factor, not by a
syntactic stamp on the proposed normal form. -/
theorem listDerives_cappedCounts {left right : List Nat} (derivation : ListDerives left right)
    (tested : Nat) : min (left.count tested) 2 = min (right.count tested) 2 := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail proof =>
      exact SemigroupBasis.CoRoots.S5_379.cappedCounts_eq_of_sameComponentSimpleSignature
        (SemigroupBasis.CoRoots.S5_379.valid_sameSignature
          (Identity.mk (SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftTail)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons rightHead rightTail))
          (fun valuation => proof.sound rightModels valuation)) tested

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105
