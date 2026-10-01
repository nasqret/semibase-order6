import SemigroupBasis.CoRoots.Order6L1RRank1.CanonicalSearch
import SemigroupBasis.Generated.BandEmbeddingTransfers
import SemigroupBasis.Generated.S4_64

/-!
# L1R fingerprint 43fb00e0b3bdd469 structural canonicalizer

Stage 1 for accepted packet `msg-0603-43fb00e0b3bdd469-design`, the
`S4_116op x S4_64` intersection covering `S6_12185`, `S6_12324`,
`S6_12392`, `S6_12462`, `S6_12492`, `S6_14080`, `S6_14222`, and
`S6_14223`.

The opposite of the `S4_116` left regular band is recorded by the
last-occurrence sequence.  The `S4_64` component uses its exported
open-or-closed first-occurrence normal form.  The common reducible search
selects the shortlex-first word with the resulting joint signature.

This file makes no completeness claim.  Its oracle comparison and Lean
elaboration are pending on Helios.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L1RRank1

/-- Keep precisely the last occurrence of every variable.  This is the
structural normal form of the right regular band `S4_116op`. -/
@[reducible] def lastOccurrenceSequence : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then
        lastOccurrenceSequence rest
      else
        letter :: lastOccurrenceSequence rest

/-- Apply the exported `S4_64` open-or-closed normal form to a whole word.
The singleton branch is already normal.  In the non-singleton branch, the
prefix is reduced to first-occurrence order and the original final letter
decides whether the result is open or closed. -/
@[reducible] def s4_64Normal (word : Word Nat) : Word Nat :=
  wordOfList (reducibleS4_64NormalList word)

structure JointSignature where
  support : List Nat
  lastOrder : List Nat
  factorNormal : List Nat
deriving DecidableEq, Repr

@[reducible] def jointSignature (word : Word Nat) : JointSignature :=
  let letters := word.toList
  { support := sortedSupport letters
    lastOrder := lastOccurrenceSequence letters
    factorNormal := (s4_64Normal word).toList }

@[reducible] def canonicalize (word : Word Nat) : Word Nat :=
  canonicalizeBySignature
    jointSignature JointSignature.support word

theorem canonicalize_eq_of_signature_eq
    {left right : Word Nat}
    (same : jointSignature left = jointSignature right) :
    canonicalize left = canonicalize right :=
  canonicalizeBySignature_eq_of_signature_eq
    jointSignature JointSignature.support same

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
