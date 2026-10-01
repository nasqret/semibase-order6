import SemigroupBasis.FiniteCertificate

/-!
# Shared mechanical definitions for order-six L1R rank-1 co-roots

This module contains only the small data constructors used by the twelve
fingerprint-local Stage-1 basis modules.  It contains no canonicalization or
completeness claim.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1

open SemigroupBasis

/-!
Each basis module uses the packet verifier's per-law normalization: the
letters occurring in one displayed identity are sorted lexicographically and
then numbered from zero.  Thus the stored `Nat` identity is alpha-equivalent
to, and mechanically recoverable from, the exact displayed spelling.
-/

/-- Package a nonempty list of natural-variable names as a word.  The empty
case is a totality fallback and is not used by any displayed basis below. -/
def basisWordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => Word.mk head tail

/-- Package two nonempty letter lists as a natural-variable identity. -/
def law (left right : List Nat) : Identity Nat :=
  Identity.mk (basisWordOfList left) (basisWordOfList right)

/-- The round-trip map used by bases involving at most three variables. -/
def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The round-trip map used by bases involving at most four variables. -/
def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

end SemigroupBasis.CoRoots.Order6L1RRank1
