import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.S4_12

/-!
# L3 light root `S3_15 / S4_12`: oracle-first blocks

This is the first independently compilable layer for msg-0607, the accepted
`S3_15 × S4_12` design with displayed-basis SHA-256
`57ed8a83c4a38e3b5143dcd685c9a3d04eaa63443bed9041f659a20253ebed81`.

It deliberately contains no completeness lemma.  The structural canonicalizer
must first be checked against raw term-function vectors on the inclusive packet
windows `(r,L) = (2,8), (3,6), (4,5)`.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Exact displayed law system -/

/-- Msg-0607, `T(S3_15) ∩ T(S4_12)`, in the exact contract order. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0, 0]),
    Identity.mk (w 0 [0, 0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [1, 1, 1]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [0, 1])       (w 0 [0, 1, 1, 1]),
    Identity.mk (w 0 [0, 1])       (w 0 [1, 0]),
    Identity.mk (w 0 [1, 1])       (w 0 [1, 1, 1, 1]),
    Identity.mk (w 0 [1, 1, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2])       (w 0 [2, 1]) ]

theorem basis_length : basis.length = 10 := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basis_s3_15_models :
    Models SemigroupBasis.Generated.S3_15.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_15.table basis toFinThree (by decide)

set_option maxRecDepth 100000 in
theorem basis_s4_12_models :
    Models SemigroupBasis.Generated.S4_12.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_12.table basis toFinFour (by decide)

/-! ## Kernel-reducible head/support/parity renderer -/

def insertNatKernel (letter : Nat) : List Nat → List Nat
  | [] => [letter]
  | head :: tail =>
      if letter ≤ head then
        letter :: head :: tail
      else
        head :: insertNatKernel letter tail

def sortNatKernel : List Nat → List Nat
  | [] => []
  | head :: tail => insertNatKernel head (sortNatKernel tail)

def sortedSupportKernel (letters : List Nat) : List Nat :=
  sortNatKernel letters.eraseDups

/-- The least positive multiplicity with the source parity: one for odd and
two for even. -/
def paritySupportKernel (letters : List Nat) : List Nat :=
  (sortedSupportKernel letters).flatMap fun letter =>
    if letters.count letter % 2 = 0 then [letter, letter] else [letter]

/-- Add the lexicographically least parity-neutral pair exactly when the
minimal parity/support representative lies below the inclusive long boundary.
-/
def padToLongKernel (source minimal : List Nat) : List Nat :=
  if minimal.length < 3 then
    match sortedSupportKernel source with
    | [] => [0, 0, 0]
    | least :: _ => sortNatKernel (least :: least :: minimal)
  else
    minimal

def wordWithHeadKernel (head : Nat) (letters : List Nat) : Word Nat :=
  Word.mk head (sortNatKernel (letters.erase head))

/-- Raw-oracle renderer for `T(S3_15) ∩ T(S4_12)`.  Lengths one and two
remain literal.  At length at least three the two factor theories retain
exactly the head, support, and exponent-parity vector. -/
def canonicalize (word : Word Nat) : Word Nat :=
  match word.toList with
  | [_] => word
  | [_, _] => word
  | letters =>
      wordWithHeadKernel word.head <|
        padToLongKernel letters (paritySupportKernel letters)

end SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12
