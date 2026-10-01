import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_18
import SemigroupBasis.Generated.S4_2
import SemigroupBasis.Generated.S4_9

/-!
# L3 light root `S3_18`: oracle-first blocks

This is the first independently compilable layer for the two accepted L3
design packets:

* msg-0630, `S3_18 × S4_2`, displayed-basis SHA-256
  `050baee64ddb1091ba7976dab7d4d469399b33ebc5a5b6f676244e072bbe9ee4`;
* msg-0631, `S3_18 × S4_9`, displayed-basis SHA-256
  `c6bf27538c221042737a9f33b188ef5a3210e633aa10ee6ebea011020fbd29b4`.

It deliberately contains no completeness lemma.  The two structural
canonicalizers must be checked first against raw term-function-vector oracles
on the inclusive packet windows `(r,L) = (2,8), (3,6), (4,5)`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Exact displayed law systems -/

/-- Msg-0630, `T(S3_18) ∩ T(S4_2)`, in the exact contract order. -/
def basisS4_2 : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])              (w 0 [0, 0, 0, 0]),
    Identity.mk (w 0 [0])              (w 1 [1, 1, 0, 0]),
    Identity.mk (w 0 [0])              (w 1 [1, 0, 1, 0]),
    Identity.mk (w 0 [0])              (w 1 [0, 1, 1, 0]),
    Identity.mk (w 0 [0])              (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [0])              (w 1 [1, 0, 0, 1]),
    Identity.mk (w 0 [0])              (w 1 [0, 1, 0, 1]),
    Identity.mk (w 0 [0])              (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [0])              (w 1 [0, 0, 1, 1]),
    Identity.mk (w 0 [0])              (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [0])              (w 0 [0, 1, 1, 1]),
    Identity.mk (w 0 [0, 0])           (w 1 [1, 1]),
    Identity.mk (w 1 [0, 0])           (w 0 [1, 0]),
    Identity.mk (w 1 [0, 0])           (w 0 [0, 1]),
    Identity.mk (w 2 [1, 0])           (w 1 [2, 0]),
    Identity.mk (w 2 [1, 0])           (w 2 [0, 1]),
    Identity.mk (w 0 [0, 0, 0, 1, 2]) (w 0 [1, 2]) ]

/-- Msg-0631, `T(S3_18) ∩ T(S4_9)`, in the exact contract order. -/
def basisS4_9 : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])          (w 1 [1, 1]),
    Identity.mk (w 3 [2, 1, 0, 0, 0]) (w 3 [2, 1]),
    Identity.mk (w 1 [0, 0])          (w 0 [1, 0]),
    Identity.mk (w 1 [0, 0])          (w 0 [0, 1]),
    Identity.mk (w 2 [1, 0])          (w 1 [2, 0]),
    Identity.mk (w 2 [1, 0])          (w 2 [0, 1]) ]

theorem basisS4_2_length : basisS4_2.length = 17 := by
  decide

theorem basisS4_9_length : basisS4_9.length = 6 := by
  decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basisS4_2_s3_18_models :
    Models SemigroupBasis.Generated.S3_18.table.semigroup basisS4_2 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_18.table basisS4_2 toFinFour (by decide)

theorem basisS4_2_s4_2_models :
    Models SemigroupBasis.Generated.S4_2.table.semigroup basisS4_2 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_2.table basisS4_2 toFinFour (by decide)

theorem basisS4_9_s3_18_models :
    Models SemigroupBasis.Generated.S3_18.table.semigroup basisS4_9 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_18.table basisS4_9 toFinFour (by decide)

theorem basisS4_9_s4_9_models :
    Models SemigroupBasis.Generated.S4_9.table.semigroup basisS4_9 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_9.table basisS4_9 toFinFour (by decide)

/-! ## Kernel-reducible mod-three renderers -/

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

def ternaryResidueKernel (letters : List Nat) : List Nat :=
  (sortedSupportKernel letters).flatMap fun letter =>
    match letters.count letter % 3 with
    | 0 => []
    | 1 => [letter]
    | _ => [letter, letter]

def wordOfListKernel : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => Word.mk head tail

def padToLongKernel (residue : List Nat) : List Nat :=
  sortNatKernel ([0, 0, 0] ++ residue)

def renderLongResidue (residue : List Nat) : Word Nat :=
  match residue with
  | first :: second :: third :: rest =>
      Word.mk first (second :: third :: rest)
  | _ => wordOfListKernel (padToLongKernel residue)

def renderBulkResidue (residue : List Nat) : Word Nat :=
  match residue with
  | [first, second] =>
      if first = second then
        Word.mk first [second]
      else
        wordOfListKernel (padToLongKernel residue)
  | first :: second :: third :: rest =>
      Word.mk first (second :: third :: rest)
  | _ => wordOfListKernel (padToLongKernel residue)

/-- Raw-oracle renderer for `T(S3_18) ∩ T(S4_9)`. -/
def canonicalizeS4_9 (word : Word Nat) : Word Nat :=
  match word.toList with
  | [_] => word
  | [_, _] => word
  | letters => renderLongResidue (ternaryResidueKernel letters)

/-- Raw-oracle renderer for `T(S3_18) ∩ T(S4_2)`. -/
def canonicalizeS4_2 (word : Word Nat) : Word Nat :=
  match word.toList with
  | [_] => word
  | [first, second] =>
      if first = second then
        renderBulkResidue (ternaryResidueKernel [first, second])
      else
        word
  | letters => renderBulkResidue (ternaryResidueKernel letters)

end SemigroupBasis.CoRoots.Order6L3RootS3_18
