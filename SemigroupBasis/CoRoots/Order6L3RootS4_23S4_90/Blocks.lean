import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S4_23
import SemigroupBasis.Generated.S4_90

/-!
# L3 light root `S4_23 / S4_90`: oracle-first blocks

This is the first independently compilable layer for msg-0633, the accepted
`S4_23 × S4_90` design with displayed-basis SHA-256
`75ad8ca18b2e8dc81f1bfbde2552605ff6e703c0b2909dbf38302e7e6984e1dc`.

It deliberately contains no completeness lemma.  The structural canonicalizer
must first be checked against raw term-function vectors on the inclusive packet
windows `(r,L) = (2,8), (3,6), (4,5)`.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Exact displayed law system -/

/-- Msg-0633, `T(S4_23) ∩ T(S4_90)`, in the exact contract order. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])          (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2])    (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1])    (w 0 [2, 1, 1]),
    Identity.mk (w 0 [2, 1, 3])    (w 0 [1, 2, 3]) ]

theorem basis_length : basis.length = 13 := by
  decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

set_option maxRecDepth 100000 in
theorem basis_s4_23_models :
    Models SemigroupBasis.Generated.S4_23.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_23.table basis toFinFour (by decide)

set_option maxRecDepth 100000 in
theorem basis_s4_90_models :
    Models SemigroupBasis.Generated.S4_90.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_90.table basis toFinFour (by decide)

/-! ## Kernel-reducible endpoint/capped-parity renderer -/

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

/-- The least multiplicity with the combined capped-count and parity state:
one for a singleton, two for repeated-even, and three for repeated-odd. -/
def cappedParityKernel (letters : List Nat) : List Nat :=
  (sortedSupportKernel letters).flatMap fun letter =>
    if letters.count letter = 1 then
      [letter]
    else if letters.count letter % 2 = 0 then
      [letter, letter]
    else
      [letter, letter, letter]

def lastNatKernel : List Nat → Nat
  | [] => 0
  | [letter] => letter
  | _ :: tail => lastNatKernel tail

/-- In the repeated-final stratum, deferring the greatest repeated letter to
the last position gives the length-then-lexicographically least word. -/
def greatestRepeatedKernel (source : List Nat) : Nat :=
  (sortedSupportKernel source).foldl
    (fun candidate letter =>
      if 2 ≤ source.count letter then letter else candidate)
    0

def renderEndpointsKernel
    (head final : Nat) (letters : List Nat) : Word Nat :=
  Word.mk head <|
    sortNatKernel ((letters.erase head).erase final) ++ [final]

/-- Raw-oracle renderer for `T(S4_23) ∩ T(S4_90)`.  The combined factor
theories retain the head, each letter's capped-count/parity state, and a fixed
final exactly when that final is simple. -/
def canonicalize (word : Word Nat) : Word Nat :=
  let source := word.toList
  let minimal := cappedParityKernel source
  match minimal with
  | [_] => word
  | _ =>
      let sourceFinal := lastNatKernel source
      let final :=
        if source.count sourceFinal = 1 then
          sourceFinal
        else
          greatestRepeatedKernel source
      renderEndpointsKernel word.head final minimal

end SemigroupBasis.CoRoots.Order6L3RootS4_23S4_90
