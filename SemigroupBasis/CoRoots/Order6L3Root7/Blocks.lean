import SemigroupBasis.CoRoots.Order6L3Root3.Blocks
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S4_110

/-!
# L3 rank-7 light root: `S2_2 × S4_110`

This is the oracle-first layer for msg-0600, displayed-basis SHA-256
`96a614db6d8587e5b5e776046980e2055a898088c29245e2204b7d85aa4798ac`.
It contains the exact 15 displayed laws, finite-table soundness, and the
structural `(first, content, final, oddSupport)` canonicalizer.

There is deliberately no completeness lemma in this layer.  The canonicalizer
was cross-validated first against complete raw term-function vectors throughout
the inclusive packet windows `(r,L) = (2,8), (3,6), (4,5)`.
-/

namespace SemigroupBasis.CoRoots.Order6L3Root7

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L3Root3

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Exact displayed law system -/

def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [])          (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1])     (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [0, 1])     (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [0, 1, 0])  (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 0, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [0, 1, 1])  (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2])  (w 0 [1, 0, 2]),
    Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 0, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2])     (w 0 [2, 1, 2, 2]),
    Identity.mk (w 0 [1, 2])     (w 0 [2, 2, 1, 2]),
    Identity.mk (w 0 [1, 2, 0])  (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1])  (w 0 [2, 1, 1]) ]

theorem basis_length : basis.length = 15 := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_s2_2_models :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table basis toFinThree (by decide)

theorem basis_s4_110_models :
    Models SemigroupBasis.Generated.S4_110.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_110.table basis toFinThree (by decide)

/-! ## FCLP signature and the oracle-matched renderer -/

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

def oddSupport (letters : List Nat) : List Nat :=
  (sortedSupportKernel letters).filter fun letter =>
    decide (letters.count letter % 2 = 1)

structure FCLPSignature where
  first : Nat
  content : List Nat
  final : Nat
  oddSupport : List Nat
deriving DecidableEq, Repr

def signature (word : Word Nat) : FCLPSignature :=
  let letters := word.toList
  ⟨word.head, sortedSupportKernel letters, word.final, oddSupport letters⟩

def endpointSkeleton (value : FCLPSignature) : List Nat :=
  if value.first = value.final then
    if value.content = [value.first] then
      [value.first]
    else
      value.first :: (value.content.erase value.first ++ [value.first])
  else
    value.first ::
      ((value.content.erase value.first).erase value.final ++ [value.final])

def parityCorrection
    (value : FCLPSignature) (skeleton : List Nat) : List Nat :=
  let skeletonOdd := oddSupport skeleton
  value.content.filter fun letter =>
    decide (
      (letter ∈ value.oddSupport ∧ letter ∉ skeletonOdd) ∨
      (letter ∉ value.oddSupport ∧ letter ∈ skeletonOdd))

def render (value : FCLPSignature) : Word Nat :=
  let skeleton := endpointSkeleton value
  let correction := parityCorrection value skeleton
  match skeleton with
  | [] => Word.singleton value.first
  | only :: [] => wordOfList (only :: correction)
  | first :: second :: rest =>
      let tail := second :: rest
      wordOfList
        (first ::
          (sortNatKernel (tail.dropLast ++ correction) ++
            [tail.getLastD second]))

def canonicalize (word : Word Nat) : Word Nat :=
  render (signature word)

theorem canonicalize_eq_of_signature_eq
    {left right : Word Nat}
    (same : signature left = signature right) :
    canonicalize left = canonicalize right := by
  simp only [canonicalize, same]

end SemigroupBasis.CoRoots.Order6L3Root7
