import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_4
import SemigroupBasis.Generated.S4_21
import SemigroupBasis.Generated.S4_60
import SemigroupBasis.Nonfinite.GraphParity

/-!
# Rank-3 light-root blocks

This is the first independently compilable layer for the two accepted L3
design packets:

* msg-0601, `S3_4 × S4_21`, displayed-basis SHA-256
  `3bd5dbab65160131b15a4c55ca28e13ae71e7182195291e7c90b4438b2dbe1e6`;
* msg-0619, `S3_4 × S4_60`, displayed-basis SHA-256
  `8d267159b21b52170c6b9dc4487eb22e438e3af5ad395486752db0dfa451d6bf`.

It deliberately contains no completeness lemma.  The structural
canonicalizers below were cross-validated first against the raw packet
term-function-vector oracle on all 5,932 words in the inclusive windows
`(r,L) = (2,8), (3,6), (4,5)`.  The companion oracle module contains 1,024
generated `decide` cases, including 606 cases on the exact upper boundaries.
-/

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## The two accepted displayed law systems -/

def basis21 : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])    (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 0])    (w 1 [0, 0]),
    Identity.mk (w 0 [1, 2])    (w 1 [0, 2]) ]

def basis60 : List (Identity Nat) :=
  [ Identity.mk (w 0 [0, 0])       (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1])    (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2])    (w 0 [1, 2]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 2])    (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2, 0])    (w 0 [2, 1, 0]) ]

theorem basis21_length : basis21.length = 6 := by
  decide

theorem basis60_length : basis60.length = 7 := by
  decide

/-! ## Shared finite-table soundness -/

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis21_s3_4_models :
    Models SemigroupBasis.Generated.S3_4.table.semigroup basis21 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_4.table basis21 toFinThree (by decide)

theorem basis21_s4_21_models :
    Models SemigroupBasis.Generated.S4_21.table.semigroup basis21 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_21.table basis21 toFinThree (by decide)

theorem basis60_s3_4_models :
    Models SemigroupBasis.Generated.S3_4.table.semigroup basis60 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_4.table basis60 toFinThree (by decide)

theorem basis60_s4_60_models :
    Models SemigroupBasis.Generated.S4_60.table.semigroup basis60 :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_60.table basis60 toFinThree (by decide)

/-! ## Computable structural signatures -/

private def insertNat (letter : Nat) : List Nat → List Nat
  | [] => [letter]
  | head :: tail =>
      if letter ≤ head then
        letter :: head :: tail
      else
        head :: insertNat letter tail

/-- A kernel-reducible sort for the bounded signature oracle.  Using
`List.mergeSort` here made the generated `decide` audit depend on the native
implementation boundary rather than producing a kernel proof. -/
def sortNat : List Nat → List Nat
  | [] => []
  | head :: tail => insertNat head (sortNat tail)

def sortedSupport (letters : List Nat) : List Nat :=
  sortNat letters.eraseDups

def cappedContent (letters : List Nat) : List Nat :=
  (sortedSupport letters).flatMap fun letter =>
    List.replicate (min (letters.count letter) 2) letter

def repeatedSupport (letters : List Nat) : List Nat :=
  (sortedSupport letters).filter fun letter =>
    decide (2 ≤ letters.count letter)

inductive S3_4Signature where
  | singleton (letter : Nat)
  | quadratic (support : List Nat)
  | long
deriving DecidableEq, Repr

def s3_4Signature (word : Word Nat) : S3_4Signature :=
  match word.tail with
  | [] => S3_4Signature.singleton word.head
  | [last] =>
      S3_4Signature.quadratic
        (sortedSupport [word.head, last])
  | _ :: _ :: _ => S3_4Signature.long

structure S4_21Signature where
  content : List Nat
  marker : Nat
deriving DecidableEq, Repr

def s4_21Signature (word : Word Nat) : S4_21Signature :=
  let letters := word.toList
  let final := word.tail.getLastD word.head
  let marker :=
    if letters.count final = 1 then
      final
    else
      (repeatedSupport letters).getLastD final
  ⟨cappedContent letters, marker⟩

inductive S4_60Signature where
  | singleton (letter : Nat)
  | product
      (first : Nat)
      (prefixSupport : List Nat)
      (simpleFinal : Option Nat)
deriving DecidableEq, Repr

def s4_60Signature (word : Word Nat) : S4_60Signature :=
  match word.tail with
  | [] => S4_60Signature.singleton word.head
  | _ :: _ =>
      let prefixSupport := sortedSupport word.toList.dropLast
      let final := word.tail.getLastD word.head
      let simpleFinal :=
        if final ∈ prefixSupport then none else some final
      S4_60Signature.product word.head prefixSupport simpleFinal

abbrev JointSignature21 :=
  S3_4Signature × S4_21Signature

abbrev JointSignature60 :=
  S3_4Signature × S4_60Signature

def jointSignature21 (word : Word Nat) : JointSignature21 :=
  (s3_4Signature word, s4_21Signature word)

def jointSignature60 (word : Word Nat) : JointSignature60 :=
  (s3_4Signature word, s4_60Signature word)

/-! ## Oracle-matched canonical renderers -/

def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => Word.mk head tail

private def protectLongList : S3_4Signature → List Nat → List Nat
  | S3_4Signature.long, [first, final] => [first, first, final]
  | _, letters => letters

def render21 (signature : JointSignature21) : Word Nat :=
  let factor := signature.2
  let letters := factor.content.erase factor.marker ++ [factor.marker]
  wordOfList (protectLongList signature.1 letters)

def render60Factor : S4_60Signature → List Nat
  | S4_60Signature.singleton letter => [letter]
  | S4_60Signature.product first prefixSupport simpleFinal =>
      let marker := simpleFinal.getD (prefixSupport.headD first)
      first :: prefixSupport.erase first ++ [marker]

def render60 (signature : JointSignature60) : Word Nat :=
  wordOfList
    (protectLongList signature.1 (render60Factor signature.2))

def canonicalize21 (word : Word Nat) : Word Nat :=
  render21 (jointSignature21 word)

def canonicalize60 (word : Word Nat) : Word Nat :=
  render60 (jointSignature60 word)

theorem canonicalize21_eq_of_signature_eq
    {left right : Word Nat}
    (same : jointSignature21 left = jointSignature21 right) :
    canonicalize21 left = canonicalize21 right := by
  simp only [canonicalize21, same]

theorem canonicalize60_eq_of_signature_eq
    {left right : Word Nat}
    (same : jointSignature60 left = jointSignature60 right) :
    canonicalize60 left = canonicalize60 right := by
  simp only [canonicalize60, same]

end SemigroupBasis.CoRoots.Order6L3Root3
