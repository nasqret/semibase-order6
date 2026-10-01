import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

open SemigroupBasis

/-!
# D2 / D4 suffix-trace spine: exact Step-1 syntax

This module is the Lean statement of the frozen `D*` descriptor for the
shared `S6_6432` / `S6_6439` route, together with the exact displayed
31-law basis `B31`.  It intentionally contains no descriptor-preservation,
normalization, or completeness theorem.
-/

/-! ## Frozen Step-0 provenance -/

def routeID : String := "l6d-d2-d4-null-ideal-suffix-trace-v1"

def step0SourceCommit : String :=
  "03aefe317e9e455dee4ecb32b878f47545d26fd4"

def step0SourceTree : String :=
  "07693cc4b8a4a3d9872a0fc33f7f858865194d2b"

def descriptorRecordPath : String :=
  "l6d-work/s6_6432_6439-step0-dstar/source-repo/DSTAR.json"

def descriptorRecordSHA256 : String :=
  "98f11e0abfb090f6b1e223ed3f63b73702496f236d727b03f39475787f89622d"

def step0ReceiptManifestSHA256 : String :=
  "64190822b8ca3353e3d1bcd24afaf5647efceec19f6be9cdde07315298f223cc"

def displayedBasisSHA256 : String :=
  "37618e2e0e10e5a6f2ab51e3fce98a6b9ec521d309e9976b14c170a8d68a5f56"

def d2TableSemanticSHA256 : String :=
  "c8c892c2908c77c542799c8d8ec7e45849829aba7f16dc1e2ff21d1b41e4c31c"

def d4TableSemanticSHA256 : String :=
  "054bc23cbf44c6dd5ef7e28f4dc244888e83c2de91a51b47e4ae7a16fcaa4257"

/-! ## The frozen computable descriptor `D*` -/

/-- One suffix record for a globally simple letter. -/
structure SimpleLetterSuffixTrace where
  letter : Nat
  suffixContent : List Nat
  suffixFirstSimple : Option Nat
deriving Repr, DecidableEq

/-- The three fields of the immutable Step-0 descriptor, in frozen order. -/
structure Descriptor where
  content : List Nat
  firstSimple : Option Nat
  simpleLetterSuffixTraces : List SimpleLetterSuffixTrace
deriving Repr, DecidableEq

/-- Sorted support of a list, with every occurring letter represented once. -/
def sortedSupport (letters : List Nat) : List Nat :=
  letters.eraseDups.mergeSort (fun left right => decide (left ≤ right))

/-- The first letter exactly when it occurs once in the supplied list. -/
def firstSimple : List Nat → Option Nat
  | [] => none
  | first :: rest =>
      if (first :: rest).count first = 1 then some first else none

/-- The suffix strictly following the first occurrence of `selected`.
The descriptor calls this only for a globally simple, hence present, letter. -/
def suffixAfter (letters : List Nat) (selected : Nat) : List Nat :=
  match letters.dropWhile (fun current => current != selected) with
  | [] => []
  | _ :: suffix => suffix

/-- Globally simple letters in increasing order. -/
def simpleLetters (letters : List Nat) : List Nat :=
  (sortedSupport letters).filter fun letter =>
    decide (letters.count letter = 1)

/-- The frozen record attached to one globally simple letter. -/
def suffixTrace (letters : List Nat) (letter : Nat) :
    SimpleLetterSuffixTrace :=
  let suffix := suffixAfter letters letter
  { letter := letter
    suffixContent := sortedSupport suffix
    suffixFirstSimple := firstSimple suffix }

/-- The immutable compact null-ideal suffix-trace descriptor `D*`. -/
def descriptor (word : Word Nat) : Descriptor :=
  let letters := word.toList
  { content := sortedSupport letters
    firstSimple := firstSimple letters
    simpleLetterSuffixTraces :=
      (simpleLetters letters).map (suffixTrace letters) }

/-- Equality of the computable descriptor is the Step-1 shared-root relation. -/
def SameSuffixTrace (left right : Word Nat) : Prop :=
  descriptor left = descriptor right
end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace
