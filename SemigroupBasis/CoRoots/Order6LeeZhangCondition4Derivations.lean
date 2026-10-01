import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Lee--Zhang Condition 4: derivational kernel

This module records the three Condition-4 identities

* `xx = xxx`,
* `xxy = xyx`, and
* `xyzu = xyuz`,

and derives their block-general consequences.  The key consequence is that,
every adjacent transposition after two nonempty prefix blocks is available.
This is the shared syntactic kernel for the corrected Condition-4 normal form.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition4

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyzu : Word Nat := w 0 [1, 2, 3]
def xyuz : Word Nat := w 0 [1, 3, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def repeatedFirstLaw : Identity Nat := ⟨xxy, xyx⟩
def tailSwapLaw : Identity Nat := ⟨xyzu, xyuz⟩

/-- Lee--Zhang Condition 4 in its direct canonical orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, repeatedFirstLaw, tailSwapLaw]

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisRepeatedFirst : Derives basis xxy xyx :=
  Derives.fromBasis (e := repeatedFirstLaw) (by simp [basis])

private theorem basisTailSwap : Derives basis xyzu xyuz :=
  Derives.fromBasis (e := tailSwapLaw) (by simp [basis])

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

/-- The power law under an arbitrary nonempty word substitution. -/
theorem derivesTripleExpansion (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have substituted :=
    Derives.subst basisPower
      (instantiateFourWords block block block block)
  simpa [powerLaw, xx, xxx, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The reverse orientation of the arbitrary power-law instance. -/
theorem derivesTripleContraction (block : Word Nat) :
    Derives basis ((block ++ block) ++ block) (block ++ block) :=
  (derivesTripleExpansion block).symm

/-- Move the second copy of a repeated block across one nonempty block. -/
theorem derivesRepeatedFirstMove (block payload : Word Nat) :
    Derives basis ((block ++ block) ++ payload)
      ((block ++ payload) ++ block) := by
  have substituted :=
    Derives.subst basisRepeatedFirst
      (instantiateFourWords block payload payload payload)
  simpa [repeatedFirstLaw, xxy, xyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap two adjacent nonempty blocks after two nonempty prefix blocks. -/
theorem derivesTailSwap
    (first second left right : Word Nat) :
    Derives basis (((first ++ second) ++ left) ++ right)
      (((first ++ second) ++ right) ++ left) := by
  have substituted :=
    Derives.subst basisTailSwap
      (instantiateFourWords first second left right)
  simpa [tailSwapLaw, xyzu, xyuz, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def listWord (head : Nat) (tail : List Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail

/-- Swap adjacent letters anywhere after two protected initial letters. -/
theorem listDerivesAdjacentSwapAfterTwo
    (first second : Nat) (context : List Nat)
    (left right : Nat) (suffix : List Nat) :
    ListDerives
      ([first, second] ++ context ++ left :: right :: suffix)
      ([first, second] ++ context ++ right :: left :: suffix) := by
  let firstWord := Word.singleton first
  let secondPrefix := listWord second context
  let leftWord := Word.singleton left
  let rightWord := Word.singleton right
  have swapped :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesTailSwap firstWord secondPrefix leftWord rightWord)
  simpa [firstWord, secondPrefix, leftWord, rightWord, listWord,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons, Word.singleton,
    Word.toList_append, List.append_assoc] using
      swapped.append suffix

/-- Every permutation of the suffix after two protected initial letters is
derivable. -/
theorem listDerivesTailPermutationAfterTwo
    (first second : Nat) {source target : List Nat}
    (permutation : source.Perm target) :
    ∀ (context suffix : List Nat),
      ListDerives
        ([first, second] ++ context ++ source ++ suffix)
        ([first, second] ++ context ++ target ++ suffix) := by
  induction permutation with
  | nil =>
      intro context suffix
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | @cons letter source target permutation inductionHypothesis =>
      intro context suffix
      simpa [List.append_assoc] using
        inductionHypothesis (context ++ [letter]) suffix
  | swap left right rest =>
      intro context suffix
      simpa [List.append_assoc] using
        (listDerivesAdjacentSwapAfterTwo first second context
          left right (rest ++ suffix)).symm
  | @trans source middle target firstPermutation secondPermutation firstIH secondIH =>
      intro context suffix
      exact
        (firstIH context suffix).trans
          (secondIH context suffix)

/-- Swap adjacent letters anywhere after a repeated singleton marker. -/
theorem listDerivesSquareAdjacentSwap
    (marker : Nat) (context : List Nat)
    (left right : Nat) (suffix : List Nat) :
    ListDerives
      ([marker, marker] ++ context ++ left :: right :: suffix)
      ([marker, marker] ++ context ++ right :: left :: suffix) :=
  listDerivesAdjacentSwapAfterTwo marker marker context left right suffix

/-- Every permutation of the suffix following a repeated singleton marker is
derivable.  `context` and `suffix` expose the contextual form needed by the
normalization recursion. -/
theorem listDerivesSquareTailPermutation
    (marker : Nat) {source target : List Nat}
    (permutation : source.Perm target) :
    ∀ (context suffix : List Nat),
      ListDerives
        ([marker, marker] ++ context ++ source ++ suffix)
        ([marker, marker] ++ context ++ target ++ suffix) :=
  listDerivesTailPermutationAfterTwo marker marker permutation

end SemigroupBasis.CoRoots.Order6LeeZhangCondition4
