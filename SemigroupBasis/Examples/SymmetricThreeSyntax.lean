import SemigroupBasis.Equational

namespace SemigroupBasis.Examples

open SemigroupBasis

def symmetricThreeX : Word Nat := Word.singleton 0
def symmetricThreeY : Word Nat := Word.singleton 1
def symmetricThreeXXXXXX : Word Nat := ⟨0, [0, 0, 0, 0, 0]⟩
def symmetricThreeYYYYYY : Word Nat :=
  ⟨1, [1, 1, 1, 1, 1]⟩
def symmetricThreeXXXXXXX : Word Nat :=
  ⟨0, [0, 0, 0, 0, 0, 0]⟩
def symmetricThreeXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def symmetricThreeYYXX : Word Nat := ⟨1, [1, 0, 0]⟩

def symmetricThreeSeventhPowerLaw : Identity Nat :=
  ⟨symmetricThreeX, symmetricThreeXXXXXXX⟩

def symmetricThreeCommonSixthLaw : Identity Nat :=
  ⟨symmetricThreeXXXXXX, symmetricThreeYYYYYY⟩

def symmetricThreeSquareCommutationLaw : Identity Nat :=
  ⟨symmetricThreeXXYY, symmetricThreeYYXX⟩

/-- The exact positive-word basis
`x = x^7`, `x^6 = y^6`, `x^2 y^2 = y^2 x^2`. -/
def symmetricThreeBasis : List (Identity Nat) :=
  [symmetricThreeSeventhPowerLaw, symmetricThreeCommonSixthLaw,
    symmetricThreeSquareCommutationLaw]

/-- Two copies of a nonempty word. -/
def symmetricThreeSquare (word : Word Nat) : Word Nat :=
  word ++ word

/-- Five copies of a nonempty word, associated to the left. -/
def symmetricThreeFifthPower (word : Word Nat) : Word Nat :=
  ((((word ++ word) ++ word) ++ word) ++ word)

/-- Six copies of a nonempty word, associated to the left. -/
def symmetricThreeSixthPower (word : Word Nat) : Word Nat :=
  symmetricThreeFifthPower word ++ word

/-- Seven copies of a nonempty word, associated to the left. -/
def symmetricThreeSeventhPower (word : Word Nat) : Word Nat :=
  symmetricThreeSixthPower word ++ word

private def symmetricThreeInstantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- The first basis law after substituting an arbitrary nonempty block for
`x`. -/
theorem symmetricThreeDerivesExpandSeventh (word : Word Nat) :
    Derives symmetricThreeBasis word
      (symmetricThreeSeventhPower word) := by
  have base :
      Derives symmetricThreeBasis symmetricThreeX
        symmetricThreeXXXXXXX :=
    Derives.fromBasis (e := symmetricThreeSeventhPowerLaw) (by
      simp [symmetricThreeBasis])
  have substituted :=
    Derives.subst base
      (symmetricThreeInstantiateTwoWords word word)
  simpa [symmetricThreeX, symmetricThreeXXXXXXX,
    symmetricThreeSeventhPower, symmetricThreeSixthPower,
    symmetricThreeFifthPower, symmetricThreeInstantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The contracting orientation of `x = x^7` for an arbitrary nonempty
block. -/
theorem symmetricThreeDerivesContractSeventh (word : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeSeventhPower word) word :=
  Derives.symm (symmetricThreeDerivesExpandSeventh word)

/-- The second basis law after substituting arbitrary nonempty blocks for
`x` and `y`. -/
theorem symmetricThreeDerivesCommonSixth (u v : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeSixthPower u)
      (symmetricThreeSixthPower v) := by
  have base :
      Derives symmetricThreeBasis symmetricThreeXXXXXX
        symmetricThreeYYYYYY :=
    Derives.fromBasis (e := symmetricThreeCommonSixthLaw) (by
      simp [symmetricThreeBasis])
  have substituted :=
    Derives.subst base (symmetricThreeInstantiateTwoWords u v)
  simpa [symmetricThreeXXXXXX, symmetricThreeYYYYYY,
    symmetricThreeSixthPower, symmetricThreeFifthPower,
    symmetricThreeInstantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The third basis law after substituting arbitrary nonempty blocks for
`x` and `y`. -/
theorem symmetricThreeDerivesCommuteSquares (u v : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeSquare u ++ symmetricThreeSquare v)
      (symmetricThreeSquare v ++ symmetricThreeSquare u) := by
  have base :
      Derives symmetricThreeBasis symmetricThreeXXYY
        symmetricThreeYYXX :=
    Derives.fromBasis (e := symmetricThreeSquareCommutationLaw) (by
      simp [symmetricThreeBasis])
  have substituted :=
    Derives.subst base (symmetricThreeInstantiateTwoWords u v)
  simpa [symmetricThreeXXYY, symmetricThreeYYXX,
    symmetricThreeSquare, symmetricThreeInstantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.Examples
