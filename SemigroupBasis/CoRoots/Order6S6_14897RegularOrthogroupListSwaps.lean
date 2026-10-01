import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupDisplayedSwaps
import SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroupListSyntax
import SemigroupBasis.Examples.AffineParityFourSyntax

namespace SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail

private theorem listPowerExpansion (letter : Nat) :
    ListDerives [letter] [letter, letter, letter] :=
  SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
    (derivesPowerExpansion (Word.singleton letter))

private theorem listPowerContraction (letter : Nat) :
    ListDerives [letter, letter, letter] [letter] :=
  SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
    (derivesPowerContraction (Word.singleton letter))

/-- Same-orientation displayed swap with four possibly empty list gaps.
Triple expansions supply two padding letters in every gap, so the word-level
kernel always receives nonempty substitutions. -/
theorem listDerivesDisplayedSwapSame
    (x y : Nat) (a b c d : List Nat) :
    ListDerives
      ([x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++ [x] ++ d ++ [y])
      ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++ [x] ++ d ++ [y]) := by
  have expandLeftX :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++ [x] ++ d ++ [y])
        ([x, x, x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++
          [x] ++ d ++ [y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([] : List Nat)
        (a ++ [y] ++ b ++ [x, y] ++ c ++ [x] ++ d ++ [y])
        (listPowerExpansion x)
  have expandLeftY :
      ListDerives
        ([x, x, x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++
          [x] ++ d ++ [y])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x] ++ d ++ [y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a)
        (b ++ [x, y] ++ c ++ [x] ++ d ++ [y])
        (listPowerExpansion y)
  have expandRightX :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x] ++ d ++ [y])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x, x, x] ++ d ++ [y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c)
        (d ++ [y])
        (listPowerExpansion x)
  have expandRightY :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x, x, x] ++ d ++ [y])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x, x, x] ++ d ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x, x, x] ++ d)
        ([] : List Nat)
        (listPowerExpansion y)
  let xWord := Word.singleton x
  let yWord := Word.singleton y
  let aWord := wordOfCons x (x :: a)
  let bWord := wordOfCons y (y :: b)
  let cWord := affineParityPrependLetters c (wordOfCons x [x])
  let dWord := affineParityPrependLetters d (wordOfCons y [y])
  have paddedSwap :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [x, x, x] ++ d ++ [y, y, y])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y]) := by
    have wordDerivation :=
      derivesDisplayedSwapSame
        xWord aWord yWord bWord cWord dWord
    have listDerivation :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        wordDerivation
    simpa [displayedSwapSameSource, displayedSwapSameTarget,
      xWord, yWord, aWord, bWord, cWord, dWord, wordOfCons,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      affineParityPrependLetters_toList,
      Word.toList_append, List.append_assoc] using listDerivation
  have contractLeftX :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y])
        ([x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([] : List Nat)
        (a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y])
        (listPowerContraction x)
  have contractLeftY :
      ListDerives
        ([x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a)
        (b ++ [y, x] ++ c ++ [x, x, x] ++ d ++ [y, y, y])
        (listPowerContraction y)
  have contractRightX :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [x, x, x] ++ d ++ [y, y, y])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [x] ++ d ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c)
        (d ++ [y, y, y])
        (listPowerContraction x)
  have contractRightY :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [x] ++ d ++ [y, y, y])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [x] ++ d ++ [y]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++ [x] ++ d)
        ([] : List Nat)
        (listPowerContraction y)
  exact expandLeftX.trans <|
    expandLeftY.trans <|
      expandRightX.trans <|
        expandRightY.trans <|
          paddedSwap.trans <|
            contractLeftX.trans <|
              contractLeftY.trans <|
                contractRightX.trans contractRightY

/-- Mixed-orientation displayed swap with arbitrary list gaps. -/
theorem listDerivesDisplayedSwapMixed
    (x y : Nat) (a b c d : List Nat) :
    ListDerives
      ([x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++ [y] ++ d ++ [x])
      ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++ [y] ++ d ++ [x]) := by
  have expandLeftX :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++ [y] ++ d ++ [x])
        ([x, x, x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++
          [y] ++ d ++ [x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([] : List Nat)
        (a ++ [y] ++ b ++ [x, y] ++ c ++ [y] ++ d ++ [x])
        (listPowerExpansion x)
  have expandLeftY :
      ListDerives
        ([x, x, x] ++ a ++ [y] ++ b ++ [x, y] ++ c ++
          [y] ++ d ++ [x])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y] ++ d ++ [x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a)
        (b ++ [x, y] ++ c ++ [y] ++ d ++ [x])
        (listPowerExpansion y)
  have expandRightY :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y] ++ d ++ [x])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y, y, y] ++ d ++ [x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c)
        (d ++ [x])
        (listPowerExpansion y)
  have expandRightX :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y, y, y] ++ d ++ [x])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y, y, y] ++ d ++ [x, x, x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y, y, y] ++ d)
        ([] : List Nat)
        (listPowerExpansion x)
  let xWord := Word.singleton x
  let yWord := Word.singleton y
  let aWord := wordOfCons x (x :: a)
  let bWord := wordOfCons y (y :: b)
  let cWord := affineParityPrependLetters c (wordOfCons y [y])
  let dWord := affineParityPrependLetters d (wordOfCons x [x])
  have paddedSwap :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [x, y] ++ c ++
          [y, y, y] ++ d ++ [x, x, x])
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x]) := by
    have wordDerivation :=
      derivesDisplayedSwapMixed
        xWord aWord yWord bWord cWord dWord
    have listDerivation :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        wordDerivation
    simpa [displayedSwapMixedSource, displayedSwapMixedTarget,
      xWord, yWord, aWord, bWord, cWord, dWord, wordOfCons,
      SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      affineParityPrependLetters_toList,
      Word.toList_append, List.append_assoc] using listDerivation
  have contractLeftX :
      ListDerives
        ([x, x, x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x])
        ([x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([] : List Nat)
        (a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x])
        (listPowerContraction x)
  have contractLeftY :
      ListDerives
        ([x] ++ a ++ [y, y, y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a)
        (b ++ [y, x] ++ c ++ [y, y, y] ++ d ++ [x, x, x])
        (listPowerContraction y)
  have contractRightY :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [y, y, y] ++ d ++ [x, x, x])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [y] ++ d ++ [x, x, x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c)
        (d ++ [x, x, x])
        (listPowerContraction y)
  have contractRightX :
      ListDerives
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [y] ++ d ++ [x, x, x])
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++
          [y] ++ d ++ [x]) := by
    simpa [List.append_assoc] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.context
        ([x] ++ a ++ [y] ++ b ++ [y, x] ++ c ++ [y] ++ d)
        ([] : List Nat)
        (listPowerContraction x)
  exact expandLeftX.trans <|
    expandLeftY.trans <|
      expandRightY.trans <|
        expandRightX.trans <|
          paddedSwap.trans <|
            contractLeftX.trans <|
              contractLeftY.trans <|
                contractRightY.trans contractRightX

end SemigroupBasis.CoRoots.Order6S6_14897RegularOrthogroup
