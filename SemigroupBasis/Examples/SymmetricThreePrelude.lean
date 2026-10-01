import SemigroupBasis.Examples.SymmetricThreeSyntax

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Any sixth-power representative is a left identity on every nonempty
word. -/
theorem symmetricThreeDerivesSixthLeftIdentity
    (representative word : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeSixthPower representative ++ word) word := by
  have replaceRepresentative :=
    Derives.appendRight
      (symmetricThreeDerivesCommonSixth representative word) word
  exact Derives.trans replaceRepresentative
    (symmetricThreeDerivesContractSeventh word)

/-- Any sixth-power representative is a right identity on every nonempty
word. -/
theorem symmetricThreeDerivesSixthRightIdentity
    (representative word : Word Nat) :
    Derives symmetricThreeBasis
      (word ++ symmetricThreeSixthPower representative) word := by
  have replaceRepresentative :=
    Derives.prepend word
      (symmetricThreeDerivesCommonSixth representative word)
  have contract :
      Derives symmetricThreeBasis
        (word ++ symmetricThreeSixthPower word) word := by
    simpa [symmetricThreeSeventhPower, symmetricThreeSixthPower,
      symmetricThreeFifthPower, Word.append_assoc] using
        symmetricThreeDerivesContractSeventh word
  exact Derives.trans replaceRepresentative contract

/-- Insert an arbitrary sixth-power representative on the left. -/
theorem symmetricThreeDerivesInsertSixthLeft
    (representative word : Word Nat) :
    Derives symmetricThreeBasis word
      (symmetricThreeSixthPower representative ++ word) :=
  Derives.symm
    (symmetricThreeDerivesSixthLeftIdentity representative word)

/-- Insert an arbitrary sixth-power representative on the right. -/
theorem symmetricThreeDerivesInsertSixthRight
    (representative word : Word Nat) :
    Derives symmetricThreeBasis word
      (word ++ symmetricThreeSixthPower representative) :=
  Derives.symm
    (symmetricThreeDerivesSixthRightIdentity representative word)

/-- The fifth power of `word` is a left inverse relative to any chosen
sixth-power representative. -/
theorem symmetricThreeDerivesFifthPowerLeftInverse
    (representative word : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeFifthPower word ++ word)
      (symmetricThreeSixthPower representative) := by
  exact symmetricThreeDerivesCommonSixth word representative

/-- The fifth power of `word` is a right inverse relative to any chosen
sixth-power representative. -/
theorem symmetricThreeDerivesFifthPowerRightInverse
    (representative word : Word Nat) :
    Derives symmetricThreeBasis
      (word ++ symmetricThreeFifthPower word)
      (symmetricThreeSixthPower representative) := by
  simpa [symmetricThreeSixthPower, symmetricThreeFifthPower,
    Word.append_assoc] using
      symmetricThreeDerivesCommonSixth word representative

/-- A fifth power followed by its word cancels from the left of any nonempty
suffix. -/
theorem symmetricThreeDerivesCancelFifthPowerLeft
    (word suffix : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeFifthPower word ++ (word ++ suffix)) suffix := by
  have cancelToIdentity :=
    Derives.appendRight
      (symmetricThreeDerivesFifthPowerLeftInverse suffix word) suffix
  have removeIdentity :=
    symmetricThreeDerivesSixthLeftIdentity suffix suffix
  exact Derives.trans
    (by
      simpa [Word.append_assoc] using cancelToIdentity)
    removeIdentity

/-- A word followed by its fifth power cancels from the right of any
nonempty prefix. -/
theorem symmetricThreeDerivesCancelFifthPowerRight
    (leftContext word : Word Nat) :
    Derives symmetricThreeBasis
      ((leftContext ++ word) ++ symmetricThreeFifthPower word)
      leftContext := by
  have cancelToIdentity :=
    Derives.prepend leftContext
      (symmetricThreeDerivesFifthPowerRightInverse leftContext word)
  have removeIdentity :=
    symmetricThreeDerivesSixthRightIdentity leftContext leftContext
  exact Derives.trans
    (by
      simpa [Word.append_assoc] using cancelToIdentity)
    removeIdentity

end SemigroupBasis.Examples
