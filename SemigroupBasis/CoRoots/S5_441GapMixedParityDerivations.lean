import SemigroupBasis.CoRoots.S5_441GapPowerDerivations

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

/-- Switch from an odd old-anchor profile to an even new-anchor profile
while retaining a nonempty filler:
`A A B B C A -> B A C B`.

The derivation first reorders the two adjacent squares, then uses an
extended envelope switch with `B B` as the old envelope, contracts the
resulting `B` power, and finally removes two leading copies of `B`.
Every multiplicity changes by an even amount. -/
theorem derivesOddEvenAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      (((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
        trailing) ++ oldAnchor)
      (((newAnchor ++ oldAnchor) ++ trailing) ++ newAnchor) := by
  have first :
      Derives basis
        (((((oldAnchor ++ oldAnchor) ++ newAnchor) ++ newAnchor) ++
          trailing) ++ oldAnchor)
        (((((oldAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor) ++
          trailing) ++ oldAnchor) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSquareFinalSwitch oldAnchor newAnchor)
        (trailing ++ oldAnchor)
  have second :
      Derives basis
        (((((oldAnchor ++ newAnchor) ++ newAnchor) ++ oldAnchor) ++
          trailing) ++ oldAnchor)
        (((((newAnchor ++ newAnchor) ++ (newAnchor ++ newAnchor)) ++
          oldAnchor) ++ trailing) ++ (newAnchor ++ newAnchor)) := by
    simpa [Word.append_assoc] using
      (derivesExtendedEnvelopeSwitch
        (newAnchor ++ newAnchor) oldAnchor trailing).symm
  have third :
      Derives basis
        (((((newAnchor ++ newAnchor) ++ (newAnchor ++ newAnchor)) ++
          oldAnchor) ++ trailing) ++ (newAnchor ++ newAnchor))
        ((((newAnchor ++ newAnchor) ++ newAnchor) ++
          (oldAnchor ++ trailing)) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      (derivesXYXToXXYXX newAnchor
        (((newAnchor ++ newAnchor) ++ oldAnchor) ++ trailing)).symm
  have fourth :
      Derives basis
        ((((newAnchor ++ newAnchor) ++ newAnchor) ++
          (oldAnchor ++ trailing)) ++ newAnchor)
        (((newAnchor ++ oldAnchor) ++ trailing) ++ newAnchor) := by
    simpa [Word.append_assoc] using
      (derivesLeftEnvelopePower
        newAnchor (oldAnchor ++ trailing)).symm
  exact first.trans <| second.trans <| third.trans fourth

/-- Reverse mixed-parity switch, obtained by exchanging the anchors and
reversing `derivesOddEvenAnchorSwitchWithTrailing`:
`A B C A -> B B A A C B`.
The filler remains a nonempty semigroup word. -/
theorem derivesEvenOddAnchorSwitchWithTrailing
    (oldAnchor newAnchor trailing : Word Nat) :
    Derives basis
      (((oldAnchor ++ newAnchor) ++ trailing) ++ oldAnchor)
      (((((newAnchor ++ newAnchor) ++ oldAnchor) ++ oldAnchor) ++
        trailing) ++ newAnchor) := by
  simpa [Word.append_assoc] using
    (derivesOddEvenAnchorSwitchWithTrailing
      newAnchor oldAnchor trailing).symm

/-- List-level form of the nonempty-filler odd/even anchor switch. -/
theorem listDerivesOddEvenAnchorSwitchWords
    (oldAnchor newAnchor trailing : Word Nat) :
    ListDerives
      (oldAnchor.toList ++ oldAnchor.toList ++ newAnchor.toList ++
        newAnchor.toList ++ trailing.toList ++ oldAnchor.toList)
      (newAnchor.toList ++ oldAnchor.toList ++ trailing.toList ++
        newAnchor.toList) := by
  simpa [Word.toList_append, List.append_assoc] using
    (ListDerives.ofWord
      (derivesOddEvenAnchorSwitchWithTrailing
        oldAnchor newAnchor trailing))

/-- Apply the nonempty-filler odd/even anchor switch inside arbitrary,
possibly empty, list contexts. -/
theorem listDerivesOddEvenAnchorSwitchContext
    (pre suffix : List Nat)
    (oldAnchor newAnchor trailing : Word Nat) :
    ListDerives
      (pre ++ oldAnchor.toList ++ oldAnchor.toList ++
        newAnchor.toList ++ newAnchor.toList ++ trailing.toList ++
        oldAnchor.toList ++ suffix)
      (pre ++ newAnchor.toList ++ oldAnchor.toList ++ trailing.toList ++
        newAnchor.toList ++ suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesOddEvenAnchorSwitchWords
        oldAnchor newAnchor trailing)

/-- List-level form of the nonempty-filler even/odd anchor switch. -/
theorem listDerivesEvenOddAnchorSwitchWords
    (oldAnchor newAnchor trailing : Word Nat) :
    ListDerives
      (oldAnchor.toList ++ newAnchor.toList ++ trailing.toList ++
        oldAnchor.toList)
      (newAnchor.toList ++ newAnchor.toList ++ oldAnchor.toList ++
        oldAnchor.toList ++ trailing.toList ++ newAnchor.toList) := by
  simpa [Word.toList_append, List.append_assoc] using
    (ListDerives.ofWord
      (derivesEvenOddAnchorSwitchWithTrailing
        oldAnchor newAnchor trailing))

/-- Apply the nonempty-filler even/odd anchor switch inside arbitrary,
possibly empty, list contexts. -/
theorem listDerivesEvenOddAnchorSwitchContext
    (pre suffix : List Nat)
    (oldAnchor newAnchor trailing : Word Nat) :
    ListDerives
      (pre ++ oldAnchor.toList ++ newAnchor.toList ++ trailing.toList ++
        oldAnchor.toList ++ suffix)
      (pre ++ newAnchor.toList ++ newAnchor.toList ++ oldAnchor.toList ++
        oldAnchor.toList ++ trailing.toList ++ newAnchor.toList ++
        suffix) := by
  simpa [List.append_assoc] using
    ListDerives.context pre suffix
      (listDerivesEvenOddAnchorSwitchWords
        oldAnchor newAnchor trailing)

end SemigroupBasis.CoRoots.S5_441
