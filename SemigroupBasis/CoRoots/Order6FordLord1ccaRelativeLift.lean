import SemigroupBasis.CoRoots.S5_788
import SemigroupBasis.CoRoots.Order6FordLord1ccaNormal

/-!
Final-relative lift of the twenty-four `S5_788` basis laws to the displayed
Ford--Lord `1cca` basis.

The suffix is a `Word`, hence is nonempty.  The proof is entirely symbolic:
one reusable route sends `XYZX F` to `X²Y²Z² F`, and the remaining cases are
finite compositions of the fourteen word-block laws from
`Order6FordLord1ccaNormal`.

This module is source-staged.  It has not yet been elaborated or kernel-checked.
-/

namespace SemigroupBasis.CoRoots.Order6FordLord1cca

open SemigroupBasis

/-! ## Generic word-block routes -/

/-- The common squared endpoint used by the longer `XYZX F` cases. -/
theorem derivesXYZXRelativeSquares
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
  have unfoldReturn :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix) := by
    simpa only [Word.append_assoc] using
      ((derivesPromotion x (y ++ z) suffix).symm)
  have zipSquares :
      Derives basis
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix)
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend (x ++ x)
        (Derives.appendRight (derivesSquareInterleave y z).symm suffix))
  exact unfoldReturn.trans zipSquares

theorem derivesS5PowerRelativeBlocks
    (x suffix : Word Nat) :
    Derives basis
      ((x ++ x) ++ suffix)
      (((x ++ x) ++ x) ++ suffix) := by
  simpa only [Word.append_assoc] using
    Derives.appendRight (derivesPower x) suffix

theorem derivesS5LeftDuplicationRelativeBlocks
    (x y suffix : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ suffix)
      ((((x ++ x) ++ y) ++ x) ++ suffix) := by
  simpa only [Word.append_assoc] using
    Derives.appendRight (derivesLeftCollapse x y).symm suffix

theorem derivesS5SquaresRelativeBlocks
    (x y suffix : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ suffix)
      (((x ++ x) ++ (y ++ y)) ++ suffix) := by
  simpa only [Word.append_assoc] using
    (derivesPromotion x y suffix).symm

theorem derivesS5IntervalExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ suffix)
      (((((((x ++ y) ++ x) ++ y) ++ y) ++ x) ++ z) ++ suffix) := by
  have sandwich :
      Derives basis
        ((((x ++ y) ++ x) ++ z) ++ suffix)
        ((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesSandwichDuplication x y) (z ++ suffix)
  have duplicateMiddle :
      Derives basis
        ((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ suffix)
        (((((((x ++ y) ++ x) ++ y) ++ y) ++ x) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend (x ++ y)
        (Derives.appendRight (derivesMiddleDuplication x y)
          (z ++ suffix)))
  exact sandwich.trans duplicateMiddle

theorem derivesS5RightXExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      (((((x ++ y) ++ z) ++ x) ++ x) ++ suffix) := by
  simpa only [Word.append_assoc] using
    Derives.appendRight (derivesRightDuplication x (y ++ z)) suffix

theorem derivesS5RightZExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      (((((x ++ y) ++ z) ++ x) ++ z) ++ suffix) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix) := by
    simpa only [Word.append_assoc] using
      ((derivesPromotion x (y ++ z) suffix).symm)
  have step2 :
      Derives basis
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix)
        (((x ++ x) ++ (((y ++ z) ++ y) ++ (z ++ z))) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend ((x ++ x) ++ y)
        (Derives.appendRight (derivesRightDuplication z y) suffix))
  have step3 :
      Derives basis
        (((x ++ x) ++ (((y ++ z) ++ y) ++ (z ++ z))) ++ suffix)
        (((((x ++ y) ++ z) ++ x) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesPromotion x (y ++ z) z) suffix
  exact step1.trans (step2.trans step3)

theorem derivesS5SeparatorExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      (((((((x ++ x) ++ y) ++ z) ++ y) ++ y) ++ z) ++ suffix) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix) := by
    simpa only [Word.append_assoc] using
      ((derivesPromotion x (y ++ z) suffix).symm)
  have step2 :
      Derives basis
        (((x ++ x) ++ ((y ++ z) ++ (y ++ z))) ++ suffix)
        (((((((x ++ x) ++ y) ++ z) ++ y) ++ y) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend (x ++ x)
        (Derives.appendRight (derivesRightDuplication y z)
          (z ++ suffix)))
  exact step1.trans step2

theorem derivesS5LeftNestedExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      (((((((x ++ y) ++ x) ++ x) ++ y) ++ z) ++ y) ++ suffix) := by
  have targetToSquares :
      Derives basis
        (((((((x ++ y) ++ x) ++ x) ++ y) ++ z) ++ y) ++ suffix)
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    have step1 :
        Derives basis
          (((((((x ++ y) ++ x) ++ x) ++ y) ++ z) ++ y) ++ suffix)
          ((((((x ++ y) ++ x) ++ y) ++ z) ++ y) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesRightDuplication x y).symm
          (((y ++ z) ++ y) ++ suffix)
    have step2 :
        Derives basis
          ((((((x ++ y) ++ x) ++ y) ++ z) ++ y) ++ suffix)
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ y) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesSquareInterleave x y).symm
          ((z ++ y) ++ suffix)
    have step3 :
        Derives basis
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ y) ++ suffix)
          (((((((x ++ x) ++ y) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend ((x ++ x) ++ y)
          (derivesPromotion y z suffix).symm)
    have step4 :
        Derives basis
          (((((((x ++ x) ++ y) ++ y) ++ y) ++ z) ++ z) ++ suffix)
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (Derives.appendRight (derivesPower y).symm
            ((z ++ z) ++ suffix)))
    exact step1.trans (step2.trans (step3.trans step4))
  exact (derivesXYZXRelativeSquares x y z suffix).trans
    targetToSquares.symm

theorem derivesS5LeftNestedZExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      (((((((x ++ y) ++ x) ++ x) ++ y) ++ z) ++ z) ++ suffix) := by
  have step1 := derivesXYZXRelativeSquares x y z suffix
  have step2 :
      Derives basis
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix)
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesSquareInterleave x y)
        ((z ++ z) ++ suffix)
  have step3 :
      Derives basis
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ z) ++ suffix)
        (((((((x ++ y) ++ x) ++ x) ++ y) ++ z) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesRightDuplication x y)
        (((y ++ z) ++ z) ++ suffix)
  exact step1.trans (step2.trans step3)

theorem derivesS5AlternatingCrossingRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleCollapse x y z).symm suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix)
        ((((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesSandwichDuplication x y)
        ((z ++ x) ++ suffix)
  exact step1.trans step2

theorem derivesS5AlternatingCrossingYRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ y) ++ suffix)) := by
  have targetToSquares :
      Derives basis
        ((((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ y) ++ suffix))
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    have step1 :
        Derives basis
          ((((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ y) ++ suffix))
          ((((((x ++ y) ++ x) ++ z) ++ y) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesSandwichDuplication x y).symm
          ((z ++ y) ++ suffix)
    have step2 :
        Derives basis
          ((((((x ++ y) ++ x) ++ z) ++ y) ++ suffix))
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesLeftTransport x y z).symm suffix
    have step3 :
        Derives basis
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix))
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (derivesPromotion y z suffix).symm)
    exact step1.trans (step2.trans step3)
  exact (derivesXYZXRelativeSquares x y z suffix).trans
    targetToSquares.symm

theorem derivesS5AlternatingSquareRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ y) ++ y) ++ z) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ y) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesHeadTransport x y z).symm suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ y) ++ z) ++ x) ++ suffix)
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleCollapse x y (y ++ z)).symm
        suffix
  have step3 :
      Derives basis
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ x) ++ suffix)
        ((((((((x ++ y) ++ x) ++ y) ++ y) ++ z) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesRightDuplication y x)
          ((z ++ x) ++ suffix)))
  exact step1.trans (step2.trans step3)

theorem derivesS5AlternatingTurnRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ y) ++ z) ++ y) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ y) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesHeadTransport x y z).symm suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ y) ++ z) ++ x) ++ suffix)
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleCollapse x y (y ++ z)).symm
        suffix
  have step3 :
      Derives basis
        ((((((x ++ y) ++ x) ++ y) ++ z) ++ x) ++ suffix)
        ((((((((x ++ y) ++ x) ++ y) ++ z) ++ y) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight
        (derivesLateDuplicationLeft x y ((x ++ y) ++ z)) suffix
  exact step1.trans (step2.trans step3)

theorem derivesS5ThirdOccurrenceRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ z) ++ y) ++ x) ++ z) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleCollapse x y z).symm suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix)
        ((((((x ++ y) ++ x) ++ x) ++ z) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend (x ++ y) (derivesPromotion x z suffix).symm)
  have step3 :
      Derives basis
        ((((((x ++ y) ++ x) ++ x) ++ z) ++ z) ++ suffix)
        (((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ z) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesLateDuplicationLeft x y x)
        ((z ++ z) ++ suffix)
  have step4 :
      Derives basis
        (((((((x ++ y) ++ x) ++ y) ++ x) ++ z) ++ z) ++ suffix)
        ((((((((x ++ y) ++ x) ++ z) ++ y) ++ x) ++ z) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesSquareInterleave (y ++ x) z)
          suffix))
  exact step1.trans (step2.trans (step3.trans step4))

theorem derivesS5DoubledZTurnRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ z) ++ z) ++ x) ++ y) ++ suffix)) := by
  have targetToSquares :
      Derives basis
        ((((((((x ++ y) ++ x) ++ z) ++ z) ++ x) ++ y) ++ suffix))
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    have step1 :
        Derives basis
          ((((((((x ++ y) ++ x) ++ z) ++ z) ++ x) ++ y) ++ suffix))
          ((((((x ++ y) ++ z) ++ z) ++ x) ++ y) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesMiddleCollapse x y (z ++ z))
          (y ++ suffix)
    have step2 :
        Derives basis
          ((((((x ++ y) ++ z) ++ z) ++ x) ++ y) ++ suffix)
          ((((((x ++ x) ++ y) ++ z) ++ z) ++ y) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesCrossTransport x y (z ++ z)).symm
          suffix
    have step3 :
        Derives basis
          ((((((x ++ x) ++ y) ++ z) ++ z) ++ y) ++ suffix)
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (Derives.appendRight (derivesMiddleDuplication y z).symm
            suffix))
    have step4 :
        Derives basis
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix))
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (derivesPromotion y z suffix).symm)
    exact step1.trans (step2.trans (step3.trans step4))
  exact (derivesXYZXRelativeSquares x y z suffix).trans
    targetToSquares.symm

theorem derivesS5DoubledZReturnRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ x) ++ z) ++ z) ++ y) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleCollapse x y z).symm suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ x) ++ z) ++ x) ++ suffix)
        ((((((x ++ y) ++ x) ++ z) ++ y) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesLateDuplicationLeft x y (x ++ z))
        suffix
  have step3 :
      Derives basis
        ((((((x ++ y) ++ x) ++ z) ++ y) ++ x) ++ suffix)
        ((((((((x ++ y) ++ x) ++ z) ++ z) ++ y) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesMiddleDuplication (y ++ x) z)
          suffix))
  exact step1.trans (step2.trans step3)

theorem derivesS5DoubledYAndZRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ y) ++ x) ++ z) ++ z) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((((x ++ y) ++ z) ++ x) ++ y) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesSandwichDuplication x (y ++ z)) suffix
  have step2 :
      Derives basis
        (((((((x ++ y) ++ z) ++ x) ++ y) ++ z) ++ x) ++ suffix)
        (((((((x ++ y) ++ x) ++ y) ++ z) ++ z) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesSquareInterleave (x ++ y) z).symm
        (x ++ suffix)
  have step3 :
      Derives basis
        (((((((x ++ y) ++ x) ++ y) ++ z) ++ z) ++ x) ++ suffix)
        ((((((((x ++ y) ++ y) ++ x) ++ z) ++ z) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesLeftTransport y x (z ++ z)).symm
          suffix))
  exact step1.trans (step2.trans step3)

theorem derivesS5RepeatedBlockRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ x) ++ y) ++ z) ++ x) ++ suffix)) := by
  simpa only [Word.append_assoc] using
    Derives.appendRight (derivesSandwichDuplication x (y ++ z)) suffix

theorem derivesS5DelayedYExpansionRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ y) ++ x) ++ z) ++ suffix)) := by
  have targetToSquares :
      Derives basis
        ((((((((x ++ y) ++ z) ++ y) ++ y) ++ x) ++ z) ++ suffix))
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    have step1 :
        Derives basis
          ((((((((x ++ y) ++ z) ++ y) ++ y) ++ x) ++ z) ++ suffix))
          (((((((x ++ y) ++ z) ++ y) ++ x) ++ z) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend x
          (Derives.appendRight (derivesRightDuplication y z).symm
            ((x ++ z) ++ suffix)))
    have step2 :
        Derives basis
          (((((((x ++ y) ++ z) ++ y) ++ x) ++ z) ++ suffix))
          ((((((x ++ y) ++ z) ++ x) ++ z) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesLateDuplicationLeft x y z).symm
          (z ++ suffix)
    have step3 :
        Derives basis
          ((((((x ++ y) ++ z) ++ x) ++ z) ++ suffix))
          ((((((x ++ y) ++ x) ++ z) ++ z) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesTailTransport x y z).symm suffix
    have step4 :
        Derives basis
          ((((((x ++ y) ++ x) ++ z) ++ z) ++ suffix))
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight (derivesPromotion x y z).symm
          (z ++ suffix)
    exact step1.trans (step2.trans (step3.trans step4))
  exact (derivesXYZXRelativeSquares x y z suffix).trans
    targetToSquares.symm

theorem derivesS5DelayedYReturnRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ y) ++ z) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleDuplication x (y ++ z)) suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix)
        ((((((((x ++ y) ++ z) ++ y) ++ y) ++ z) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesRightDuplication y z)
          ((z ++ x) ++ suffix)))
  exact step1.trans step2

theorem derivesS5DelayedCrossingRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ z) ++ x) ++ y) ++ suffix)) := by
  have targetToSquares :
      Derives basis
        ((((((((x ++ y) ++ z) ++ y) ++ z) ++ x) ++ y) ++ suffix))
        ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
    have step1 :
        Derives basis
          ((((((((x ++ y) ++ z) ++ y) ++ z) ++ x) ++ y) ++ suffix))
          ((((((x ++ x) ++ y) ++ (z ++ y)) ++ z) ++ y) ++ suffix) := by
      simpa only [Word.append_assoc] using
        Derives.appendRight
          (derivesCrossTransport x y ((z ++ y) ++ z)).symm suffix
    have step2 :
        Derives basis
          ((((((x ++ x) ++ y) ++ (z ++ y)) ++ z) ++ y) ++ suffix)
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix)) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (Derives.appendRight (derivesSandwichDuplication y z).symm
            suffix))
    have step3 :
        Derives basis
          ((((((x ++ x) ++ y) ++ z) ++ y) ++ suffix))
          ((((((x ++ x) ++ y) ++ y) ++ z) ++ z) ++ suffix) := by
      simpa only [Word.append_assoc] using
        (Derives.prepend (x ++ x)
          (derivesPromotion y z suffix).symm)
    exact step1.trans (step2.trans step3)
  exact (derivesXYZXRelativeSquares x y z suffix).trans
    targetToSquares.symm

theorem derivesS5DelayedTurnRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ z) ++ y) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleDuplication x (y ++ z)) suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix)
        ((((((((x ++ y) ++ z) ++ y) ++ z) ++ y) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight
        (derivesLateDuplicationLeft x y ((z ++ y) ++ z)) suffix
  exact step1.trans step2

theorem derivesS5DelayedSquareRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ z) ++ z) ++ x) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ x) ++ suffix)
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesMiddleDuplication x (y ++ z)) suffix
  have step2 :
      Derives basis
        (((((x ++ y) ++ z) ++ (y ++ z)) ++ x) ++ suffix)
        ((((((((x ++ y) ++ z) ++ y) ++ z) ++ z) ++ x) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend (x ++ y)
        (Derives.appendRight (derivesRightDuplication z y)
          (x ++ suffix)))
  exact step1.trans step2

theorem derivesS5TerminalInitialRelativeBlocks
    (x y z suffix : Word Nat) :
    Derives basis
      (((x ++ y) ++ z) ++ y ++ suffix)
      ((((((((x ++ y) ++ z) ++ y) ++ z) ++ z) ++ y) ++ suffix)) := by
  have step1 :
      Derives basis
        ((((x ++ y) ++ z) ++ y) ++ suffix)
        ((((((x ++ y) ++ z) ++ y) ++ z) ++ y) ++ suffix) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend x
        (Derives.appendRight (derivesSandwichDuplication y z) suffix))
  have step2 :
      Derives basis
        ((((((x ++ y) ++ z) ++ y) ++ z) ++ y) ++ suffix)
        ((((((((x ++ y) ++ z) ++ y) ++ z) ++ z) ++ y) ++ suffix)) := by
    simpa only [Word.append_assoc] using
      (Derives.prepend ((x ++ y) ++ z)
        (Derives.appendRight (derivesMiddleDuplication y z) suffix))
  exact step1.trans step2

/-! ## Exact `S5_788` laws and the finite dispatch theorem -/

private def literalWord (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def xWord : Word Nat := Word.singleton 0
private def yWord : Word Nat := Word.singleton 1
private def zWord : Word Nat := Word.singleton 2

theorem derivesS5_788AxiomRelative
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_788.basis)
    (suffix : Word Nat) :
    Derives basis (identity.lhs ++ suffix) (identity.rhs ++ suffix) := by
  simp only [SemigroupBasis.CoRoots.S5_788.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives basis
      (literalWord 0 [0] ++ suffix) (literalWord 0 [0, 0] ++ suffix)
    simpa [literalWord, xWord, Word.singleton, Word.append,
      Word.append_assoc] using derivesS5PowerRelativeBlocks xWord suffix
  · change Derives basis
      (literalWord 0 [1, 0] ++ suffix)
      (literalWord 0 [0, 1, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5LeftDuplicationRelativeBlocks xWord yWord suffix
  · change Derives basis
      (literalWord 0 [1, 0] ++ suffix)
      (literalWord 0 [0, 1, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5SquaresRelativeBlocks xWord yWord suffix
  · change Derives basis
      (literalWord 0 [1, 0, 2] ++ suffix)
      (literalWord 0 [1, 0, 1, 1, 0, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5IntervalExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 0, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5RightXExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 0, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5RightZExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [0, 1, 2, 1, 1, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5SeparatorExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 0, 1, 2, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5LeftNestedExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 0, 1, 2, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5LeftNestedZExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 1, 0, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5AlternatingCrossingRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 1, 0, 2, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5AlternatingCrossingYRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 1, 1, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5AlternatingSquareRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 1, 2, 1, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5AlternatingTurnRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 2, 1, 0, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5ThirdOccurrenceRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 2, 2, 0, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DoubledZTurnRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 0, 2, 2, 1, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DoubledZReturnRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 1, 0, 2, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DoubledYAndZRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 0, 1, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5RepeatedBlockRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 1, 1, 0, 2] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DelayedYExpansionRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 1, 1, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DelayedYReturnRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 1, 2, 0, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DelayedCrossingRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 1, 2, 1, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DelayedTurnRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 0] ++ suffix)
      (literalWord 0 [1, 2, 1, 2, 2, 0] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5DelayedSquareRelativeBlocks xWord yWord zWord suffix
  · change Derives basis
      (literalWord 0 [1, 2, 1] ++ suffix)
      (literalWord 0 [1, 2, 1, 2, 2, 1] ++ suffix)
    simpa [literalWord, xWord, yWord, zWord, Word.singleton, Word.append,
      Word.append_assoc] using
      derivesS5TerminalInitialRelativeBlocks xWord yWord zWord suffix

/-! ## Substitution-generalized and derivation-generalized lift -/

/-- Reserve the fresh literal `3` for the fixed final suffix while applying
an arbitrary substitution to the variables of an `S5_788` axiom. -/
private def suffixSubstitution
    (sigma : Nat → Word Nat) (suffix : Word Nat) : Nat → Word Nat
  | 3 => suffix
  | letter => sigma letter

/-- Every substituted `S5_788` axiom lifts immediately before the same fixed
nonempty suffix. -/
theorem liftS5_788AxiomUnderSuffix
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_788.basis)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind sigma ++ suffix)
      (identity.rhs.bind sigma ++ suffix) := by
  have substituted :=
    Derives.subst
      (derivesS5_788AxiomRelative identity member (Word.singleton 3))
      (suffixSubstitution sigma suffix)
  simp only [SemigroupBasis.CoRoots.S5_788.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simpa [SemigroupBasis.CoRoots.S5_788.powerLaw,
      SemigroupBasis.CoRoots.S5_788.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_788.squaresLaw,
      SemigroupBasis.CoRoots.S5_788.intervalExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.rightXExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.rightZExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.separatorExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.leftNestedExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.leftNestedZExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.alternatingCrossingLaw,
      SemigroupBasis.CoRoots.S5_788.alternatingCrossingYLaw,
      SemigroupBasis.CoRoots.S5_788.alternatingSquareLaw,
      SemigroupBasis.CoRoots.S5_788.alternatingTurnLaw,
      SemigroupBasis.CoRoots.S5_788.thirdOccurrenceLaw,
      SemigroupBasis.CoRoots.S5_788.doubledZTurnLaw,
      SemigroupBasis.CoRoots.S5_788.doubledZReturnLaw,
      SemigroupBasis.CoRoots.S5_788.doubledYAndZLaw,
      SemigroupBasis.CoRoots.S5_788.repeatedBlockLaw,
      SemigroupBasis.CoRoots.S5_788.delayedYExpansionLaw,
      SemigroupBasis.CoRoots.S5_788.delayedYReturnLaw,
      SemigroupBasis.CoRoots.S5_788.delayedCrossingLaw,
      SemigroupBasis.CoRoots.S5_788.delayedTurnLaw,
      SemigroupBasis.CoRoots.S5_788.delayedSquareLaw,
      SemigroupBasis.CoRoots.S5_788.terminalInitialLaw,
      SemigroupBasis.CoRoots.S5_788.xx,
      SemigroupBasis.CoRoots.S5_788.xxx,
      SemigroupBasis.CoRoots.S5_788.xyx,
      SemigroupBasis.CoRoots.S5_788.xxyx,
      SemigroupBasis.CoRoots.S5_788.xxyy,
      SemigroupBasis.CoRoots.S5_788.xyxz,
      SemigroupBasis.CoRoots.S5_788.xyxyyxz,
      SemigroupBasis.CoRoots.S5_788.xyzx,
      SemigroupBasis.CoRoots.S5_788.xyzxx,
      SemigroupBasis.CoRoots.S5_788.xyzxz,
      SemigroupBasis.CoRoots.S5_788.xxyzyyz,
      SemigroupBasis.CoRoots.S5_788.xyxxyzy,
      SemigroupBasis.CoRoots.S5_788.xyxxyzz,
      SemigroupBasis.CoRoots.S5_788.xyxyxzx,
      SemigroupBasis.CoRoots.S5_788.xyxyxzy,
      SemigroupBasis.CoRoots.S5_788.xyxyyzx,
      SemigroupBasis.CoRoots.S5_788.xyxyzyx,
      SemigroupBasis.CoRoots.S5_788.xyxzyxz,
      SemigroupBasis.CoRoots.S5_788.xyxzzxy,
      SemigroupBasis.CoRoots.S5_788.xyxzzyx,
      SemigroupBasis.CoRoots.S5_788.xyyxzzx,
      SemigroupBasis.CoRoots.S5_788.xyzxyzx,
      SemigroupBasis.CoRoots.S5_788.xyzyyxz,
      SemigroupBasis.CoRoots.S5_788.xyzyyzx,
      SemigroupBasis.CoRoots.S5_788.xyzyzxy,
      SemigroupBasis.CoRoots.S5_788.xyzyzyx,
      SemigroupBasis.CoRoots.S5_788.xyzyzzx,
      SemigroupBasis.CoRoots.S5_788.xyzy,
      SemigroupBasis.CoRoots.S5_788.xyzyzzy,
      suffixSubstitution, Word.bind, Word.singleton, Word.append,
      Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every `S5_788` derivation remains valid after an arbitrary substitution
and immediately before an arbitrary fixed nonempty suffix. -/
theorem liftS5_788UnderSuffix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_788.basis left right)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      exact liftS5_788AxiomUnderSuffix _ member suffix sigma
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix sigma).symm
  | trans _ _ first second =>
      exact (first suffix sigma).trans (second suffix sigma)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind sigma) (induction suffix sigma)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind sigma ++ suffix) sigma
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction suffix (fun letter => (tau letter).bind sigma)

/-- Identity-substitution specialization of `liftS5_788UnderSuffix`. -/
theorem liftS5_788UnderSuffixIdentity
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_788.basis left right)
    (suffix : Word Nat) :
    Derives basis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_788UnderSuffix derivation suffix Word.singleton

end SemigroupBasis.CoRoots.Order6FordLord1cca
