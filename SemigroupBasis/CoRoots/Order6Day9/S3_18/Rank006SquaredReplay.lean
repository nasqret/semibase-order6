import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros
import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics
import SemigroupBasis.Examples.CommutativePositiveModThreeFour

/-!
# Rank006: a sound squared replay of the complete positive-mod-three calculus

The lower laws x = x^4 and xy = yx are NOT Sigma+ laws. Their squared
images are derived here. The replay keeps the square on every source,
substitution and contextual intermediate; it never bare-retargets a lower
axiom. This closes the entire powered-block subproblem without imposing
an alphabet, length or multiplicity bound. Arbitrary separator assembly
remains a separate obligation.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006PeriodMacros

abbrev positiveBasis := commutativePositiveModThreeBasis

theorem derivesSquaredPower (word : Word Nat) :
    Derives sigmaPlus (square word) (square (fourth word)) := by
  have second : Derives sigmaPlus (fifth word) (square (fourth word)) := by
    simpa only [fifth, fourth, square, cube, Word.append_assoc] using
      Derives.appendRight (derivesSquarePeriod word) (cube word)
  exact (derivesSquarePeriod word).trans second

theorem derivesSquaredCommutativity (first second : Word Nat) :
    Derives sigmaPlus (square (first ++ second)) (square (second ++ first)) :=
  (derivesSquareAppend first second).trans
    ((derivesSquaresCommute first second).trans (derivesSquareAppend second first).symm)

theorem derivesSquaredPrepend (stem : Word Nat) {first second : Word Nat}
    (derivation : Derives sigmaPlus (square first) (square second)) :
    Derives sigmaPlus (square (stem ++ first)) (square (stem ++ second)) :=
  (derivesSquareAppend stem first).trans
    ((Derives.prepend (square stem) derivation).trans (derivesSquareAppend stem second).symm)

theorem derivesSquaredAppend {first second : Word Nat}
    (derivation : Derives sigmaPlus (square first) (square second)) (suffix : Word Nat) :
    Derives sigmaPlus (square (first ++ suffix)) (square (second ++ suffix)) :=
  (derivesSquareAppend first suffix).trans
    ((Derives.appendRight derivation (square suffix)).trans (derivesSquareAppend second suffix).symm)

private theorem bind_append (first second : Word Nat) (substitution : Nat → Word Nat) :
    (first ++ second).bind substitution = first.bind substitution ++ second.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- All lower constructors replay, including arbitrary nonempty-word
substitutions. Squaring is maintained throughout the induction. -/
theorem liftPositiveSquared {left right : Word Nat}
    (derivation : Derives positiveBasis left right) (substitution : Nat → Word Nat) :
    Derives sigmaPlus (square (left.bind substitution)) (square (right.bind substitution)) := by
  induction derivation generalizing substitution with
  | fromBasis member =>
      simp only [positiveBasis, commutativePositiveModThreeBasis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [positiveModThreePowerLaw, positiveModThreeX, positiveModThreeXXXX,
          fourth, square, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesSquaredPower (substitution 0)
      · simpa [positiveModThreeCommutativityLaw, positiveModThreeXY, positiveModThreeYX,
          square, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesSquaredCommutativity (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction substitution).symm
  | trans _ _ first second => exact (first substitution).trans (second substitution)
  | prepend stem _ induction =>
      simpa only [bind_append] using
        derivesSquaredPrepend (stem.bind substitution) (induction substitution)
  | appendRight _ suffix induction =>
      simpa only [bind_append] using
        derivesSquaredAppend (induction substitution) (suffix.bind substitution)
  | subst _ next induction =>
      simpa only [bind_bind] using
        induction (fun letter => (next letter).bind substitution)

theorem liftPositiveSquaredIdentity {left right : Word Nat}
    (derivation : Derives positiveBasis left right) :
    Derives sigmaPlus (square left) (square right) := by
  simpa only [bind_singleton] using liftPositiveSquared derivation Word.singleton

def doubled (word : Word Nat) : Word Nat :=
  word.bind (fun letter => square (Word.singleton letter))

theorem derivesSquareLetterwise (word : Word Nat) :
    Derives sigmaPlus (square word) (doubled word) := by
  cases word with
  | mk head tail =>
      induction tail generalizing head with
      | nil => exact Derives.refl _
      | cons next rest induction =>
          change Derives sigmaPlus (square (Word.singleton head ++ Word.mk next rest))
            ((Word.singleton head ++ Word.mk next rest).bind
              (fun letter => square (Word.singleton letter)))
          rw [bind_append]
          exact (derivesSquareAppend (Word.singleton head) (Word.mk next rest)).trans
            (Derives.prepend (square (Word.singleton head)) (induction next))

/-- Equivalent letterwise-square interface, obtained by actual derivations. -/
theorem liftPositiveLetterwise {left right : Word Nat}
    (derivation : Derives positiveBasis left right) :
    Derives sigmaPlus (doubled left) (doubled right) :=
  (derivesSquareLetterwise left).symm.trans
    ((liftPositiveSquaredIdentity derivation).trans (derivesSquareLetterwise right))

/-- Uses the independently complete lower calculus only at its own basis. -/
theorem positiveDerivesOfSupportMod (left right : Word Nat)
    (support : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (residues : ∀ letter, left.toList.count letter % 3 = right.toList.count letter % 3) :
    Derives positiveBasis left right := by
  have reducedPerm := positiveModThreeReduce_perm support residues
  have leftNormal := positiveModThreeDerivesNormal left
  have rightNormal := positiveModThreeDerivesNormal right
  cases leftShape : positiveModThreeReduce left.toList with
  | nil =>
      rw [leftShape] at leftNormal
      exact False.elim leftNormal
  | cons first rest =>
      cases rightShape : positiveModThreeReduce right.toList with
      | nil =>
          rw [rightShape] at rightNormal
          exact False.elim rightNormal
      | cons other otherRest =>
          rw [leftShape] at leftNormal
          rw [rightShape] at rightNormal
          rw [leftShape, rightShape] at reducedPerm
          exact leftNormal.trans
            ((positiveModThreeDerivesPermutation
              (Word.mk first rest) (Word.mk other otherRest) reducedPerm).trans rightNormal.symm)

theorem derivesSquaresOfSupportMod (left right : Word Nat)
    (support : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (residues : ∀ letter, left.toList.count letter % 3 = right.toList.count letter % 3) :
    Derives sigmaPlus (square left) (square right) :=
  liftPositiveSquaredIdentity (positiveDerivesOfSupportMod left right support residues)

theorem derivesLetterwiseOfSupportMod (left right : Word Nat)
    (support : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (residues : ∀ letter, left.toList.count letter % 3 = right.toList.count letter % 3) :
    Derives sigmaPlus (doubled left) (doubled right) :=
  liftPositiveLetterwise (positiveDerivesOfSupportMod left right support residues)

theorem rightValid_support (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ letter, letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList := by
  rw [rightTable_eq_uniqueSeparatorFour] at valid
  exact uniqueSeparatorFourValid_support_iff identity valid

/-- Full factor-theory completeness on squared words, with no bound. -/
theorem derivesSquaresOfFactorValid (left right : Word Nat)
    (leftValid : (Identity.mk (square left) (square right)).SatisfiedBy leftTable.semigroup)
    (rightValid : (Identity.mk (square left) (square right)).SatisfiedBy rightTable.semigroup) :
    Derives sigmaPlus (square left) (square right) := by
  apply derivesSquaresOfSupportMod left right
  · intro letter
    have supported := rightValid_support _ rightValid letter
    simpa only [square, Word.toList_append, List.mem_append, or_self] using supported
  · intro letter
    have modulo := (leftValid_iff_mod_eq _).mp leftValid letter
    simp only [square, Word.toList_append, List.count_append] at modulo
    omega

theorem squared_factor_valid_iff_derives (left right : Word Nat) :
    ((Identity.mk (square left) (square right)).SatisfiedBy leftTable.semigroup ∧
      (Identity.mk (square left) (square right)).SatisfiedBy rightTable.semigroup) ↔
      Derives sigmaPlus (square left) (square right) :=
  ⟨fun valid => derivesSquaresOfFactorValid left right valid.1 valid.2,
    fun derivation => derives_factor_valid derivation⟩

theorem derives_support {left right : Word Nat}
    (derivation : Derives sigmaPlus left right) :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList :=
  rightValid_support (Identity.mk left right) (derivation.sound modelsRight)

theorem listDerives_support {left right : List Nat}
    (derivation : ListDerives sigmaPlus left right) (letter : Nat) :
    letter ∈ left ↔ letter ∈ right := by
  cases derivation with
  | empty => simp
  | words wordDerivation =>
      exact derives_support wordDerivation letter

theorem derivesSquaredPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives sigmaPlus (square left) (square right) :=
  liftPositiveSquaredIdentity (positiveModThreeDerivesPermutation left right permutation)

/-- A return has a genuine square representative; no first-letter-square shortcut. -/
theorem derivesReturnToSquare (outer middle : Word Nat) :
    Derives sigmaPlus ((outer ++ middle) ++ outer) (square (outer ++ square middle)) := by
  have collect : Derives sigmaPlus (square outer ++ fourth middle)
      (square (outer ++ square middle)) := by
    simpa only [square, fourth, Word.append_assoc] using
      (derivesSquareAppend outer (square middle)).symm
  exact (derivesReturnToPoweredSquares outer middle).trans collect

theorem derivesCubeToSquare (word : Word Nat) :
    Derives sigmaPlus (cube word) (square (cube word)) := by
  simpa only [cube, square, fifth, Word.append_assoc] using
    Derives.appendRight (derivesSquarePeriod word) word

theorem derivesDoubleReturnToSquare (outer middle : Word Nat) :
    Derives sigmaPlus ((square outer ++ middle) ++ outer)
      (square (cube outer ++ square middle)) := by
  have first : Derives sigmaPlus ((square outer ++ middle) ++ outer)
      (cube outer ++ fourth middle) := by
    simpa only [square, cube, Word.append_assoc] using
      Derives.prepend outer (derivesReturnToPoweredSquares outer middle)
  have second : Derives sigmaPlus (cube outer ++ fourth middle)
      (square (cube outer) ++ fourth middle) :=
    Derives.appendRight (derivesCubeToSquare outer) (fourth middle)
  have third : Derives sigmaPlus (square (cube outer) ++ fourth middle)
      (square (cube outer ++ square middle)) := by
    simpa only [square, fourth, Word.append_assoc] using
      (derivesSquareAppend (cube outer) (square middle)).symm
  exact first.trans (second.trans third)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay
