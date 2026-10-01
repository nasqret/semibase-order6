import SemigroupBasis.CoRoots.Order6Day10.S3_16op.Rank067Replay
import SemigroupBasis.Subdirect

/-!
# Unrestricted exact B7 converse for Rank067 / S6_14272

The actual S5_904 factor fixes the literal first two letters. The actual
S3_16-opposite factor supplies the complete right-regular-band calculus.
Four displayed-law edges lift that calculus behind any two nonempty prefix
blocks. Doubling the first two letters adds the common guard to each word;
the lifted band derivation then joins them. Singleton words are literal.
No length/rank bound, erased context, cancellation, or extra law is assumed.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_16op.Rank067Intersection

open SemigroupBasis

abbrev basis := Rank067Replay.basis
abbrev leftTable := Rank067Replay.leftTable
abbrev rightTable := Rank067Replay.rightTable

/-- Duplicate the initial pair, leaving the remaining list in place. -/
theorem duplicateInitialPair (first second : Nat) (rest : List Nat) :
    Derives basis (Word.mk first (second :: rest))
      (Word.mk first [second] ++ Word.mk first (second :: rest)) := by
  have step := Rank067Replay.derivesProductSquare
    (Word.singleton first) (Word.singleton second)
  cases rest with
  | nil =>
      simpa [Word.singleton, Word.append] using step
  | cons third rest =>
      simpa [Word.singleton, Word.append, List.append_assoc] using
        Derives.appendRight step (Word.mk third rest)

theorem derivesOfFirstTwoAndUpperValid (left right : Word Nat)
    (prefixes : CoRoots.S5_830.FirstTwo left = CoRoots.S5_830.FirstTwo right)
    (valid : (Identity.mk left right).SatisfiedBy leftTable.semigroup) :
    Derives basis left right := by
  cases left with
  | mk first leftTail =>
      cases right with
      | mk otherFirst rightTail =>
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  have heads : first = otherFirst := by
                    simpa [CoRoots.S5_830.FirstTwo, Word.toList] using prefixes
                  subst otherFirst
                  exact Derives.refl _
              | cons otherSecond rightRest =>
                  have lengths := congrArg List.length prefixes
                  simp [CoRoots.S5_830.FirstTwo, Word.toList] at lengths
          | cons second leftRest =>
              cases rightTail with
              | nil =>
                  have lengths := congrArg List.length prefixes
                  simp [CoRoots.S5_830.FirstTwo, Word.toList] at lengths
              | cons otherSecond rightRest =>
                  have pairs : [first, second] = [otherFirst, otherSecond] := by
                    simpa [CoRoots.S5_830.FirstTwo, Word.toList] using prefixes
                  have heads : first = otherFirst := (List.cons.inj pairs).1
                  have seconds : second = otherSecond :=
                    (List.cons.inj (List.cons.inj pairs).2).1
                  subst otherFirst
                  subst otherSecond
                  have leftPadding := duplicateInitialPair first second leftRest
                  have rightPadding := duplicateInitialPair first second rightRest
                  have middle :
                      Derives basis
                        (Word.mk first [second] ++ Word.mk first (second :: leftRest))
                        (Word.mk first [second] ++ Word.mk first (second :: rightRest)) := by
                    simpa [Word.singleton, Word.append] using
                      Rank067Replay.derivesSameTwoPrefixOfUpperValid
                        (Word.mk first (second :: leftRest))
                        (Word.mk first (second :: rightRest))
                        (Word.singleton first) (Word.singleton second) valid
                  exact leftPadding.trans (middle.trans rightPadding.symm)

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity leftValid rightValid
  have prefixes := Rank067Replay.lowerValid_firstTwo identity rightValid
  exact derivesOfFirstTwoAndUpperValid identity.lhs identity.rhs prefixes leftValid

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := Rank067Replay.modelsLeft
  rightModels := Rank067Replay.modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.S3_16op.Rank067Intersection
