import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusSemantics

/-!
# Rank071 approved B16: unrestricted actual-factor converse

Repeated initial letters are aligned by two own-head squares and their
three-edge commutation. Guarded lower completeness is used only behind
nonempty words. Simple initial letters agree by the actual marker factor;
singleton and distinct-pair words are rigid, and longer fresh-head tails
are stripped semantically using a left identity on products.

There is no cancellation assumption, bounded-rank premise, raw-head
equality premise for repeated words, or unguarded lower-law replay.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusIntersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusReplay
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusSemantics

/-- The two repeated heads need not be the same letter. -/
theorem repeatedPaddingConverse (left right : Word Nat)
    (leftRepeated : left.head ∈ left.tail) (rightRepeated : right.head ∈ right.tail)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis left right := by
  let leftSquare := Word.singleton left.head ++ Word.singleton left.head
  let rightSquare := Word.singleton right.head ++ Word.singleton right.head
  have leftPad : Derives basis left (leftSquare ++ left) :=
    derivesOwnHeadSquare left leftRepeated
  have rightPad : Derives basis right (rightSquare ++ right) :=
    derivesOwnHeadSquare right rightRepeated
  have toRightPadded : (Identity.mk left (rightSquare ++ right)).SatisfiedBy rightTable.semigroup := by
    intro valuation
    exact (valid valuation).trans (rightPad.sound modelsRight valuation)
  have removeLeftSquare : (Identity.mk (leftSquare ++ right) right).SatisfiedBy rightTable.semigroup := by
    intro valuation
    calc
      rightTable.semigroup.eval valuation (leftSquare ++ right) =
          rightTable.semigroup.mul (rightTable.semigroup.eval valuation leftSquare)
            (rightTable.semigroup.eval valuation right) := by rw [Semigroup.eval_append]
      _ = rightTable.semigroup.mul (rightTable.semigroup.eval valuation leftSquare)
            (rightTable.semigroup.eval valuation left) :=
        congrArg (fun value => rightTable.semigroup.mul (rightTable.semigroup.eval valuation leftSquare) value)
          (valid valuation).symm
      _ = rightTable.semigroup.eval valuation (leftSquare ++ left) := by simp only [Semigroup.eval_append]
      _ = rightTable.semigroup.eval valuation left := (leftPad.sound modelsRight valuation).symm
      _ = rightTable.semigroup.eval valuation right := valid valuation
  have replayLeft : Derives basis (leftSquare ++ left) (leftSquare ++ (rightSquare ++ right)) :=
    derivesSamePrefixOfLowerValid left (rightSquare ++ right) leftSquare toRightPadded
  have commute : Derives basis (leftSquare ++ (rightSquare ++ right))
      (rightSquare ++ (leftSquare ++ right)) := by
    simpa only [leftSquare, rightSquare, Word.append_assoc] using
      Derives.appendRight (derivesSquaresCommute (Word.singleton left.head) (Word.singleton right.head)) right
  have replayRight : Derives basis (rightSquare ++ (leftSquare ++ right)) (rightSquare ++ right) :=
    derivesSamePrefixOfLowerValid (leftSquare ++ right) right rightSquare removeLeftSquare
  exact leftPad.trans (replayLeft.trans (commute.trans (replayRight.trans rightPad.symm)))

/-- A simple-head word is either lower-signature rigid or has a product tail. -/
theorem simpleRigidOrLong (word : Word Nat) (fresh : word.head ∉ word.tail) :
    (∀ other, LowerSignature word other → word = other) ∨
      ∃ head first second rest, word = Word.mk head (first :: second :: rest) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => exact Or.inl (singletonRigid head)
      | cons first rest =>
          cases rest with
          | nil =>
              have different : head ≠ first := by
                intro equal
                exact fresh (by simp [equal])
              exact Or.inl (distinctPairRigid head first different)
          | cons second rest => exact Or.inr ⟨head, first, second, rest, rfl⟩

/-- Strip a common fresh head only after excluding both short rigid strata. -/
theorem simpleConverse (left right : Word Nat)
    (leftValid : (Identity.mk left right).SatisfiedBy leftTable.semigroup)
    (rightValid : (Identity.mk left right).SatisfiedBy rightTable.semigroup)
    (fresh : left.head ∉ left.tail) : Derives basis left right := by
  have rightFacts := sameHeadOfSimple (Identity.mk left right) leftValid fresh
  have rightFresh : right.head ∉ right.tail := by
    have headEqual : right.head = left.head := rightFacts.1
    rw [headEqual]
    exact rightFacts.2
  have same := SemigroupBasis.CoRoots.S5_240.valid_signature (Identity.mk left right) rightValid
  rcases simpleRigidOrLong left fresh with rigid | ⟨head, first, second, rest, leftShape⟩
  · rw [rigid right same]
    exact Derives.refl _
  · rcases simpleRigidOrLong right rightFresh with rigid | ⟨otherHead, otherFirst, otherSecond, otherRest, rightShape⟩
    · rw [rigid left same.symm]
      exact Derives.refl _
    · subst left
      subst right
      have equal : otherHead = head := rightFacts.1
      subst otherHead
      have stripped : (Identity.mk (Word.mk first (second :: rest))
          (Word.mk otherFirst (otherSecond :: otherRest))).SatisfiedBy rightTable.semigroup :=
        freshHeadTailValid head (Word.mk first (second :: rest))
          (Word.mk otherFirst (otherSecond :: otherRest)) fresh rightFacts.2
          (by simp) (by simp) rightValid
      exact derivesSamePrefixOfLowerValid (Word.mk first (second :: rest))
        (Word.mk otherFirst (otherSecond :: otherRest)) (Word.singleton head) stripped

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

/-- Full arbitrary-rank, arbitrary-length converse for exactly the approved B16. -/
theorem complete : Complete := by
  intro identity leftValid rightValid
  by_cases repeated : identity.lhs.head ∈ identity.lhs.tail
  · exact repeatedPaddingConverse identity.lhs identity.rhs repeated
      (repeatedRight identity leftValid repeated) rightValid
  · exact simpleConverse identity.lhs identity.rhs leftValid rightValid repeated

theorem valid_iff_derives (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup) ↔
      Derives basis identity.lhs identity.rhs := by
  constructor
  · intro valid
    exact complete identity valid.1 valid.2
  · intro derivation
    exact ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem oppositeBasisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  (basisForOfFinitePair target pair).oppositeReversed

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusIntersection
