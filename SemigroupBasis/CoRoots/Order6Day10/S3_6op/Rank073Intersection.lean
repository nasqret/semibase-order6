import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Eligibility
import SemigroupBasis.Subdirect

/-!
# Rank073 exact B12: unrestricted actual-factor converse

Repeated heads are retargeted through eligible lower-prefix padding and the
displayed xyx=yxyx law. No commutation of squares is used. Simple heads use
actual-marker freshness, joint short-word rigidity, and product-only semantic
stripping. All owner obligations are discharged for arbitrary Nat words.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Semantics
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Eligibility

private theorem repeated_long (word : Word Nat) (repeated : word.head ∈ word.tail) :
    word.tail ≠ [] := by
  intro empty
  simp [empty] at repeated

/-- Change a repeated initial letter to any eligible support letter. -/
theorem retargetEligible (word : Word Nat) (repeated : word.head ∈ word.tail)
    (letter : Nat) (eligible : Eligible word letter) :
    Derives basis word (Word.singleton letter ++ word) := by
  let oldHead := Word.singleton word.head
  let newHead := Word.singleton letter
  have duplicate : Derives basis word (oldHead ++ word) := derivesOwnHeadPad word repeated
  have padOld : (Identity.mk word (oldHead ++ word)).SatisfiedBy rightTable.semigroup :=
    duplicate.sound modelsRight
  have padNew : (Identity.mk word (newHead ++ word)).SatisfiedBy rightTable.semigroup :=
    eligiblePrefixValid word letter (repeated_long word repeated) eligible
  have padTwo : (Identity.mk word (newHead ++ (oldHead ++ word))).SatisfiedBy rightTable.semigroup := by
    intro valuation
    exact (padNew valuation).trans (lowerValidPrepend padOld newHead valuation)
  have padThree : (Identity.mk word (oldHead ++ (newHead ++ (oldHead ++ word)))).SatisfiedBy
      rightTable.semigroup := by
    intro valuation
    exact (padOld valuation).trans (lowerValidPrepend padTwo oldHead valuation)
  have insert : Derives basis (oldHead ++ word) (oldHead ++ (newHead ++ (oldHead ++ word))) :=
    derivesSamePrefixOfLowerValid word (newHead ++ (oldHead ++ word)) oldHead padTwo
  have retarget : Derives basis (oldHead ++ (newHead ++ (oldHead ++ word)))
      (newHead ++ (oldHead ++ (newHead ++ (oldHead ++ word)))) := by
    simpa only [Word.append_assoc] using Derives.appendRight (derivesHeadRetarget oldHead newHead) word
  have remove : Derives basis (newHead ++ (oldHead ++ (newHead ++ (oldHead ++ word))))
      (newHead ++ word) :=
    derivesSamePrefixOfLowerValid (oldHead ++ (newHead ++ (oldHead ++ word))) word newHead
      (fun valuation => (padThree valuation).symm)
  exact duplicate.trans (insert.trans (retarget.trans remove))

theorem repeatedPaddingConverse (left right : Word Nat)
    (leftRepeated : left.head ∈ left.tail) (rightRepeated : right.head ∈ right.tail)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis left right := by
  have same := SemigroupBasis.CoRoots.S5_303.valid_signature (Identity.mk left right) valid
  have leftEligible := eligibleHead left (repeated_long left leftRepeated)
  have rightEligible : Eligible right left.head := eligibleOfSignature same leftEligible
  have leftPad := derivesOwnHeadPad left leftRepeated
  have rightPad := retargetEligible right rightRepeated left.head rightEligible
  have middle := derivesSamePrefixOfLowerValid left right (Word.singleton left.head) valid
  exact leftPad.trans (middle.trans rightPad.symm)

/-- Short rigidity includes freshness of the other word; lower rigidity alone is false. -/
theorem simpleRigidOrLong (word : Word Nat) (fresh : word.head ∉ word.tail) :
    (∀ other, word.head ∉ other.tail → LowerSignature word other → word = other) ∨
      ∃ head first second rest, word = Word.mk head (first :: second :: rest) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => exact Or.inl (fun other _ same => singletonRigid head other same)
      | cons first rest =>
          cases rest with
          | nil =>
              have different : head ≠ first := by
                intro equal
                exact fresh (by simp [equal])
              exact Or.inl (fun other otherFresh same => simplePairRigid head first different other otherFresh same)
          | cons second rest => exact Or.inr ⟨head, first, second, rest, rfl⟩

theorem simpleConverse (left right : Word Nat)
    (leftValid : (Identity.mk left right).SatisfiedBy leftTable.semigroup)
    (rightValid : (Identity.mk left right).SatisfiedBy rightTable.semigroup)
    (fresh : left.head ∉ left.tail) : Derives basis left right := by
  have rightFacts := sameHeadOfSimple (Identity.mk left right) leftValid fresh
  have headEqual : right.head = left.head := rightFacts.1
  have rightFresh : right.head ∉ right.tail := by
    rw [headEqual]
    exact rightFacts.2
  have leftFreshAsRight : right.head ∉ left.tail := by
    rw [headEqual]
    exact fresh
  have same := SemigroupBasis.CoRoots.S5_303.valid_signature (Identity.mk left right) rightValid
  rcases simpleRigidOrLong left fresh with rigid | ⟨head, first, second, rest, leftShape⟩
  · rw [rigid right rightFacts.2 same]
    exact Derives.refl _
  · rcases simpleRigidOrLong right rightFresh with rigid | ⟨otherHead, otherFirst, otherSecond, otherRest, rightShape⟩
    · rw [rigid left leftFreshAsRight same.symm]
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

/-- No rank/length bound, extra law, or unproved normalizer parameter remains. -/
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

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection
