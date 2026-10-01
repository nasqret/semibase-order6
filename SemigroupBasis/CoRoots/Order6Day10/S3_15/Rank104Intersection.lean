import SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank104Replay
import SemigroupBasis.Subdirect

/-!
# Exact unrestricted B7 converse for Rank104 / S6_9777

Every complete-lower axiom has both endpoints of length at least three.
Thus lower derivations either preserve a word literally or keep both words
long, including through arbitrary nonempty-word substitutions. This proves
the exact short-word rigidity needed here; no unrelated lower signature is
assumed. Long words duplicate their own actual head. The S3_15 factor equates
those heads, so the guarded lower replay closes the unrestricted converse.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank104Intersection

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis := Rank104Replay.basis
abbrev leftTable := Rank104Replay.leftTable
abbrev rightTable := Rank104Replay.rightTable
abbrev lowerBasis := Rank104Replay.lowerBasis

private theorem listLength_le_flatMap_words (letters : List Nat)
    (substitution : Nat → Word Nat) :
    letters.length ≤ (letters.flatMap (fun letter => (substitution letter).toList)).length := by
  induction letters with
  | nil => simp
  | cons letter rest induction =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have positive : 1 ≤ (substitution letter).toList.length := by
        simp [Word.toList]
      omega

theorem length_le_bind (word : Word Nat) (substitution : Nat → Word Nat) :
    word.toList.length ≤ (word.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact listLength_le_flatMap_words word.toList substitution

/-- All lower derivations preserve short words literally, even under substitution. -/
theorem lowerShortOrLong {left right : Word Nat} (derivation : Derives lowerBasis left right) :
    left = right ∨ (3 ≤ left.toList.length ∧ 3 ≤ right.toList.length) := by
  induction derivation with
  | fromBasis member =>
      have typedMember : _ ∈ Rank104Replay.lowerBasis := member
      rw [Rank104Replay.lowerBasis_literal] at typedMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at typedMember
      rcases typedMember with rfl | rfl | rfl | rfl | rfl
      all_goals exact Or.inr (by decide)
  | refl => exact Or.inl rfl
  | symm _ induction =>
      rcases induction with equal | long
      · exact Or.inl equal.symm
      · exact Or.inr ⟨long.2, long.1⟩
  | trans _ _ first second =>
      rcases first with rfl | firstLong
      · exact second
      · rcases second with rfl | secondLong
        · exact Or.inr firstLong
        · exact Or.inr ⟨firstLong.1, secondLong.2⟩
  | prepend stem _ induction =>
      rcases induction with rfl | ⟨leftLong, rightLong⟩
      · exact Or.inl rfl
      · right
        constructor <;> simp only [Word.toList_append, List.length_append] <;> omega
  | appendRight _ final induction =>
      rcases induction with rfl | ⟨leftLong, rightLong⟩
      · exact Or.inl rfl
      · right
        constructor <;> simp only [Word.toList_append, List.length_append] <;> omega
  | subst _ substitution induction =>
      rcases induction with rfl | ⟨leftLong, rightLong⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Nat.le_trans leftLong (length_le_bind _ substitution),
          Nat.le_trans rightLong (length_le_bind _ substitution)⟩

theorem shortRigid (left right : Word Nat) (short : left.toList.length ≤ 2)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) : left = right := by
  have lower : Derives lowerBasis left right :=
    Rank104Replay.lowerBasis_complete.2 (Identity.mk left right) valid
  rcases lowerShortOrLong lower with equal | long
  · exact equal
  · omega

theorem duplicateOwnHead (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third tail =>
              simpa [Word.append, Word.singleton] using
                Rank104Replay.derivesLongInsertion (Word.singleton head)
                  (Word.singleton second) (Word.mk third tail)

theorem derivesOfHeadAndLowerValid (left right : Word Nat)
    (heads : left.head = right.head)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis left right := by
  by_cases shortLeft : left.toList.length ≤ 2
  · have equal := shortRigid left right shortLeft valid
    subst right
    exact Derives.refl _
  · by_cases shortRight : right.toList.length ≤ 2
    · have reverseValid : (Identity.mk right left).SatisfiedBy rightTable.semigroup :=
        fun valuation => (valid valuation).symm
      have equal := shortRigid right left shortRight reverseValid
      subst left
      exact Derives.refl _
    · have duplicateLeft := duplicateOwnHead left (by omega)
      have duplicateRight := duplicateOwnHead right (by omega)
      have middle := Rank104Replay.derivesSamePrefixOfLowerValid left right
        (Word.singleton left.head) valid
      have duplicateRightSame : Derives basis right (Word.singleton left.head ++ right) := by
        simpa only [heads] using duplicateRight
      exact duplicateLeft.trans (middle.trans duplicateRightSame.symm)

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity leftValid rightValid
  have heads : identity.lhs.head = identity.rhs.head :=
    leftNormalBandFifteenValid_head_eq identity leftValid
  exact derivesOfHeadAndLowerValid identity.lhs identity.rhs heads rightValid

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := Rank104Replay.modelsLeft
  rightModels := Rank104Replay.modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank104Intersection
