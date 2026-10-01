import SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035TailInsertion

/-!
# Rank035: unrestricted completeness of the exact fourteen displayed laws

Use Edmunds' complete M18 factor theory through the source-bound existing
normalizer. The simple-final stratum strips only semantic validity using
the actual identity element; the repeated-final stratum uses a common
inserted square and the proved guarded replay. No bound or extra law occurs.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035GuardedReplay
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035TailInsertion

abbrev SimpleFinalAgreement (identity : Identity Nat) : Prop :=
  ∀ letter,
    ((splitPrefixFinal identity.lhs).2 = letter ∧ letter ∉ (splitPrefixFinal identity.lhs).1) ↔
      ((splitPrefixFinal identity.rhs).2 = letter ∧ letter ∉ (splitPrefixFinal identity.rhs).1)

theorem simple_of_marker_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) : SimpleFinalAgreement identity := by
  intro letter
  exact finalMarkerValid_splitSimpleFinal_iff identity valid letter

private theorem eval_congr_on_support (first second : Nat → Fin 5) (word : Word Nat)
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    rightTable.semigroup.eval first word = rightTable.semigroup.eval second word := by
  have listEqual := SemigroupBasis.CoRoots.S5_254.m18EvalFrom_congr
    .identity first second word.toList agree
  change SemigroupBasis.CoRoots.S5_254.m18EvalList first word.toList =
    SemigroupBasis.CoRoots.S5_254.m18EvalList second word.toList at listEqual
  rw [SemigroupBasis.CoRoots.S5_254.m18EvalList_toList,
    SemigroupBasis.CoRoots.S5_254.m18EvalList_toList] at listEqual
  exact SemigroupBasis.CoRoots.S5_254.M18ListState.value.inj listEqual

theorem right_identity (value : Fin 5) : rightTable.semigroup.mul value (3 : Fin 5) = value := by
  revert value
  decide

/-- Strip a globally fresh final only from validity in the actual factor. -/
theorem simpleFinal_stem_valid (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList) (finalNotRight : final ∉ right.toList)
    (wholeValid : (Identity.mk (left ++ Word.singleton final) (right ++ Word.singleton final)).SatisfiedBy
      rightTable.semigroup) :
    (Identity.mk left right).SatisfiedBy rightTable.semigroup := by
  intro valuation
  let lifted : Nat → Fin 5 := fun letter => if letter = final then 3 else valuation letter
  have leftAgree : rightTable.semigroup.eval valuation left = rightTable.semigroup.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree : rightTable.semigroup.eval valuation right = rightTable.semigroup.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal : lifted final = 3 := by simp [lifted]
  rw [liftedFinal, right_identity, right_identity] at evaluated
  exact leftAgree.trans (evaluated.trans rightAgree.symm)

theorem prefix_support_of_support_and_simple (identity : Identity Nat)
    (support : ∀ letter, letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList)
    (simple : SimpleFinalAgreement identity) (letter : Nat) :
    letter ∈ (splitPrefixFinal identity.lhs).1 ↔ letter ∈ (splitPrefixFinal identity.rhs).1 := by
  let left := splitPrefixFinal identity.lhs
  let right := splitPrefixFinal identity.rhs
  have leftMembership (selected : Nat) :
      selected ∈ identity.lhs.toList ↔ selected ∈ left.1 ∨ selected = left.2 := by
    rw [← wordOfPrefixFinal_split identity.lhs, toList_wordOfPrefixFinal]
    simp [left]
  have rightMembership (selected : Nat) :
      selected ∈ identity.rhs.toList ↔ selected ∈ right.1 ∨ selected = right.2 := by
    rw [← wordOfPrefixFinal_split identity.rhs, toList_wordOfPrefixFinal]
    simp [right]
  change letter ∈ left.1 ↔ letter ∈ right.1
  constructor
  · intro member
    have whole := (support letter).mp ((leftMembership letter).mpr (.inl member))
    rcases (rightMembership letter).mp whole with rightMember | rightFinal
    · exact rightMember
    · apply Decidable.byContradiction
      intro missing
      have rightSimple : right.2 = letter ∧ letter ∉ right.1 := ⟨rightFinal.symm, missing⟩
      exact ((simple letter).mpr rightSimple).2 member
  · intro member
    have whole := (support letter).mpr ((rightMembership letter).mpr (.inl member))
    rcases (leftMembership letter).mp whole with leftMember | leftFinal
    · exact leftMember
    · apply Decidable.byContradiction
      intro missing
      have leftSimple : left.2 = letter ∧ letter ∉ left.1 := ⟨leftFinal.symm, missing⟩
      exact ((simple letter).mp leftSimple).2 member

theorem splitStem_nil_iff (identity : Identity Nat)
    (support : ∀ letter, letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList)
    (simple : SimpleFinalAgreement identity) :
    (splitPrefixFinal identity.lhs).1 = [] ↔ (splitPrefixFinal identity.rhs).1 = [] := by
  have prefixSupport := prefix_support_of_support_and_simple identity support simple
  constructor
  · intro leftEmpty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro letter rightMember
    have leftMember := (prefixSupport letter).mpr rightMember
    rw [leftEmpty] at leftMember
    simpa using leftMember
  · intro rightEmpty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro letter leftMember
    have rightMember := (prefixSupport letter).mp leftMember
    rw [rightEmpty] at rightMember
    simpa using rightMember

/-- Completeness for every simple-final word, at unrestricted rank and length. -/
theorem derivesSimpleFinal (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy leftTable.semigroup)
    (lowerValid : identity.SatisfiedBy rightTable.semigroup)
    (leftSimple : (splitPrefixFinal identity.lhs).2 ∉ (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs := by
  have simple := simple_of_marker_valid identity markerValid
  have same := SemigroupBasis.CoRoots.S5_254.sameM18Signature_of_valid identity lowerValid
  let final := (splitPrefixFinal identity.lhs).2
  have rightSimple := (simple final).mp ⟨rfl, leftSimple⟩
  have finalEq : (splitPrefixFinal identity.rhs).2 = final := rightSimple.1
  have rightAbsent : final ∉ (splitPrefixFinal identity.rhs).1 := rightSimple.2
  have stemsEmpty := splitStem_nil_iff identity same.support simple
  cases leftStem : (splitPrefixFinal identity.lhs).1 with
  | nil =>
      have rightStem := stemsEmpty.mp leftStem
      have leftReconstructed := wordOfPrefixFinal_split identity.lhs
      have rightReconstructed := wordOfPrefixFinal_split identity.rhs
      rw [leftStem] at leftReconstructed
      rw [rightStem] at rightReconstructed
      simp only [wordOfPrefixFinal_nil] at leftReconstructed rightReconstructed
      rw [← leftReconstructed, ← rightReconstructed, finalEq]
      exact Derives.refl _
  | cons leftFirst leftRest =>
      cases rightStem : (splitPrefixFinal identity.rhs).1 with
      | nil =>
          have impossible := stemsEmpty.mpr rightStem
          rw [leftStem] at impossible
          contradiction
      | cons rightFirst rightRest =>
          let leftWord := Word.mk leftFirst leftRest
          let rightWord := Word.mk rightFirst rightRest
          have leftFinalAbsent : final ∉ leftWord.toList := by
            simpa [final, leftWord, Word.toList, leftStem] using leftSimple
          have rightFinalAbsent : final ∉ rightWord.toList := by
            simpa [rightWord, Word.toList, rightStem] using rightAbsent
          have leftShape : leftWord ++ Word.singleton final = identity.lhs := by
            apply Word.toList_injective
            rw [Word.toList_append, Word.toList_singleton, ← wordOfPrefixFinal_split identity.lhs,
              toList_wordOfPrefixFinal, leftStem]
            rfl
          have rightShape : rightWord ++ Word.singleton final = identity.rhs := by
            apply Word.toList_injective
            rw [Word.toList_append, Word.toList_singleton, ← wordOfPrefixFinal_split identity.rhs,
              toList_wordOfPrefixFinal, rightStem, finalEq]
            rfl
          have wholeValid : (Identity.mk (leftWord ++ Word.singleton final)
              (rightWord ++ Word.singleton final)).SatisfiedBy rightTable.semigroup := by
            simpa only [leftShape, rightShape] using lowerValid
          have stemValid := simpleFinal_stem_valid final leftWord rightWord
            leftFinalAbsent rightFinalAbsent wholeValid
          have lifted := derivesSameSuffixOfLowerValid leftWord rightWord (Word.singleton final) stemValid
          simpa only [leftShape, rightShape] using lifted

/-- Completeness throughout the repeated-final stratum, using a common square. -/
theorem derivesRepeatedFinal (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy leftTable.semigroup)
    (lowerValid : identity.SatisfiedBy rightTable.semigroup)
    (leftRepeated : (splitPrefixFinal identity.lhs).2 ∈ (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs := by
  have simple := simple_of_marker_valid identity markerValid
  have rightRepeated : (splitPrefixFinal identity.rhs).2 ∈ (splitPrefixFinal identity.rhs).1 := by
    apply Decidable.byContradiction
    intro missing
    have leftSimple := (simple (splitPrefixFinal identity.rhs).2).mpr ⟨rfl, missing⟩
    exact leftSimple.2 (by simpa [leftSimple.1] using leftRepeated)
  let final := (splitPrefixFinal identity.rhs).2
  have rightCount : 2 ≤ identity.rhs.toList.count final := by
    have positive : 0 < (splitPrefixFinal identity.rhs).1.count final := List.count_pos_iff.mpr rightRepeated
    have countShape : identity.rhs.toList.count final = (splitPrefixFinal identity.rhs).1.count final + 1 := by
      rw [toList_eq_splitPrefixFinal, List.count_append]
      simp [final]
    omega
  have same := SemigroupBasis.CoRoots.S5_254.sameM18Signature_of_valid identity lowerValid
  have leftCount : 2 ≤ identity.lhs.toList.count final := (same.multiple final).mpr rightCount
  let guard := Word.singleton final ++ Word.singleton final
  have leftInsertion : Derives basis identity.lhs (identity.lhs ++ guard) := by
    simpa [guard, Word.append_assoc] using derivesAppendSeenPair identity.lhs final leftRepeated leftCount
  have rightInsertion : Derives basis identity.rhs (identity.rhs ++ guard) := by
    simpa [guard, Word.append_assoc] using derivesAppendSeenPair identity.rhs final rightRepeated rightCount
  have comparison := derivesSameSuffixOfLowerValid identity.lhs identity.rhs guard lowerValid
  exact leftInsertion.trans (comparison.trans rightInsertion.symm)

/-- The exact frozen fourteen-law unrestricted owner obligation. -/
theorem complete : Complete := by
  intro identity markerValid lowerValid
  by_cases repeated : (splitPrefixFinal identity.lhs).2 ∈ (splitPrefixFinal identity.lhs).1
  · exact derivesRepeatedFinal identity markerValid lowerValid repeated
  · exact derivesSimpleFinal identity markerValid lowerValid repeated

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  intersectionBasisOfComplete complete

def mixedIntersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup.opposite basis :=
  mixedIntersectionBasisOfComplete complete

theorem basisFor (target : FiniteTable) (pair : FinitePair target) : BasisFor target.semigroup basis :=
  intersectionBasis.basisFor pair

theorem basisForOpposite (target : FiniteTable) (pair : FinitePairOpposite target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

theorem mixedBasisFor (target : FiniteTable) (pair : MixedFinitePair target) : BasisFor target.semigroup basis :=
  mixedIntersectionBasis.basisFor pair

theorem mixedBasisForOpposite (target : FiniteTable) (pair : MixedFinitePairOpposite target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  mixedIntersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Intersection
