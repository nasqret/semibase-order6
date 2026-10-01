import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02FinalMoves
import SemigroupBasis.Subdirect

/-! Exact B13 completeness at arbitrary rank and length. Fresh-final stripping
uses the actual right identity only at the semantic level. Repeated finals
use explicit append moves and a common tail-supported suffix. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Replay
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02FinalMoves

abbrev basis := Section02Replay.basis
abbrev leftTable := Section02Replay.leftTable
abbrev rightTable := Section02Replay.rightTable
abbrev alternateRightTable := Section02Replay.alternateRightTable

theorem firstSequenceMem (selected : Nat) : ∀ letters : List Nat,
    selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal, firstSequenceMem selected rest]

theorem lowerValid_support (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  have same := CoRoots.S5_869.valid_sameSignature identity valid
  intro z
  rw [← firstSequenceMem z identity.lhs.toList, same.firstOccurrences,
    firstSequenceMem z identity.rhs.toList]

theorem lowerValid_tailSupport (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ z, z ∈ identity.lhs.tail ↔ z ∈ identity.rhs.tail := by
  have same := CoRoots.S5_869.valid_sameSignature identity valid
  have heads := same.head_eq
  have support := lowerValid_support identity valid
  rcases identity with ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  intro z
  by_cases initial : z = leftHead
  · subst z
    have repeated := same.repeatedInitial
    change decide (leftHead ∈ leftTail) = decide (leftHead ∈ rightTail) at repeated
    by_cases leftMember : leftHead ∈ leftTail <;>
      by_cases rightMember : leftHead ∈ rightTail <;>
      simp [leftMember, rightMember] at repeated ⊢
  · simpa [Word.toList, initial] using support z

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
  have foldAgreement : ∀ (letters : List Nat) (initial : Fin 5),
      (∀ letter, letter ∈ letters → first letter = second letter) →
      letters.foldl (fun current letter => rightTable.mul current (first letter)) initial =
        letters.foldl (fun current letter => rightTable.mul current (second letter)) initial := by
    intro letters
    induction letters with
    | nil => intro initial _; rfl
    | cons letter rest ih =>
        intro initial equal
        simp only [List.foldl_cons]
        rw [equal letter (List.Mem.head rest)]
        exact ih _ (fun tested member => equal tested (List.Mem.tail letter member))
  cases word with
  | mk head tail =>
      change tail.foldl (fun current letter => rightTable.mul current (first letter)) (first head) =
        tail.foldl (fun current letter => rightTable.mul current (second letter)) (second head)
      rw [agree head (by simp [Word.toList])]
      exact foldAgreement tail (second head) (fun letter member => agree letter (List.Mem.tail head member))

theorem right_identity (value : Fin 5) : rightTable.semigroup.mul value (3 : Fin 5) = value := by
  revert value
  decide

/-- This strips semantic validity only; it is not a cancellation rule. -/
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

theorem derivesSimpleFinal (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy leftTable.semigroup)
    (lowerValid : identity.SatisfiedBy rightTable.semigroup)
    (leftSimple : (splitPrefixFinal identity.lhs).2 ∉ (splitPrefixFinal identity.lhs).1) :
    Derives basis identity.lhs identity.rhs := by
  have simple := simple_of_marker_valid identity markerValid
  have support := lowerValid_support identity lowerValid
  let final := (splitPrefixFinal identity.lhs).2
  have rightSimple := (simple final).mp ⟨rfl, leftSimple⟩
  have finalEq : (splitPrefixFinal identity.rhs).2 = final := rightSimple.1
  have rightAbsent : final ∉ (splitPrefixFinal identity.rhs).1 := rightSimple.2
  have stemsEmpty := splitStem_nil_iff identity support simple
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

theorem final_mem_tail_of_repeated (word : Word Nat)
    (repeated : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1) :
    (splitPrefixFinal word).2 ∈ word.tail := by
  let final := (splitPrefixFinal word).2
  cases prefixShape : (splitPrefixFinal word).1 with
  | nil => simp [prefixShape] at repeated
  | cons head stem =>
      have shape : Word.mk head (stem ++ [final]) = word := by
        apply Word.toList_injective
        rw [← wordOfPrefixFinal_split word, toList_wordOfPrefixFinal, prefixShape]
        rfl
      change final ∈ word.tail
      rw [← shape]
      simp

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
  have rightMember : final ∈ identity.rhs.tail := final_mem_tail_of_repeated identity.rhs rightRepeated
  have leftMember : final ∈ identity.lhs.tail := (lowerValid_tailSupport identity lowerValid final).mpr rightMember
  have leftInsertion := derivesAppendRepeatedFinal identity.lhs final leftRepeated leftMember
  have rightInsertion := derivesAppendRepeatedFinal identity.rhs final rightRepeated rightMember
  have comparison := derivesSameSuffixOfLowerValid identity.lhs identity.rhs (Word.singleton final) lowerValid
  exact leftInsertion.trans (comparison.trans rightInsertion.symm)

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity markerValid lowerValid
  by_cases repeated : (splitPrefixFinal identity.lhs).2 ∈ (splitPrefixFinal identity.lhs).1
  · exact derivesRepeatedFinal identity markerValid lowerValid repeated
  · exact derivesSimpleFinal identity markerValid lowerValid repeated

def AlternateComplete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy alternateRightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem completeAlternate : AlternateComplete := by
  intro identity leftValid alternateValid
  have lowerDerived := alternateLowerBasis_complete.2 identity alternateValid
  have lowerValid : identity.SatisfiedBy rightTable.semigroup :=
    fun valuation => lowerDerived.sound lowerBasis_complete.1 valuation
  exact complete identity leftValid lowerValid

theorem derives_iff_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro derived
    exact ⟨fun valuation => derived.sound modelsLeft valuation, fun valuation => derived.sound modelsRight valuation⟩
  · intro valid
    exact complete identity valid.1 valid.2

theorem derives_iff_alternate_joint_valid (identity : Identity Nat) :
    Derives basis identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy alternateRightTable.semigroup := by
  constructor
  · intro derived
    exact ⟨fun valuation => derived.sound modelsLeft valuation, fun valuation => derived.sound modelsAlternateRight valuation⟩
  · intro valid
    exact completeAlternate identity valid.1 valid.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

def alternateIntersectionBasis : IntersectionBasis leftTable.semigroup alternateRightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsAlternateRight
  complete := completeAlternate

abbrev FinitePair (target : FiniteTable) := SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup
abbrev AlternateFinitePair (target : FiniteTable) := SubdirectPair target.semigroup leftTable.semigroup alternateRightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair
theorem basisForOfAlternateFinitePair (target : FiniteTable) (pair : AlternateFinitePair target) :
    BasisFor target.semigroup basis := alternateIntersectionBasis.basisFor pair
theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) := intersectionBasis.oppositeReversed.basisFor pair
theorem basisForOppositeOfAlternateFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite alternateRightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) := alternateIntersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Intersection
