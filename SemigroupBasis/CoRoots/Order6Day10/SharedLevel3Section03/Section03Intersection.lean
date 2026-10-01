import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Normalization
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Subdirect

/-! Unrestricted B13 completeness: actual lower phase profiles align the
canonical lists, and the actual upper factor fixes the initial-repeat bit. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Normalization

abbrev basis := Section03Replay.basis
abbrev leftTable := Section03Replay.leftTable
abbrev rightTable := Section03Replay.rightTable
abbrev alternateRightTable := Section03Replay.alternateRightTable

theorem simpleInitial_iff (word : Word Nat) (letter : Nat) :
    CoRoots.S5_107.SimpleInitial word letter ↔ word.head = letter ∧ letter ∉ word.tail := by
  cases word with
  | mk head tail =>
      by_cases equal : head = letter
      · subst head
        simp [CoRoots.S5_107.SimpleInitial, CoRoots.S5_107.SimpleIn, Word.toList, List.count_eq_zero]
      · simp [CoRoots.S5_107.SimpleInitial, equal]

theorem initialMarkerValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) (letter : Nat) :
    (identity.lhs.head = letter ∧ letter ∉ identity.lhs.tail) ↔
      (identity.rhs.head = letter ∧ letter ∉ identity.rhs.tail) := by
  have actual : identity.SatisfiedBy finalMarkerThree.semigroup.opposite := valid
  have same := CoRoots.S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff identity actual letter
  simpa only [simpleInitial_iff] using same

theorem repeatedRight (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup)
    (repeated : identity.lhs.head ∈ identity.lhs.tail) : identity.rhs.head ∈ identity.rhs.tail := by
  apply Decidable.byContradiction
  intro missing
  have simpleLeft := (initialMarkerValid identity valid identity.rhs.head).mpr ⟨rfl, missing⟩
  exact simpleLeft.2 (by simpa only [← simpleLeft.1] using repeated)

theorem repeatBoolValid (identity : Identity Nat) (valid : identity.SatisfiedBy leftTable.semigroup) :
    decide (identity.lhs.head ∈ identity.lhs.tail) = decide (identity.rhs.head ∈ identity.rhs.tail) := by
  by_cases leftRepeated : identity.lhs.head ∈ identity.lhs.tail
  · have rightRepeated := repeatedRight identity valid leftRepeated
    simp [leftRepeated, rightRepeated]
  · have rightFresh : identity.rhs.head ∉ identity.rhs.tail := by
      intro rightRepeated
      exact leftRepeated (repeatedRight ⟨identity.rhs, identity.lhs⟩
        (fun valuation => (valid valuation).symm) rightRepeated)
    simp [leftRepeated, rightFresh]

theorem lowerValid_heads (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have order := CoRoots.S5_831.valid_firstOccurrenceSequence_eq identity valid
  have heads := congrArg (fun letters : List Nat => letters.head?) order
  simpa [Word.toList, firstOccurrenceSequence] using heads

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity markerValid lowerValid
  have equal := canonical_eq_of_data (lowerValid_heads identity lowerValid)
    (CoRoots.S5_831.valid_samePhaseOccupancySignature identity lowerValid)
    (repeatBoolValid identity markerValid)
  have left := Section03Normalization.derivesCanonical identity.lhs
  have right := Section03Normalization.derivesCanonical identity.rhs
  rw [equal] at left
  exact (left.trans right.symm).toWord

def AlternateComplete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy alternateRightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem completeAlternate : AlternateComplete := by
  intro identity markerValid alternateValid
  have derived := alternateLowerBasis_complete.2 identity alternateValid
  have lowerValid : identity.SatisfiedBy rightTable.semigroup :=
    fun valuation => derived.sound lowerBasis_complete.1 valuation
  exact complete identity markerValid lowerValid

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

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Intersection
