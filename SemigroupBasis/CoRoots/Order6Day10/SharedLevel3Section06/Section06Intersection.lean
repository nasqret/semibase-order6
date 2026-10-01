import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Replay
import SemigroupBasis.Subdirect

/-! The unrestricted two-factor converses use actual left-zero head
separation and the existing complete affine theories, transported through
the explicit B6 prefix replay. No finite key is a completeness premise. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Intersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Replay

abbrev basis := Section06Replay.basis
abbrev leftTable := Section06Replay.leftTable
abbrev rightTable := Section06Replay.rightTable
abbrev alternateLeftTable := Section06Replay.alternateLeftTable
abbrev alternateRightTable := Section06Replay.alternateRightTable

theorem left_head (identity : Identity Nat) (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  let valuation : Nat → Fin 2 := fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  change Examples.leftZeroTwo.semigroup.eval valuation identity.lhs =
    Examples.leftZeroTwo.semigroup.eval valuation identity.rhs at evaluated
  rw [Examples.leftZeroTwo_eval, Examples.leftZeroTwo_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  simp [valuation, Ne.symm different] at evaluated

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity headValid affineValid
  exact derivesOfHeadAndAffine identity.lhs identity.rhs (left_head identity headValid)
    (rightBasis_complete.2 identity affineValid)

def AlternateComplete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy alternateLeftTable.semigroup → identity.SatisfiedBy alternateRightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem completeAlternate : AlternateComplete := by
  intro identity headValid affineValid
  exact derivesOfHeadAndAffine identity.lhs identity.rhs (left_head identity headValid)
    (alternateRightBasis_complete.2 identity affineValid)

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
      identity.SatisfiedBy alternateLeftTable.semigroup ∧ identity.SatisfiedBy alternateRightTable.semigroup := by
  constructor
  · intro derived
    exact ⟨fun valuation => derived.sound modelsAlternateLeft valuation, fun valuation => derived.sound modelsAlternateRight valuation⟩
  · intro valid
    exact completeAlternate identity valid.1 valid.2

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

def alternateIntersectionBasis : IntersectionBasis alternateLeftTable.semigroup alternateRightTable.semigroup basis where
  leftModels := modelsAlternateLeft
  rightModels := modelsAlternateRight
  complete := completeAlternate

abbrev FinitePair (target : FiniteTable) := SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup
abbrev AlternateFinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup alternateLeftTable.semigroup alternateRightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair
theorem basisForOfAlternateFinitePair (target : FiniteTable) (pair : AlternateFinitePair target) :
    BasisFor target.semigroup basis := alternateIntersectionBasis.basisFor pair
theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) := intersectionBasis.oppositeReversed.basisFor pair
theorem basisForOppositeOfAlternateFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite alternateLeftTable.semigroup.opposite alternateRightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) := alternateIntersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Intersection
