import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Replay
import SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics
import SemigroupBasis.Subdirect

/-! Two unrestricted actual-factor converses for the unchanged B6.
Only the table-specific S4_77 semantic theorem is reused from Rank084;
no B7 law, derivation, hypothesis or completeness theorem is used. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Intersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Replay

abbrev basis := Section05Replay.basis
abbrev leftTable := Section05Replay.leftTable
abbrev rightTable := Section05Replay.rightTable
abbrev alternateLeftTable := Section05Replay.alternateLeftTable
abbrev alternateRightTable := Section05Replay.alternateRightTable

theorem derivesOfData (left right : Word Nat)
    (prefixEq : CoRoots.S5_830.FirstTwo left = CoRoots.S5_830.FirstTwo right)
    (support : CoRoots.S5_830.SameSupport left right) (lastEq : Last left = Last right) :
    Derives basis left right := by
  rcases left with ⟨first, leftTail⟩
  rcases right with ⟨other, rightTail⟩
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil =>
          have heads : first = other := by simpa [CoRoots.S5_830.FirstTwo, Word.toList] using prefixEq
          subst other
          exact Derives.refl _
      | cons second rest => simp [CoRoots.S5_830.FirstTwo, Word.toList] at prefixEq
  | cons second rest =>
      cases rightTail with
      | nil => simp [CoRoots.S5_830.FirstTwo, Word.toList] at prefixEq
      | cons otherSecond otherRest =>
          exact derivesOfLongData _ _ (by simp [Word.toList]) (by simp [Word.toList]) prefixEq support lastEq

theorem left_reversed_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.reversed.SatisfiedBy Examples.leftNormalBandFifteen.semigroup :=
  (identity.satisfiedBy_opposite_iff_reversed Generated.S3_15.table.semigroup).mp valid

theorem left_support (identity : Identity Nat) (valid : identity.SatisfiedBy leftTable.semigroup) :
    CoRoots.S5_830.SameSupport identity.lhs identity.rhs := by
  have same := Examples.leftNormalBandFifteenValid_support_eq identity.reversed (left_reversed_valid identity valid)
  intro letter
  simpa [Identity.reversed] using same letter

theorem left_last (identity : Identity Nat) (valid : identity.SatisfiedBy leftTable.semigroup) :
    Last identity.lhs = Last identity.rhs :=
  Examples.leftNormalBandFifteenValid_head_eq identity.reversed (left_reversed_valid identity valid)

theorem right_firstTwo (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    CoRoots.S5_830.FirstTwo identity.lhs = CoRoots.S5_830.FirstTwo identity.rhs :=
  SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusSemantics.rightFirstTwo identity valid

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity supportLastValid prefixValid
  exact derivesOfData identity.lhs identity.rhs (right_firstTwo identity prefixValid)
    (left_support identity supportLastValid) (left_last identity supportLastValid)

theorem rightZero_eval (valuation : Nat → Fin 2) (word : Word Nat) :
    alternateLeftTable.semigroup.eval valuation word = valuation (Last word) := by
  change Generated.S2_4.table.semigroup.opposite.eval valuation word = valuation (Last word)
  rw [Semigroup.eval_opposite_eq_reverse]
  exact Examples.leftZeroTwo_eval valuation word.reverse

theorem alternate_last (identity : Identity Nat)
    (valid : identity.SatisfiedBy alternateLeftTable.semigroup) :
    Last identity.lhs = Last identity.rhs := by
  let valuation : Nat → Fin 2 := fun letter => if letter = Last identity.lhs then 0 else 1
  have evaluated := valid valuation
  rw [rightZero_eval, rightZero_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  simp [valuation, Ne.symm different] at evaluated

theorem alternateRight_valid_replay (identity : Identity Nat)
    (valid : identity.SatisfiedBy alternateRightTable.semigroup) :
    identity.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup := by
  have derived := alternateRightBasis_complete.2 identity valid
  exact fun valuation => derived.sound CoRoots.S5_830.models valuation

def AlternateComplete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy alternateLeftTable.semigroup → identity.SatisfiedBy alternateRightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem completeAlternate : AlternateComplete := by
  intro identity lastValid prefixSupportValid
  have replayValid := alternateRight_valid_replay identity prefixSupportValid
  exact derivesOfData identity.lhs identity.rhs (CoRoots.S5_830.valid_firstTwo identity replayValid)
    (CoRoots.S5_830.valid_support identity replayValid) (alternate_last identity lastValid)

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

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Intersection
