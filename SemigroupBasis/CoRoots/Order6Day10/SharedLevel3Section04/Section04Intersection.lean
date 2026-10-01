import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Replay
import SemigroupBasis.Subdirect

/-! Two actual-factor converses for ONE unchanged B8. Lengths one and two
stay literal; longer words use full support, their first two letters, and
the proved guarded replay with a terminal head. No bounded descriptor is
assumed and no bare S5_830 rewrite is imported into B8. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Intersection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Replay

abbrev basis := Section04Replay.basis
abbrev leftTable := Section04Replay.leftTable
abbrev rightTable := Section04Replay.rightTable
abbrev alternateLeftTable := Section04Replay.alternateLeftTable
abbrev alternateRightTable := Section04Replay.alternateRightTable

def signaturePrefix : CoRoots.S5_526.FirstPairSignature → List Nat
  | .singleton first => [first]
  | .pair first second => [first, second]
  | .long first second => [first, second]

theorem signaturePrefix_eq (word : Word Nat) :
    signaturePrefix (CoRoots.S5_526.signature word) = CoRoots.S5_830.FirstTwo word := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => rfl
  | cons second rest => cases rest <;> rfl

theorem lengthClass_long_iff (word : Word Nat) :
    CoRoots.S5_526.lengthClass word = .long ↔ 3 ≤ word.toList.length := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => simp [CoRoots.S5_526.lengthClass, Word.toList]
  | cons second rest =>
      cases rest <;> simp [CoRoots.S5_526.lengthClass, Word.toList]

theorem firstTwo_eq_short (word : Word Nat) (short : word.toList.length ≤ 2) :
    CoRoots.S5_830.FirstTwo word = word.toList := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => rfl
  | cons second rest =>
      cases rest with
      | nil => rfl
      | cons third more => simp [Word.toList] at short

theorem derivesOfData (left right : Word Nat)
    (lengths : CoRoots.S5_526.lengthClass left = CoRoots.S5_526.lengthClass right)
    (prefixEq : CoRoots.S5_830.FirstTwo left = CoRoots.S5_830.FirstTwo right)
    (support : CoRoots.S5_830.SameSupport left right) : Derives basis left right := by
  by_cases leftLong : 3 ≤ left.toList.length
  · have rightLong : 3 ≤ right.toList.length := by
      apply (lengthClass_long_iff right).mp
      rw [← lengths]
      exact (lengthClass_long_iff left).mpr leftLong
    exact derivesOfLongData left right leftLong rightLong prefixEq support
  · have rightNotLong : ¬3 ≤ right.toList.length := by
      intro rightLong
      apply leftLong
      apply (lengthClass_long_iff left).mp
      rw [lengths]
      exact (lengthClass_long_iff right).mpr rightLong
    have same : left = right := by
      apply Word.toList_injective
      calc
        left.toList = CoRoots.S5_830.FirstTwo left := (firstTwo_eq_short left (by omega)).symm
        _ = CoRoots.S5_830.FirstTwo right := prefixEq
        _ = right.toList := firstTwo_eq_short right (by omega)
    rw [same]
    exact Derives.refl _

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup → identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity semilatticeValid pairValid
  have prefixEq : CoRoots.S5_830.FirstTwo identity.lhs = CoRoots.S5_830.FirstTwo identity.rhs := by
    have same := congrArg signaturePrefix (CoRoots.S5_526.valid_signature_eq identity pairValid)
    simpa only [signaturePrefix_eq] using same
  exact derivesOfData identity.lhs identity.rhs
    (CoRoots.S5_526.valid_lengthClass_eq identity pairValid) prefixEq
    (Examples.semilatticeValid_support_eq identity semilatticeValid)

def quadraticLengthCode : CoRoots.S5_526.LengthClass → Fin 3
  | .singleton => 2
  | .pair => 1
  | .long => 0

theorem quadraticLengthCode_injective : Function.Injective quadraticLengthCode := by
  intro left right equal
  cases left <;> cases right <;> simp [quadraticLengthCode] at equal ⊢

theorem quadraticLength_eval (word : Word Nat) :
    alternateLeftTable.semigroup.eval (fun _ => (2 : Fin 3)) word =
      quadraticLengthCode (CoRoots.S5_526.lengthClass word) := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => rfl
  | cons second rest =>
      cases rest with
      | nil => rfl
      | cons third more =>
          exact Examples.projectionQuadraticEval_long (fun _ => (2 : Fin 3)) first second third more

theorem alternateLengthClass (identity : Identity Nat)
    (valid : identity.SatisfiedBy alternateLeftTable.semigroup) :
    CoRoots.S5_526.lengthClass identity.lhs = CoRoots.S5_526.lengthClass identity.rhs := by
  have evaluated := valid (fun _ => (2 : Fin 3))
  rw [quadraticLength_eval, quadraticLength_eval] at evaluated
  exact quadraticLengthCode_injective evaluated

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
  intro identity quadraticValid prefixSupportValid
  have replayValid := alternateRight_valid_replay identity prefixSupportValid
  exact derivesOfData identity.lhs identity.rhs (alternateLengthClass identity quadraticValid)
    (CoRoots.S5_830.valid_firstTwo identity replayValid) (CoRoots.S5_830.valid_support identity replayValid)

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

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Intersection
