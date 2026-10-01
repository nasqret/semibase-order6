import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.S5_254Family
import SemigroupBasis.Subdirect

/-!
# Rank035: exact oriented fourteen-law system and owner interface

The two frozen contracts use the opposite of their canonical printed list.
The following words are those literal reversals, not a replacement basis.
Their common SHA256 is 87336d9de7bdfa07b13e1e43ff71c0322106c50c0104709defcbbb41783982e1.

Literature intake: Lee--Zhang (2015), Condition 9 dual holds on both actual
targets; it is finite-basability evidence, not this displayed completeness
theorem. The complete M18 factor basis is the existing formalization of
Edmunds (1977), Proposition 3.2(d). Its lower derivations must be replayed
with a genuine nonempty final guard in the new joint calculus.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 1 [0, 0, 0], Word.mk 0 [0, 1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1, 0, 0, 0], Word.mk 0 [1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 1 [2, 1, 0, 0], Word.mk 0 [0, 1, 2, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 0, 1, 0]⟩
def law05 : Identity Nat := ⟨Word.mk 1 [2, 0, 1, 0], Word.mk 0 [0, 1, 2, 1]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 1, 0], Word.mk 0 [0, 1, 1]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 2, 1, 0], Word.mk 0 [1, 2, 0, 1]⟩
def law08 : Identity Nat := ⟨Word.mk 1 [0, 0, 1], Word.mk 0 [0, 1, 1]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 0, 1], Word.mk 0 [0, 1, 1]⟩
def law10 : Identity Nat := ⟨Word.mk 1 [0, 2, 0, 1], Word.mk 0 [1, 2, 0, 1]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [1, 0, 1, 1]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 1], Word.mk 0 [0, 1, 2, 1]⟩
def law13 : Identity Nat := ⟨Word.mk 1 [0, 0, 2], Word.mk 0 [0, 1, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06,
   law07, law08, law09, law10, law11, law12, law13]

abbrev displayedBasisSHA256 : String :=
  "87336d9de7bdfa07b13e1e43ff71c0322106c50c0104709defcbbb41783982e1"

abbrev leftTable : FiniteTable := Generated.S3_6.table
abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.S5_254.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_254.basis

def rightOppositeTable : FiniteTable where
  order := 5
  mul left right := rightTable.mul right left
  assoc := by decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basis_length : basis.length = 14 := by decide

theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The two factor orientations satisfy the same exact M18 basis. -/
theorem lowerModelsOpposite : Models rightTable.semigroup.opposite lowerBasis := by
  change Models rightOppositeTable.semigroup lowerBasis
  exact FiniteCertificate.checkModels_sound rightOppositeTable lowerBasis toFinFour (by decide)

/-- Dualize the checked model; no unproved self-duality is used. -/
theorem reversedLowerModels :
    Models rightTable.semigroup (reversedBasis lowerBasis) := by
  change Models rightTable.semigroup.opposite.opposite (reversedBasis lowerBasis)
  exact lowerModelsOpposite.oppositeReversed

/-- Actual M18 opposite validity has the complete direct-factor signature. -/
theorem lower_opposite_valid_iff (identity : Identity Nat) :
    identity.SatisfiedBy rightTable.semigroup.opposite ↔
      identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro valid
    exact (SemigroupBasis.CoRoots.S5_254.oppositeBasisFor.2 identity valid).sound
      reversedLowerModels
  · intro valid
    exact (SemigroupBasis.CoRoots.S5_254.basisFor.2 identity valid).sound
      lowerModelsOpposite

theorem modelsRightOpposite : Models rightTable.semigroup.opposite basis := by
  intro identity member
  exact (lower_opposite_valid_iff identity).mpr (modelsRight identity member)

/-- One unrestricted owner converse is shared by the two existing contracts. -/
def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

abbrev FinitePairOpposite (target : FiniteTable) :=
  SubdirectPair target.semigroup.opposite
    leftTable.semigroup.opposite rightTable.semigroup.opposite

abbrev MixedFinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup.opposite

abbrev MixedFinitePairOpposite (target : FiniteTable) :=
  SubdirectPair target.semigroup.opposite
    leftTable.semigroup.opposite rightTable.semigroup.opposite.opposite

def intersectionBasisOfComplete (complete : Complete) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

def mixedIntersectionBasisOfComplete (complete : Complete) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup.opposite basis where
  leftModels := modelsLeft
  rightModels := modelsRightOpposite
  complete identity leftValid rightValid :=
    complete identity leftValid ((lower_opposite_valid_iff identity).mp rightValid)

end SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape
