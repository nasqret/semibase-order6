import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Order6.FactorPairJoin
import SemigroupBasis.Order6Subdirect.Common

/-!
# Day-7 authenticated `S3_15op × S5_869` finite obligations, rank 028

Displayed basis SHA-256: `c9199f57be9590dbf025fdd83eef2a499c7da52f903bc24d4bd9112d4321853a`.
This recovered collision-safe prefix proves finite-table soundness only.
Conditional endpoint shells were intentionally excluded.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004FiniteBase

open SemigroupBasis

abbrev leftTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.Catalogue.S3_15.table

def rightTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_869.table

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- `xx = xxx`; independently normalized variables: x->0. -/
def law00 : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩
/-- `xxyxz = xxyz`; independently normalized variables: x->0, y->1, z->2. -/
def law01 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2], w 0 [0, 1, 2]⟩
/-- `xy = xyy`; independently normalized variables: x->0, y->1. -/
def law02 : Identity Nat :=
  ⟨w 0 [1], w 0 [1, 1]⟩
/-- `xyxyz = xyxz`; independently normalized variables: x->0, y->1, z->2. -/
def law03 : Identity Nat :=
  ⟨w 0 [1, 0, 1, 2], w 0 [1, 0, 2]⟩
/-- `xyzx = xyzyx`; independently normalized variables: x->0, y->1, z->2. -/
def law04 : Identity Nat :=
  ⟨w 0 [1, 2, 0], w 0 [1, 2, 1, 0]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04]

def displayedBasisSHA256 : String :=
  "c9199f57be9590dbf025fdd83eef2a499c7da52f903bc24d4bd9112d4321853a"

private def toFin00 : Nat → Fin 1
  | _ => 0

private def toFin01 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin02 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin03 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin04 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law00_valid : law00.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law00.map toFin00).map Fin.val = law00 := by
    decide
  have finiteValid :
      (law00.map toFin00).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law00.map toFin00) (by decide)
  have lifted :
      ((law00.map toFin00).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law00.map toFin00).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law00_valid : law00.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law00.map toFin00).map Fin.val = law00 := by
    decide
  have finiteValid :
      (law00.map toFin00).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law00.map toFin00) (by decide)
  have lifted :
      ((law00.map toFin00).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law00.map toFin00).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law01_valid : law01.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law01.map toFin01).map Fin.val = law01 := by
    decide
  have finiteValid :
      (law01.map toFin01).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law01.map toFin01) (by decide)
  have lifted :
      ((law01.map toFin01).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law01.map toFin01).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law01_valid : law01.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law01.map toFin01).map Fin.val = law01 := by
    decide
  have finiteValid :
      (law01.map toFin01).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law01.map toFin01) (by decide)
  have lifted :
      ((law01.map toFin01).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law01.map toFin01).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law02_valid : law02.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law02.map toFin02).map Fin.val = law02 := by
    decide
  have finiteValid :
      (law02.map toFin02).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law02.map toFin02) (by decide)
  have lifted :
      ((law02.map toFin02).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law02.map toFin02).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law02_valid : law02.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law02.map toFin02).map Fin.val = law02 := by
    decide
  have finiteValid :
      (law02.map toFin02).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law02.map toFin02) (by decide)
  have lifted :
      ((law02.map toFin02).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law02.map toFin02).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law03_valid : law03.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law03.map toFin03).map Fin.val = law03 := by
    decide
  have finiteValid :
      (law03.map toFin03).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law03.map toFin03) (by decide)
  have lifted :
      ((law03.map toFin03).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law03.map toFin03).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law03_valid : law03.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law03.map toFin03).map Fin.val = law03 := by
    decide
  have finiteValid :
      (law03.map toFin03).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law03.map toFin03) (by decide)
  have lifted :
      ((law03.map toFin03).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law03.map toFin03).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law04_valid : law04.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law04.map toFin04).map Fin.val = law04 := by
    decide
  have finiteValid :
      (law04.map toFin04).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law04.map toFin04) (by decide)
  have lifted :
      ((law04.map toFin04).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law04.map toFin04).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law04_valid : law04.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law04.map toFin04).map Fin.val = law04 := by
    decide
  have finiteValid :
      (law04.map toFin04).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law04.map toFin04) (by decide)
  have lifted :
      ((law04.map toFin04).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law04.map toFin04).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem leftModels : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact left_law00_valid
  · exact left_law01_valid
  · exact left_law02_valid
  · exact left_law03_valid
  · exact left_law04_valid


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact right_law00_valid
  · exact right_law01_valid
  · exact right_law02_valid
  · exact right_law03_valid
  · exact right_law04_valid

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004FiniteBase
