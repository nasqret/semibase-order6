import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Order6.FactorPairJoin
import SemigroupBasis.Order6Subdirect.Common

/-!
# Day-7 authenticated `S3_11 × S5_796op` finite obligations, rank 001

Displayed basis SHA-256: `80eb7216d34f2e4f201ded3f4ba8da5c9ff4bbffeb661407e6bfe1ca2153b6f8`.
This source proves finite-table soundness and exact split-subdirect maps only.
Both endpoint theorems retain an explicit externally proved unrestricted
IntersectionNormalizer premise. It asserts no separation witness, no seed,
no unrestricted completeness, no acceptance, and no seal.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank001

open SemigroupBasis

abbrev leftTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S3_11.table

def rightTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.Catalogue.S5_796.table

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- `xx = xxxx`; independently normalized variables: x->0. -/
def law00 : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0, 0]⟩
/-- `xxxyx = xyx`; independently normalized variables: x->0, y->1. -/
def law01 : Identity Nat :=
  ⟨w 0 [0, 0, 1, 0], w 0 [1, 0]⟩
/-- `xxyx = xyxx`; independently normalized variables: x->0, y->1. -/
def law02 : Identity Nat :=
  ⟨w 0 [0, 1, 0], w 0 [1, 0, 0]⟩
/-- `xxyxx = xyx`; independently normalized variables: x->0, y->1. -/
def law03 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 0], w 0 [1, 0]⟩
/-- `xxyxz = yxyyz`; independently normalized variables: x->0, y->1, z->2. -/
def law04 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2], w 1 [0, 1, 1, 2]⟩
/-- `xxyy = xyxy`; independently normalized variables: x->0, y->1. -/
def law05 : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [1, 0, 1]⟩
/-- `xxyy = yxxy`; independently normalized variables: x->0, y->1. -/
def law06 : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 1 [0, 0, 1]⟩
/-- `xxyyz = xyyxz`; independently normalized variables: x->0, y->1, z->2. -/
def law07 : Identity Nat :=
  ⟨w 0 [0, 1, 1, 2], w 0 [1, 1, 0, 2]⟩
/-- `xxyzy = xyxzy`; independently normalized variables: x->0, y->1, z->2. -/
def law08 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 0, 2, 1]⟩
/-- `xxyzy = xzxyy`; independently normalized variables: x->0, y->1, z->2. -/
def law09 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [2, 0, 1, 1]⟩
/-- `xxyzy = yxxzy`; independently normalized variables: x->0, y->1, z->2. -/
def law10 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 1 [0, 0, 2, 1]⟩
/-- `xyx = xyxxx`; independently normalized variables: x->0, y->1. -/
def law11 : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0, 0]⟩
/-- `xyx = xyyyx`; independently normalized variables: x->0, y->1. -/
def law12 : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 1, 1, 0]⟩
/-- `xyx = yxyyx`; independently normalized variables: x->0, y->1. -/
def law13 : Identity Nat :=
  ⟨w 0 [1, 0], w 1 [0, 1, 1, 0]⟩
/-- `xyx = yyxyx`; independently normalized variables: x->0, y->1. -/
def law14 : Identity Nat :=
  ⟨w 0 [1, 0], w 1 [1, 0, 1, 0]⟩
/-- `xyx = yyyxx`; independently normalized variables: x->0, y->1. -/
def law15 : Identity Nat :=
  ⟨w 0 [1, 0], w 1 [1, 1, 0, 0]⟩
/-- `xyzx = xzyx`; independently normalized variables: x->0, y->1, z->2. -/
def law16 : Identity Nat :=
  ⟨w 0 [1, 2, 0], w 0 [2, 1, 0]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15, law16]

def displayedBasisSHA256 : String :=
  "80eb7216d34f2e4f201ded3f4ba8da5c9ff4bbffeb661407e6bfe1ca2153b6f8"

private def toFin00 : Nat → Fin 1
  | _ => 0

private def toFin01 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin02 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin03 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin04 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin05 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin06 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin07 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin08 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin09 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin10 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin11 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin12 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin13 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin14 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin15 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin16 : Nat → Fin 3
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law05_valid : law05.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law05.map toFin05).map Fin.val = law05 := by
    decide
  have finiteValid :
      (law05.map toFin05).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law05.map toFin05) (by decide)
  have lifted :
      ((law05.map toFin05).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law05.map toFin05).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law05_valid : law05.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law05.map toFin05).map Fin.val = law05 := by
    decide
  have finiteValid :
      (law05.map toFin05).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law05.map toFin05) (by decide)
  have lifted :
      ((law05.map toFin05).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law05.map toFin05).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law06_valid : law06.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law06.map toFin06).map Fin.val = law06 := by
    decide
  have finiteValid :
      (law06.map toFin06).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law06.map toFin06) (by decide)
  have lifted :
      ((law06.map toFin06).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law06.map toFin06).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law06_valid : law06.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law06.map toFin06).map Fin.val = law06 := by
    decide
  have finiteValid :
      (law06.map toFin06).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law06.map toFin06) (by decide)
  have lifted :
      ((law06.map toFin06).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law06.map toFin06).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law07_valid : law07.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law07.map toFin07).map Fin.val = law07 := by
    decide
  have finiteValid :
      (law07.map toFin07).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law07.map toFin07) (by decide)
  have lifted :
      ((law07.map toFin07).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law07.map toFin07).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law07_valid : law07.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law07.map toFin07).map Fin.val = law07 := by
    decide
  have finiteValid :
      (law07.map toFin07).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law07.map toFin07) (by decide)
  have lifted :
      ((law07.map toFin07).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law07.map toFin07).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law08_valid : law08.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law08.map toFin08).map Fin.val = law08 := by
    decide
  have finiteValid :
      (law08.map toFin08).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law08.map toFin08) (by decide)
  have lifted :
      ((law08.map toFin08).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law08.map toFin08).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law08_valid : law08.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law08.map toFin08).map Fin.val = law08 := by
    decide
  have finiteValid :
      (law08.map toFin08).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law08.map toFin08) (by decide)
  have lifted :
      ((law08.map toFin08).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law08.map toFin08).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law09_valid : law09.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law09.map toFin09).map Fin.val = law09 := by
    decide
  have finiteValid :
      (law09.map toFin09).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law09.map toFin09) (by decide)
  have lifted :
      ((law09.map toFin09).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law09.map toFin09).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law09_valid : law09.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law09.map toFin09).map Fin.val = law09 := by
    decide
  have finiteValid :
      (law09.map toFin09).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law09.map toFin09) (by decide)
  have lifted :
      ((law09.map toFin09).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law09.map toFin09).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law10_valid : law10.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law10.map toFin10).map Fin.val = law10 := by
    decide
  have finiteValid :
      (law10.map toFin10).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law10.map toFin10) (by decide)
  have lifted :
      ((law10.map toFin10).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law10.map toFin10).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law10_valid : law10.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law10.map toFin10).map Fin.val = law10 := by
    decide
  have finiteValid :
      (law10.map toFin10).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law10.map toFin10) (by decide)
  have lifted :
      ((law10.map toFin10).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law10.map toFin10).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law11_valid : law11.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law11.map toFin11).map Fin.val = law11 := by
    decide
  have finiteValid :
      (law11.map toFin11).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law11.map toFin11) (by decide)
  have lifted :
      ((law11.map toFin11).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law11.map toFin11).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law11_valid : law11.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law11.map toFin11).map Fin.val = law11 := by
    decide
  have finiteValid :
      (law11.map toFin11).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law11.map toFin11) (by decide)
  have lifted :
      ((law11.map toFin11).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law11.map toFin11).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law12_valid : law12.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law12.map toFin12).map Fin.val = law12 := by
    decide
  have finiteValid :
      (law12.map toFin12).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law12.map toFin12) (by decide)
  have lifted :
      ((law12.map toFin12).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law12.map toFin12).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law12_valid : law12.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law12.map toFin12).map Fin.val = law12 := by
    decide
  have finiteValid :
      (law12.map toFin12).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law12.map toFin12) (by decide)
  have lifted :
      ((law12.map toFin12).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law12.map toFin12).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law13_valid : law13.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law13.map toFin13).map Fin.val = law13 := by
    decide
  have finiteValid :
      (law13.map toFin13).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law13.map toFin13) (by decide)
  have lifted :
      ((law13.map toFin13).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law13.map toFin13).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law13_valid : law13.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law13.map toFin13).map Fin.val = law13 := by
    decide
  have finiteValid :
      (law13.map toFin13).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law13.map toFin13) (by decide)
  have lifted :
      ((law13.map toFin13).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law13.map toFin13).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law14_valid : law14.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law14.map toFin14).map Fin.val = law14 := by
    decide
  have finiteValid :
      (law14.map toFin14).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law14.map toFin14) (by decide)
  have lifted :
      ((law14.map toFin14).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law14.map toFin14).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law14_valid : law14.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law14.map toFin14).map Fin.val = law14 := by
    decide
  have finiteValid :
      (law14.map toFin14).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law14.map toFin14) (by decide)
  have lifted :
      ((law14.map toFin14).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law14.map toFin14).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law15_valid : law15.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law15.map toFin15).map Fin.val = law15 := by
    decide
  have finiteValid :
      (law15.map toFin15).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law15.map toFin15) (by decide)
  have lifted :
      ((law15.map toFin15).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law15.map toFin15).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law15_valid : law15.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law15.map toFin15).map Fin.val = law15 := by
    decide
  have finiteValid :
      (law15.map toFin15).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law15.map toFin15) (by decide)
  have lifted :
      ((law15.map toFin15).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law15.map toFin15).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law16_valid : law16.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law16.map toFin16).map Fin.val = law16 := by
    decide
  have finiteValid :
      (law16.map toFin16).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law16.map toFin16) (by decide)
  have lifted :
      ((law16.map toFin16).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law16.map toFin16).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law16_valid : law16.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law16.map toFin16).map Fin.val = law16 := by
    decide
  have finiteValid :
      (law16.map toFin16).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law16.map toFin16) (by decide)
  have lifted :
      ((law16.map toFin16).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law16.map toFin16).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem leftModels : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact left_law00_valid
  · exact left_law01_valid
  · exact left_law02_valid
  · exact left_law03_valid
  · exact left_law04_valid
  · exact left_law05_valid
  · exact left_law06_valid
  · exact left_law07_valid
  · exact left_law08_valid
  · exact left_law09_valid
  · exact left_law10_valid
  · exact left_law11_valid
  · exact left_law12_valid
  · exact left_law13_valid
  · exact left_law14_valid
  · exact left_law15_valid
  · exact left_law16_valid


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact right_law00_valid
  · exact right_law01_valid
  · exact right_law02_valid
  · exact right_law03_valid
  · exact right_law04_valid
  · exact right_law05_valid
  · exact right_law06_valid
  · exact right_law07_valid
  · exact right_law08_valid
  · exact right_law09_valid
  · exact right_law10_valid
  · exact right_law11_valid
  · exact right_law12_valid
  · exact right_law13_valid
  · exact right_law14_valid
  · exact right_law15_valid
  · exact right_law16_valid


namespace S6_11228

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (3 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (2 : Fin 3)
  else if value = 1 then (2 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (1 : Fin 3)
  else if value = 4 then (2 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (2 : Fin 6)
  else if value = 1 then (3 : Fin 6)
  else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (4 : Fin 5)
  else if value = 3 then (4 : Fin 5)
  else if value = 4 then (2 : Fin 5)
  else (3 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (4 : Fin 6)
  else if value = 3 then (5 : Fin 6)
  else (2 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

/-- Conditional endpoint shell: the unrestricted normalizer remains an explicit input. -/
theorem representative_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup basis :=
  IntersectionNormalizer.basisFor normalizer leftModels rightModels pair

/-- Conditional opposite-orientation shell; it does not assert an unproved normalizer. -/
theorem opposite_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_normalizer normalizer).oppositeReversed

end S6_11228

end SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank001
