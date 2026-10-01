import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Order6.FactorPairJoin
import SemigroupBasis.Order6Subdirect.Common

/-!
# Day-7 authenticated `S3_16 × S5_997` finite obligations, rank 004

Displayed basis SHA-256: `d0145658c146c21f96f503c662b3876f19cb12db0779901c2745ba7a4e305a18`.
This recovered collision-safe prefix proves finite-table soundness only.
Conditional endpoint shells were intentionally excluded.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002FiniteBase

open SemigroupBasis

abbrev leftTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S3_16.table

def rightTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_997.table

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- `x = xxx`; independently normalized variables: x->0. -/
def law00 : Identity Nat :=
  ⟨w 0 [], w 0 [0, 0]⟩
/-- `xxy = xyyxy`; independently normalized variables: x->0, y->1. -/
def law01 : Identity Nat :=
  ⟨w 0 [0, 1], w 0 [1, 1, 0, 1]⟩
/-- `xxyxy = xyxxy`; independently normalized variables: x->0, y->1. -/
def law02 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 1], w 0 [1, 0, 0, 1]⟩
/-- `xxyyx = xyxyx`; independently normalized variables: x->0, y->1. -/
def law03 : Identity Nat :=
  ⟨w 0 [0, 1, 1, 0], w 0 [1, 0, 1, 0]⟩
/-- `cbacca = cbcaca`; independently normalized variables: c->0, b->1, a->2. -/
def law04 : Identity Nat :=
  ⟨w 0 [1, 2, 0, 0, 2], w 0 [1, 0, 2, 0, 2]⟩
/-- `bccbac = bbccac`; independently normalized variables: b->0, c->1, a->2. -/
def law05 : Identity Nat :=
  ⟨w 0 [1, 1, 0, 2, 1], w 0 [0, 1, 1, 2, 1]⟩
/-- `aacbca = acabca`; independently normalized variables: a->0, c->1, b->2. -/
def law06 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1, 0], w 0 [1, 0, 2, 1, 0]⟩
/-- `cbaaca = cbca`; independently normalized variables: c->0, b->1, a->2. -/
def law07 : Identity Nat :=
  ⟨w 0 [1, 2, 2, 0, 2], w 0 [1, 0, 2]⟩
/-- `ccacba = caccba`; independently normalized variables: c->0, a->1, b->2. -/
def law08 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2, 1], w 0 [1, 0, 0, 2, 1]⟩
/-- `aabcab = abacab`; independently normalized variables: a->0, b->1, c->2. -/
def law09 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 0, 1], w 0 [1, 0, 2, 0, 1]⟩
/-- `ccbacb = cbcacb`; independently normalized variables: c->0, b->1, a->2. -/
def law10 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 0, 1], w 0 [1, 0, 2, 0, 1]⟩
/-- `ccbcab = cbccab`; independently normalized variables: c->0, b->1, a->2. -/
def law11 : Identity Nat :=
  ⟨w 0 [0, 1, 0, 2, 1], w 0 [1, 0, 0, 2, 1]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11]

def displayedBasisSHA256 : String :=
  "d0145658c146c21f96f503c662b3876f19cb12db0779901c2745ba7a4e305a18"

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

private def toFin05 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin06 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

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

private def toFin11 : Nat → Fin 3
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


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem leftModels : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002FiniteBase
