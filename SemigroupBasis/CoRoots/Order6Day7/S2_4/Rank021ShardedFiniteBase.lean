import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Order6.FactorPairJoin
import SemigroupBasis.Order6Subdirect.Common
import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021SixVariableFiniteShard

/-!
# Day-7 authenticated `S2_4 × S5_402op` finite obligations, rank 021

Displayed basis SHA-256: `7ec16079273858e127e48f8afc6344408a63498f2f90a3f5c640953294bc4142`.
This memory-bounded finite-only prefix reuses 25 authenticated table shards.
Conditional endpoint shells were intentionally excluded.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase

open SemigroupBasis

abbrev leftTable : FiniteTable := SemigroupBasis.Generated.S2_4.table

def rightTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.Catalogue.S5_402.table

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- `xxx = xx`; independently normalized variables: x->0. -/
def law00 : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0]⟩
/-- `xxyx = xyx`; independently normalized variables: x->0, y->1. -/
def law01 : Identity Nat :=
  ⟨w 0 [0, 1, 0], w 0 [1, 0]⟩
/-- `xyxx = xyx`; independently normalized variables: x->0, y->1. -/
def law02 : Identity Nat :=
  ⟨w 0 [1, 0, 0], w 0 [1, 0]⟩
/-- `hxxkyytzz = hyytxxkzz`; independently normalized variables: h->0, x->1, k->2, y->3, t->4, z->5. -/
def law03 : Identity Nat :=
  ⟨w 0 [1, 1, 2, 3, 3, 4, 5, 5], w 0 [3, 3, 4, 1, 1, 2, 5, 5]⟩
/-- `cabcac = cacabc`; independently normalized variables: c->0, a->1, b->2. -/
def law04 : Identity Nat :=
  ⟨w 0 [1, 2, 0, 1, 0], w 0 [1, 0, 1, 2, 0]⟩
/-- `cacac = caac`; independently normalized variables: c->0, a->1. -/
def law05 : Identity Nat :=
  ⟨w 0 [1, 0, 1, 0], w 0 [1, 1, 0]⟩
/-- `abba = ababa`; independently normalized variables: a->0, b->1. -/
def law06 : Identity Nat :=
  ⟨w 0 [1, 1, 0], w 0 [1, 0, 1, 0]⟩
/-- `caabcb = caacbb`; independently normalized variables: c->0, a->1, b->2. -/
def law07 : Identity Nat :=
  ⟨w 0 [1, 1, 2, 0, 2], w 0 [1, 1, 0, 2, 2]⟩
/-- `bacbc = bcbabc`; independently normalized variables: b->0, a->1, c->2. -/
def law08 : Identity Nat :=
  ⟨w 0 [1, 2, 0, 2], w 0 [2, 0, 1, 0, 2]⟩
/-- `aaccb = acacb`; independently normalized variables: a->0, c->1, b->2. -/
def law09 : Identity Nat :=
  ⟨w 0 [0, 1, 1, 2], w 0 [1, 0, 1, 2]⟩
/-- `babacc = bbacac`; independently normalized variables: b->0, a->1, c->2. -/
def law10 : Identity Nat :=
  ⟨w 0 [1, 0, 1, 2, 2], w 0 [0, 1, 2, 1, 2]⟩
/-- `cbbca = cbcbca`; independently normalized variables: c->0, b->1, a->2. -/
def law11 : Identity Nat :=
  ⟨w 0 [1, 1, 0, 2], w 0 [1, 0, 1, 0, 2]⟩
/-- `babcc = bbacc`; independently normalized variables: b->0, a->1, c->2. -/
def law12 : Identity Nat :=
  ⟨w 0 [1, 0, 2, 2], w 0 [0, 1, 2, 2]⟩
/-- `cabcb = ccabb`; independently normalized variables: c->0, a->1, b->2. -/
def law13 : Identity Nat :=
  ⟨w 0 [1, 2, 0, 2], w 0 [0, 1, 2, 2]⟩
/-- `aacbb = abacb`; independently normalized variables: a->0, c->1, b->2. -/
def law14 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 2], w 0 [2, 0, 1, 2]⟩
/-- `abccb = acbcb`; independently normalized variables: a->0, b->1, c->2. -/
def law15 : Identity Nat :=
  ⟨w 0 [1, 2, 2, 1], w 0 [2, 1, 2, 1]⟩
/-- `cbaba = cabba`; independently normalized variables: c->0, b->1, a->2. -/
def law16 : Identity Nat :=
  ⟨w 0 [1, 2, 1, 2], w 0 [2, 1, 1, 2]⟩
/-- `babcb = bcbab`; independently normalized variables: b->0, a->1, c->2. -/
def law17 : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [2, 0, 1, 0]⟩
/-- `babca = bbcaa`; independently normalized variables: b->0, a->1, c->2. -/
def law18 : Identity Nat :=
  ⟨w 0 [1, 0, 2, 1], w 0 [0, 2, 1, 1]⟩
/-- `ccbaa = cacba`; independently normalized variables: c->0, b->1, a->2. -/
def law19 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 2], w 0 [2, 0, 1, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15, law16, law17, law18, law19]

def displayedBasisSHA256 : String :=
  "7ec16079273858e127e48f8afc6344408a63498f2f90a3f5c640953294bc4142"

private def toFin00 : Nat → Fin 1
  | _ => 0

private def toFin01 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin02 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin03 : Nat → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 5

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

private def toFin11 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin12 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin13 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin14 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin15 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin16 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin17 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin18 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def toFin19 : Nat → Fin 3
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
    SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021SixVariableFiniteShard.longIdentity_valid
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law17_valid : law17.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law17.map toFin17).map Fin.val = law17 := by
    decide
  have finiteValid :
      (law17.map toFin17).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law17.map toFin17) (by decide)
  have lifted :
      ((law17.map toFin17).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law17.map toFin17).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law17_valid : law17.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law17.map toFin17).map Fin.val = law17 := by
    decide
  have finiteValid :
      (law17.map toFin17).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law17.map toFin17) (by decide)
  have lifted :
      ((law17.map toFin17).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law17.map toFin17).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law18_valid : law18.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law18.map toFin18).map Fin.val = law18 := by
    decide
  have finiteValid :
      (law18.map toFin18).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law18.map toFin18) (by decide)
  have lifted :
      ((law18.map toFin18).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law18.map toFin18).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law18_valid : law18.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law18.map toFin18).map Fin.val = law18 := by
    decide
  have finiteValid :
      (law18.map toFin18).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law18.map toFin18) (by decide)
  have lifted :
      ((law18.map toFin18).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law18.map toFin18).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem left_law19_valid : law19.SatisfiedBy leftTable.semigroup := by
  have roundTrip :
      (law19.map toFin19).map Fin.val = law19 := by
    decide
  have finiteValid :
      (law19.map toFin19).SatisfiedBy leftTable.semigroup :=
    leftTable.checkIdentityFused_sound
      (law19.map toFin19) (by decide)
  have lifted :
      ((law19.map toFin19).map Fin.val).SatisfiedBy leftTable.semigroup :=
    (law19.map toFin19).satisfiedBy_map Fin.val leftTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem right_law19_valid : law19.SatisfiedBy rightTable.semigroup := by
  have roundTrip :
      (law19.map toFin19).map Fin.val = law19 := by
    decide
  have finiteValid :
      (law19.map toFin19).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (law19.map toFin19) (by decide)
  have lifted :
      ((law19.map toFin19).map Fin.val).SatisfiedBy rightTable.semigroup :=
    (law19.map toFin19).satisfiedBy_map Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem leftModels : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact left_law17_valid
  · exact left_law18_valid
  · exact left_law19_valid


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact right_law17_valid
  · exact right_law18_valid
  · exact right_law19_valid

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase
