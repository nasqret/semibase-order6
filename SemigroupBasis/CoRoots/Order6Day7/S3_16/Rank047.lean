import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Order6.FactorPairJoin
import SemigroupBasis.Order6Subdirect.Common

/-!
# Day-7 authenticated `S3_16 × S4_11` finite obligations, rank 047

Displayed basis SHA-256: `32bc7b95f90bf577df1628b15f5d1656c1dde14b75d6ed7ee0db9755ec8b0429`.
This source proves finite-table soundness and exact split-subdirect maps only.
Both endpoint theorems retain an explicit externally proved unrestricted
IntersectionNormalizer premise. It asserts no separation witness, no seed,
no unrestricted completeness, no acceptance, and no seal.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank047

open SemigroupBasis

abbrev leftTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S3_16.table

def rightTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_11.table

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- `xxy = xyx`; independently normalized variables: x->0, y->1. -/
def law00 : Identity Nat :=
  ⟨w 0 [0, 1], w 0 [1, 0]⟩
/-- `xxy = xyy`; independently normalized variables: x->0, y->1. -/
def law01 : Identity Nat :=
  ⟨w 0 [0, 1], w 0 [1, 1]⟩
/-- `xxyzt = xyzt`; independently normalized variables: x->0, y->1, z->2, t->3. -/
def law02 : Identity Nat :=
  ⟨w 0 [0, 1, 2, 3], w 0 [1, 2, 3]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02]

def displayedBasisSHA256 : String :=
  "32bc7b95f90bf577df1628b15f5d1656c1dde14b75d6ed7ee0db9755ec8b0429"

private def toFin00 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin01 : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFin02 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

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


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem leftModels : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact left_law00_valid
  · exact left_law01_valid
  · exact left_law02_valid


/-- Finite-table soundness only; unrestricted factor completeness is not asserted. -/
theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact right_law00_valid
  · exact right_law01_valid
  · exact right_law02_valid


namespace S6_5683

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
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (1 : Fin 6)
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
    if right = 0 then (5 : Fin 6)
    else if right = 1 then (5 : Fin 6)
    else if right = 2 then (5 : Fin 6)
    else if right = 3 then (5 : Fin 6)
    else if right = 4 then (5 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (0 : Fin 3)
  else if value = 4 then (1 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4)
  else if value = 1 then (1 : Fin 4)
  else if value = 2 then (2 : Fin 4)
  else if value = 3 then (3 : Fin 4)
  else if value = 4 then (0 : Fin 4)
  else (0 : Fin 4)

def ontoRightSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else (3 : Fin 6)

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

end S6_5683

namespace S6_5733

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (1 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6)
    else if right = 1 then (4 : Fin 6)
    else if right = 2 then (4 : Fin 6)
    else if right = 3 then (4 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if right = 0 then (5 : Fin 6)
    else if right = 1 then (5 : Fin 6)
    else if right = 2 then (5 : Fin 6)
    else if right = 3 then (5 : Fin 6)
    else if right = 4 then (5 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (1 : Fin 3)
  else if value = 1 then (1 : Fin 3)
  else if value = 2 then (1 : Fin 3)
  else if value = 3 then (1 : Fin 3)
  else if value = 4 then (0 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (4 : Fin 6)
  else if value = 1 then (0 : Fin 6)
  else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4)
  else if value = 1 then (1 : Fin 4)
  else if value = 2 then (2 : Fin 4)
  else if value = 3 then (3 : Fin 4)
  else if value = 4 then (0 : Fin 4)
  else (0 : Fin 4)

def ontoRightSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else (3 : Fin 6)

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

end S6_5733

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank047
