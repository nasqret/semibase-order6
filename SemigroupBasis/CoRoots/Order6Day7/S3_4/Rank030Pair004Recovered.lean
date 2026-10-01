import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase

/-!
# Explicitly reviewed ordinal-qualified collision recovery: S3_4 x S5_83

Original frozen full-source SHA-256: `34cd85cd820b72aa0b70e19ca59b20dabf646c098e0a11077414449b5103db15`.
Displayed basis SHA-256: `8b73087c957c5d8c056a232eef6271c47cb0f0de2250815873bca8422b0ef24e`.
Each conditional shell below is copied byte-for-byte from that independently
reconstructed original; it still requires an externally proved unrestricted
IntersectionNormalizer and asserts no endpoint without that premise.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered

open SemigroupBasis

abbrev leftTable : FiniteTable := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase.leftTable

abbrev rightTable : FiniteTable := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase.rightTable

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase.basis

theorem leftModels : Models leftTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase.leftModels

theorem rightModels : Models rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004FiniteBase.rightModels

namespace S6_2638

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
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (0 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (1 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (0 : Fin 3)
  else if value = 4 then (2 : Fin 3)
  else (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (0 : Fin 5)
  else if value = 2 then (1 : Fin 5)
  else if value = 3 then (3 : Fin 5)
  else if value = 4 then (2 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (2 : Fin 6)
  else if value = 2 then (4 : Fin 6)
  else if value = 3 then (3 : Fin 6)
  else (5 : Fin 6)

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

end S6_2638
end SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered
