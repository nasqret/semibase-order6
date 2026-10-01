import SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong

namespace SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong

def mul (left right : Fin 6) : Fin 6 :=
  if left = 3 ∧ right = 2 then 1
  else if left = 4 ∧ right = 4 then 4
  else if left = 4 ∧ right = 5 then 5
  else if left = 5 then 5
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 2, 1, 1, 1],
       [1, 1, 1, 1, 5, 6],
       [6, 6, 6, 6, 6, 6]] := by
  decide

def tableSHA256 : String :=
  "87772017e41e7946b93ed8ffeb0441f9aeca1977b3224732d0b6f6cafe717967"

def componentSHA256 : String :=
  "a283cd255463788f839005a765907c549d8bcb65932afedf2bd07ff369c7f327"

def sequenceFactorID : String := "S3_16"
def sequenceOrientation : String := "direct"
def shortFactorID : String := "S4_2"
def shortOrientation : String := "direct"
def basisOrientation : String := "direct"
def memberCount : Nat := 2

def sequenceMap (value : Fin 6) : Fin 3 :=
  if value = 4 then 1 else if value = 5 then 2 else 0

def sequenceMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (sequenceMap value).val + 1

theorem sequenceMapValuesOneBased_certificate :
    sequenceMapValuesOneBased = [1, 1, 1, 1, 2, 3] := by
  decide

def sequenceSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 4 else 5

def sequenceSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 3 => (sequenceSection value).val + 1

theorem sequenceSectionValuesOneBased_certificate :
    sequenceSectionValuesOneBased = [1, 5, 6] := by
  decide

def sequenceQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := sequenceMap
  map_mul := by decide
  preimage := sequenceSection
  right_inverse := by decide

def shortMap (value : Fin 6) : Fin 4 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 0

def shortMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (shortMap value).val + 1

theorem shortMapValuesOneBased_certificate :
    shortMapValuesOneBased = [1, 2, 3, 4, 1, 1] := by
  decide

def shortSection (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else 3

def shortSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 4 => (shortSection value).val + 1

theorem shortSectionValuesOneBased_certificate :
    shortSectionValuesOneBased = [1, 2, 3, 4] := by
  decide

def shortQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := shortMap
  map_mul := by decide
  preimage := shortSection
  right_inverse := by decide

def coordinateSignaturesOneBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((sequenceMap value).val + 1, (shortMap value).val + 1)

theorem coordinateSignaturesOneBased_certificate :
    coordinateSignaturesOneBased =
      [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 1)] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_16.table.semigroup
    SemigroupBasis.Generated.S4_2.table.semigroup where
  left := sequenceQuotient
  right := shortQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s3_16_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_eq_oppositeBasis]
  exact representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367
