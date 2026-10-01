import SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong

namespace SemigroupBasis.Generated.Order6FactorIntersection.FinalMarkerShortLong.S6_1052

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong

def mul (left right : Fin 6) : Fin 6 :=
  if (left = 3 ∧ right = 4) ∨ (left = 4 ∧ right = 3) then 1
  else if left = 5 ∧ right = 2 then 2
  else if left = 5 ∧ right = 5 then 5
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsZeroBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val

theorem tableRowsZeroBased_certificate :
    tableRowsZeroBased =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 1, 0, 0],
       [0, 0, 2, 0, 0, 5]] := by
  decide

def tableSHA256 : String :=
  "0d904195cb0a87285e338407b759952a4434db6a91cf855338608c88df776aef"

def componentSHA256 : String :=
  "f5ad5b05894349bf63eccb6c562707dc73b1034275f161ec4c035645f953c834"

def markerFactorID : String := "S3_6"
def markerOrientation : String := "direct"
def shortFactorID : String := "S4_3"
def shortOrientation : String := "direct"
def basisOrientation : String := "opposite"
def memberCount : Nat := 3

def markerMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1 else if value = 5 then 2 else 0

def markerMapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (markerMap value).val

theorem markerMapValuesZeroBased_certificate :
    markerMapValuesZeroBased = [0, 0, 1, 0, 0, 2] := by
  decide

def markerSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 2 else 5

def markerSectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 3 => (markerSection value).val

theorem markerSectionValuesZeroBased_certificate :
    markerSectionValuesZeroBased = [0, 2, 5] := by
  decide

def markerQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerSection
  right_inverse := by decide

def shortMap (value : Fin 6) : Fin 4 :=
  if value = 1 then 1
  else if value = 3 then 2
  else if value = 4 then 3
  else 0

def shortMapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (shortMap value).val

theorem shortMapValuesZeroBased_certificate :
    shortMapValuesZeroBased = [0, 1, 0, 2, 3, 0] := by
  decide

def shortSection (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else 4

def shortSectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 4 => (shortSection value).val

theorem shortSectionValuesZeroBased_certificate :
    shortSectionValuesZeroBased = [0, 1, 3, 4] := by
  decide

def shortQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S4_3.table.semigroup where
  toFun := shortMap
  map_mul := by decide
  preimage := shortSection
  right_inverse := by decide

def coordinateSignaturesZeroBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((markerMap value).val, (shortMap value).val)

theorem coordinateSignaturesZeroBased_certificate :
    coordinateSignaturesZeroBased =
      [(0, 0), (0, 1), (1, 0), (0, 2), (0, 3), (2, 0)] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_6.table.semigroup
    SemigroupBasis.Generated.S4_3.table.semigroup where
  left := markerQuotient
  right := shortQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s3_6_s4_3_intersectionBasis.basisFor subdirectPair

theorem opposite_reversed_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

theorem opposite_basis :
    BasisFor table.semigroup.opposite recordedOppositeBasis :=
  recordedOppositeBasisFor representative_basis

end SemigroupBasis.Generated.Order6FactorIntersection.FinalMarkerShortLong.S6_1052
