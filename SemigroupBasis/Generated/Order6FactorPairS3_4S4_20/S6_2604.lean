import SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20

namespace SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_2604`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 3, 5 => 3
  | 4, 4 => 1
  | 5, 2 => 2
  | 5, 5 => 5
  | _, _ => 0

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
       [0, 0, 0, 0, 0, 3],
       [0, 0, 0, 0, 1, 0],
       [0, 0, 2, 0, 0, 5]] := by
  decide

def tableSHA256 : String :=
  "fabac90f21e579c853b9ed1b6b081586abfc33c1547eb935e84b014025725920"

def componentSHA256 : String :=
  "2495601ba5ed56b27d1a12c0c16c41926c70af4af164b760df94518ed4c828f0"

def leftFactorID : String := "S3_4"
def leftFactorOrientation : String := "direct"
def rightFactorID : String := "S4_20"
def rightFactorOrientation : String := "direct"
def basisOrientation : String := "direct"
def memberCount : Nat := 4

/-- Quotient blocks `[1,3,4,6]`, `[2]`, `[5]`. -/
def s3Map (value : Fin 6) : Fin 3 :=
  if value = 1 then 1 else if value = 4 then 2 else 0

def s3Section (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1 else 4

def s3MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s3Map value).val

def s3SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 3 => (s3Section value).val

theorem s3ValuesZeroBased_certificate :
    s3MapValuesZeroBased = [0, 1, 0, 0, 2, 0] ∧
      s3SectionValuesZeroBased = [0, 1, 4] := by
  decide

def ontoS3 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_4.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

/-- Quotient blocks `[1,2,5]`, `[3]`, `[4]`, `[6]`. -/
def s4Map (value : Fin 6) : Fin 4 :=
  if value = 2 then 1
  else if value = 3 then 2
  else if value = 5 then 3
  else 0

def s4Section (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 3
  else 5

def s4MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s4Map value).val

def s4SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 4 => (s4Section value).val

theorem s4ValuesZeroBased_certificate :
    s4MapValuesZeroBased = [0, 0, 1, 2, 0, 3] ∧
      s4SectionValuesZeroBased = [0, 2, 3, 5] := by
  decide

def ontoS4 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := s4Map
  map_mul := by decide
  preimage := s4Section
  right_inverse := by decide

def coordinateSignaturesZeroBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((s3Map value).val, (s4Map value).val)

theorem coordinateSignaturesZeroBased_certificate :
    coordinateSignaturesZeroBased =
      [(0, 0), (1, 0), (0, 1), (0, 2), (2, 0), (0, 3)] := by
  decide

/-- The two quotient kernels have diagonal intersection. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_4.table.semigroup
    SemigroupBasis.Generated.S4_20.table.semigroup where
  left := ontoS3
  right := ontoS4
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

theorem opposite_reversed_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604
