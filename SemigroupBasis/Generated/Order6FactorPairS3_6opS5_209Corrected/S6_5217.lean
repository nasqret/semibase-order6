import SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Corrected.Shared

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Corrected.S6_5217

open SemigroupBasis

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_5217`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 5 => 3
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 3
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
       [0, 0, 0, 0, 0, 1],
       [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 1, 3],
       [0, 0, 0, 1, 1, 4],
       [0, 1, 2, 3, 3, 5]] := by
  decide

def tableSHA256 : String :=
  "cbd12bcde32bda023aa150ce42ec278a16387c4e23341c892962ed44abf70658"

def familyID : String := "o6fp-26c708eeb801b5c8"
def contractFamilyID : String := "O6F_0014"
def proofRoute : String :=
  "s3-6op-s5-209-factor-pair-join-normal-form"

/-- Quotient blocks `[1,2,3,4]`, `[5]`, `[6]`, identified with
the opposite of the catalogue representative `S3_6`. -/
def s3Map (value : Fin 6) : Fin 3 :=
  if value = 4 then 1
  else if value = 5 then 2
  else 0

def s3Section (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 4
  else 5

def s3MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s3Map value).val

def s3SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 3 => (s3Section value).val

theorem s3ValuesZeroBased_certificate :
    s3MapValuesZeroBased = [0, 0, 0, 0, 1, 2] ∧
      s3SectionValuesZeroBased = [0, 4, 5] := by
  decide

def ontoS3Opposite : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by
    intro value
    exact by decide +revert

/-- Quotient blocks `[1]`, `[2]`, `[3]`, `[4,5]`, `[6]`, identified
with the stored catalogue representative `S5_209`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 3
  else if value = 5 then 4
  else 0

def s5Section (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 5

def s5MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s5Map value).val

def s5SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 5 => (s5Section value).val

theorem s5ValuesZeroBased_certificate :
    s5MapValuesZeroBased = [0, 1, 2, 3, 3, 4] ∧
      s5SectionValuesZeroBased = [0, 1, 2, 3, 5] := by
  decide

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S5_209.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by
    intro value
    exact by decide +revert

def coordinateSignaturesZeroBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((s3Map value).val, (s5Map value).val)

theorem coordinateSignaturesZeroBased_certificate :
    coordinateSignaturesZeroBased =
      [(0, 0), (0, 1), (0, 2), (0, 3), (1, 3), (2, 4)] := by
  decide

/-- The two recorded quotient kernels have diagonal intersection. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_6.table.semigroup.opposite
    SemigroupBasis.Generated.S5_209.table.semigroup where
  left := ontoS3Opposite
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness.correctedBasis

/-- Unconditional arbitrary-support basis endpoint using the repaired
thirteen-law factor-pair intersection theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness.correctedIntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Corrected.S6_5217
