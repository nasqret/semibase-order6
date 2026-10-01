import SemigroupBasis.Generated.Order6FactorPairS2_4S5_209Corrected.Shared

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS2_4S5_209Corrected.S6_5659

open SemigroupBasis

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_5659`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 4 => 1
  | 1, 5 => 1
  | 3, 3 => 1
  | 3, 4 => 3
  | 3, 5 => 3
  | 4, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 4, 4 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 5
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
       [0, 0, 0, 0, 1, 1],
       [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 3, 3],
       [0, 1, 2, 3, 4, 4],
       [0, 1, 2, 3, 5, 5]] := by
  decide

def tableSHA256 : String :=
  "12d17aef8cc2c3fb2d4dd9dd776d90974cda0631fb93d0099dc048218558dd83"

def familyID : String := "o6fp-d4b8fb9aa3355737"
def contractFamilyID : String := "O6F_0007"
def witnessDescriptorSHA256 : String :=
  "5fed0351de3acd1bbdf7bbc766a373660f74a35ef0baac25f06674d9876b44ca"
def proofRoute : String :=
  "s3-15-s5-209-factor-pair-join-normal-form"

/-- Quotient blocks `[1,2,3,4]`, `[5]`, `[6]`, identified with the stored
left-normal-band representative `S3_15`. -/
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

def ontoS3 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by
    intro value
    exact by decide +revert

/-- Quotient blocks `[1]`, `[2]`, `[3]`, `[4]`, `[5,6]`, identified with
the stored catalogue representative `S5_209`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 4
  else if value = 5 then 4
  else 0

def s5Section (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 4

def s5MapValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 => (s5Map value).val

def s5SectionValuesZeroBased : List Nat :=
  List.ofFn fun value : Fin 5 => (s5Section value).val

theorem s5ValuesZeroBased_certificate :
    s5MapValuesZeroBased = [0, 1, 2, 3, 4, 4] ∧
      s5SectionValuesZeroBased = [0, 1, 2, 3, 4] := by
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
      [(0, 0), (0, 1), (0, 2), (0, 3), (1, 4), (2, 4)] := by
  decide

/-- The two quotient kernels have diagonal intersection. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup
    SemigroupBasis.Generated.S5_209.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Completeness.correctedBasis

/-- Unconditional arbitrary-support basis endpoint using the corrected
eleven-law factor-pair intersection theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Completeness.intersectionS3_15S5_209.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS2_4S5_209Corrected.S6_5659
