import SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Transport

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Transport.S6_9319

open SemigroupBasis

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_9319`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 2 => 1
  | 2, 3 => 1
  | 2, 4 => 1
  | 2, 5 => 2
  | 3, 2 => 1
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 5 => 2
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 2
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
       [0, 0, 1, 1, 1, 2],
       [0, 0, 1, 1, 1, 2],
       [0, 0, 1, 1, 1, 4],
       [0, 1, 2, 3, 2, 5]] := by
  decide

def tableSHA256 : String :=
  "3094f134ba21f97cab6cc71d696dd11e38bfae3c7e27571e0adf94e9f50169a8"

def familyID : String := "o6fp-76cd251bc24df36c"
def witnessDescriptorSHA256 : String :=
  "ec8d4ae27659ab8c9ac0fcb627a7e93d4a730af2572e967c356bc82efe56a11c"
def proofRoute : String :=
  "s3-6op-s5-500-factor-pair-corrected-intersection-transport"

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

/-- Quotient blocks `[1]`, `[2]`, `[3,5]`, `[4]`, `[6]`, identified with
the catalogue representative `S5_500`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 2
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
    s5MapValuesZeroBased = [0, 1, 2, 3, 2, 4] ∧
      s5SectionValuesZeroBased = [0, 1, 2, 3, 5] := by
  decide

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup where
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
      [(0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (2, 4)] := by
  decide

/-- The two quotient kernels have diagonal intersection. -/
def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_6.table.semigroup.opposite
    SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup where
  left := ontoS3Opposite
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Transport.correctedBasis

/-- Unconditional arbitrary-support basis endpoint obtained by transporting
the repaired thirteen-law intersection theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Transport.intersectionS3_6opS5_500.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorPairS3_6opS5_209Transport.S6_9319
