import SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240

/-!
# Exact endpoint for S6_3032

The two recorded quotient kernels separate all six elements.  The resulting
subdirect representation has factors `S3_8` and `S5_240`, so the corrected
nine-law intersection basis applies directly.
-/

namespace SemigroupBasis.Order6.S6_3032

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

/-- Exact zero-based multiplication for catalogue representative `S6_3032`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 4 => 1
  | 1, 5 => 1
  | 2, 4 => 1
  | 2, 5 => 1
  | 3, 4 => 1
  | 3, 5 => 2
  | 4, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 4, 4 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 3
  | 5, 4 => 4
  | 5, 5 => 4
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fa4818ad71ab54467051efe03703d6f573145609817e03edfbf1b30d2f6458ba"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

/-- The hand-written finite table is exactly the committed Smallsemi row. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 1, 2, 3],
       [1, 2, 3, 4, 5, 5],
       [1, 2, 3, 4, 5, 5]] := by
  decide

/-- Quotient blocks `[1]`, `[2,3,4]`, `[5,6]`. -/
def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | _ => 0

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 4
  | _ => 0

def ontoS3 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

/-- Quotient blocks `[1,2]`, `[3]`, `[4]`, `[5]`, `[6]`. -/
def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | _ => 0

def ontoS5 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

private def valuesZeroBased {n m : Nat} (map : Fin n -> Fin m) : List Nat :=
  List.ofFn fun value => (map value).val

def s3MapValuesZeroBased : List Nat := valuesZeroBased s3Map
def s3SectionValuesZeroBased : List Nat := valuesZeroBased s3Section
def s5MapValuesZeroBased : List Nat := valuesZeroBased s5Map
def s5SectionValuesZeroBased : List Nat := valuesZeroBased s5Section

def leftFactorID : String := "S3_8"
def leftFactorOrientation : String := "direct"
def rightFactorID : String := "S5_240"
def rightFactorOrientation : String := "direct"

theorem factorBinding_certificate :
    leftFactorID = "S3_8" /\
    leftFactorOrientation = "direct" /\
    rightFactorID = "S5_240" /\
    rightFactorOrientation = "direct" /\
    s3MapValuesZeroBased = [0, 1, 1, 1, 2, 2] /\
    s3SectionValuesZeroBased = [0, 1, 4] /\
    s5MapValuesZeroBased = [0, 0, 1, 2, 3, 4] /\
    s5SectionValuesZeroBased = [0, 2, 3, 4, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional complete basis theorem for the exact `S6_3032` table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240.intersectionBasis.basisFor
    subdirectPair

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_3032
