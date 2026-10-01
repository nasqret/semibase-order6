import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802OppositeNormal

/-!
# Exact endpoint for S6_13666

The catalogue representative is a subdirect product of `S3_13` and
`S5_802^op`. The eight-law fixed-head intersection basis therefore gives the
recorded complete basis for `S6_13666`.
-/

namespace SemigroupBasis.Order6.S6_13666

open SemigroupBasis

def targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.basis

/-- Exact zero-based multiplication for catalogue representative `S6_13666`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 3 => 1
  | 1, 4 => 1
  | 1, 5 => 1
  | 2, _ => 2
  | 3, 3 => 3
  | 3, 4 => 3
  | 3, 5 => 5
  | 4, 1 => 1
  | 4, 3 => 3
  | 4, 4 => 4
  | 4, 5 => 5
  | 5, 3 => 3
  | 5, 4 => 5
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c763e34835f767e071b8bb7f6af61bdeb3831565fa4a52a70e36590f6c4ba780"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 2, 2, 2],
   [3, 3, 3, 3, 3, 3],
   [1, 1, 1, 4, 4, 6],
   [1, 2, 1, 4, 5, 6],
   [1, 1, 1, 4, 6, 6]]

/-- The hand-written finite table is exactly the committed Smallsemi row. -/
theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def leftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 2 => 2
  | 4 => 1
  | _ => 0

def leftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 4
  | 2 => 2
  | _ => 0

def ontoLeft :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.leftFactor where
  toFun := leftMap
  map_mul := by decide
  preimage := leftSection
  right_inverse := by decide

def rightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 3
  | _ => 0

def rightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | 4 => 4
  | _ => 0

def ontoRight :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.rightFactor where
  toFun := rightMap
  map_mul := by decide
  preimage := rightSection
  right_inverse := by decide

private def valuesOneBased {n m : Nat} (map : Fin n -> Fin m) : List Nat :=
  List.ofFn fun value => (map value).val + 1

def leftMapValuesOneBased := valuesOneBased leftMap
def rightMapValuesOneBased := valuesOneBased rightMap
def leftSectionValuesOneBased := valuesOneBased leftSection
def rightSectionValuesOneBased := valuesOneBased rightSection

def leftFactorId : String := "S3_13"
def leftFactorOrientation : String := "direct"
def rightFactorId : String := "S5_802"
def rightFactorOrientation : String := "opposite"

theorem factor_binding_certificate :
    leftFactorId = "S3_13" /\
    leftFactorOrientation = "direct" /\
    rightFactorId = "S5_802" /\
    rightFactorOrientation = "opposite" /\
    leftMapValuesOneBased = [1, 1, 3, 1, 2, 1] /\
    rightMapValuesOneBased = [1, 2, 1, 3, 5, 4] /\
    leftSectionValuesOneBased = [1, 5, 3] /\
    rightSectionValuesOneBased = [1, 2, 4, 6, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.leftFactor
      SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.rightFactor where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional complete basis theorem for the exact `S6_13666` table. -/
theorem representative_basis : BasisFor table.semigroup targetBasis := by
  simpa [targetBasis] using
    SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.intersectionBasis.basisFor
      subdirectPair

end SemigroupBasis.Order6.S6_13666
