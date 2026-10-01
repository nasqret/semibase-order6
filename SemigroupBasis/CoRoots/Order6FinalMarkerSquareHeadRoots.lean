import SemigroupBasis.CoRoots.Order6FinalMarkerSquareHead
import SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfersLayer2

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  Order6FinalMarkerSquareHead.basis

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def candidateBasisUpToOppositeSHA256 : String :=
  "5f2826110c2fe2abf0ab4f2a905014a488c932d03c3b7bcac678f08c15deb103"

namespace S6_7541

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_7541`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, 5 => 3
  | 3, _ => 3
  | 4, 1 => 1
  | 4, 4 => 4
  | 5, _ => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "244c7a7b78655359773d5ae38ea435512b8406d747aeac2e2b8d92c7d60c3478"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 4],
   [4, 4, 4, 4, 4, 4],
   [1, 2, 1, 1, 5, 1],
   [6, 6, 6, 6, 6, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

/-- Partition `[0,1,0,0,2,0]`, followed by the identity catalogue map. -/
def markerMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 1 => 1
  | 4 => 2
  | _ => 0

def markerSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 4
  | _ => 0

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerSection
  right_inverse := by
    intro value
    exact by decide +revert

/-- Partition `[0,0,1,2,3,4]`, followed by the identity catalogue map. -/
def squareHeadMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

def squareHeadSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | _ => 0

def ontoSquareHead :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup where
  toFun := squareHeadMap
  map_mul := by decide
  preimage := squareHeadSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_830.table.semigroup where
  left := ontoMarker
  right := ontoSquareHead
  jointlyInjective := by
    intro left right
    exact by decide +revert

/-- Genuine unrestricted `Nat`-level endpoint for `S6_7541`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerSquareHead.canonicalIntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_7541

namespace S6_10244

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_10244`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, 1 => 1
  | 2, 2 => 2
  | 2, 3 => 2
  | 3, 1 => 1
  | 3, 2 => 2
  | 3, 3 => 2
  | 3, 5 => 4
  | 4, _ => 4
  | 5, _ => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0451e87872ef9389c3c7e0dc4d8f6a520882d2188b8f6966c0cfe20501360ff7"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 2, 3, 3, 1, 1],
   [1, 2, 3, 3, 1, 5],
   [5, 5, 5, 5, 5, 5],
   [6, 6, 6, 6, 6, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

/-- Partition `[0,1,2,2,0,0]`, followed by the identity catalogue map. -/
def markerMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | _ => 0

def markerSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | _ => 0

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerSection
  right_inverse := by
    intro value
    exact by decide +revert

/-- Partition `[0,0,1,2,3,4]`, followed by catalogue map
`[3,1,2,4,5]` into `S5_943`. -/
def squareHeadMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 2 => 0
  | 3 => 1
  | 4 => 3
  | 5 => 4
  | _ => 2

def squareHeadSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 4
  | _ => 5

def ontoSquareHead :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup where
  toFun := squareHeadMap
  map_mul := by decide
  preimage := squareHeadSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup where
  left := ontoMarker
  right := ontoSquareHead
  jointlyInjective := by
    intro left right
    exact by decide +revert

private def factorIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_943.table.semigroup basis :=
  Order6FinalMarkerSquareHead.intersectionOfSquareHeadBasis
    SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers.S5_943.representative_basis

theorem representative_basis : BasisFor table.semigroup basis :=
  factorIntersection.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_10244

namespace S6_10298

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_10298`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, 1 => 1
  | 2, 2 => 2
  | 2, 3 => 2
  | 2, 4 => 2
  | 2, 5 => 2
  | 3, 1 => 1
  | 3, 2 => 2
  | 3, 3 => 2
  | 3, 4 => 2
  | 3, 5 => 4
  | 4, 1 => 1
  | 4, 2 => 4
  | 4, 3 => 4
  | 4, 4 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 5
  | 5, 3 => 5
  | 5, 4 => 5
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b9816db75d9f751f86de5c890621c2bf08ffa330301b2547545d7846c84983e1"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 2, 3, 3, 3, 3],
   [1, 2, 3, 3, 3, 5],
   [1, 2, 5, 5, 5, 5],
   [1, 2, 6, 6, 6, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

/-- Partition `[0,1,2,2,2,2]`, followed by the identity catalogue map. -/
def markerMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | _ => 0

def markerSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | _ => 0

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMap
  map_mul := by decide
  preimage := markerSection
  right_inverse := by
    intro value
    exact by decide +revert

/-- Partition `[0,0,1,2,3,4]`, followed by catalogue map
`[5,1,2,3,4]` into `S5_904`. -/
def squareHeadMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | _ => 4

def squareHeadSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 0

def ontoSquareHead :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup where
  toFun := squareHeadMap
  map_mul := by decide
  preimage := squareHeadSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup where
  left := ontoMarker
  right := ontoSquareHead
  jointlyInjective := by
    intro left right
    exact by decide +revert

private def factorIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup basis :=
  Order6FinalMarkerSquareHead.intersectionOfSquareHeadBasis
    SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfers.S5_904.representative_basis

theorem representative_basis : BasisFor table.semigroup basis :=
  factorIntersection.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_10298

end SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots
