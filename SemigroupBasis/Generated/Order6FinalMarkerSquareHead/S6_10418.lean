import SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FinalMarkerSquareHead.S6_10418

open SemigroupBasis

abbrev familyBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.basis

abbrev familyOppositeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.oppositeBasis

/-- Exact zero-based multiplication for the Smallsemi representative
`S6_10418`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, _ => 2
  | 3, 0 => 2
  | 3, 1 => 2
  | 3, 2 => 2
  | 3, 3 => 2
  | 3, 4 => 0
  | 3, 5 => 2
  | 4, _ => 4
  | 5, 1 => 1
  | 5, 3 => 1
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "93f09cb5bf19ec4486b097a46d27b087fefcecd0727a03b74394f89630449181"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [3, 3, 3, 3, 3, 3],
   [3, 3, 3, 3, 1, 3],
   [5, 5, 5, 5, 5, 5],
   [1, 2, 1, 2, 1, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

/-- Two target-valued homomorphisms on the source `S6_7541`, in one-based
catalogue coordinates. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1, 2, 1, 1, 6, 1], [3, 3, 4, 1, 3, 5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased =
      [[1, 2, 1, 1, 6, 1], [3, 3, 4, 1, 3, 5]] := by
  decide

def coordinateValue (coordinate : Fin 2) (value : Fin 6) : Fin 6 :=
  if coordinate = 0 then
    match value.val with
    | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 5 | _ => 0
  else
    match value.val with
    | 0 => 2 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 2 | _ => 4

def coordinateHom (coordinate : Fin 2) :
    Hom
      SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.S6_7541.table.semigroup
      table.semigroup where
  toFun := coordinateValue coordinate
  map_mul := by
    intro left right
    apply Fin.ext
    revert coordinate left right
    decide

def sourceEmbedding :
    Embedding
      SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.S6_7541.table.semigroup
      (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro left right equalCoordinates
    revert left right
    decide)

private def toFinThree (index : Nat) : Fin 3 :=
  if index = 0 then 0 else if index = 1 then 1 else 2

theorem targetModels : Models table.semigroup familyBasis :=
  FiniteCertificate.checkModels_sound table familyBasis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup familyBasis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.S6_7541.representative_basis
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite familyOppositeBasis := by
  simpa [familyOppositeBasis,
    SemigroupBasis.CoRoots.Order6FinalMarkerSquareHeadRoots.oppositeBasis] using
      representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FinalMarkerSquareHead.S6_10418
