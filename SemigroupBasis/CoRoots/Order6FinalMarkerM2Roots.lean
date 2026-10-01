import SemigroupBasis.CoRoots.Order6FinalMarkerM2

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FinalMarkerM2Roots

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  Order6FinalMarkerM2.basis

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def candidateBasisUpToOppositeSHA256 : String :=
  Order6FinalMarkerM2.candidateBasisUpToOppositeSHA256

private def markerMapA (value : Fin 6) : Fin 3 :=
  match value.val with
  | 2 => 1
  | 5 => 2
  | _ => 0

private def markerSectionA (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 2
  | 2 => 5
  | _ => 0

private def markerMapB (value : Fin 6) : Fin 3 :=
  match value.val with
  | 3 => 1
  | 5 => 2
  | _ => 0

private def markerSectionB (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 3
  | 2 => 5
  | _ => 0

private def markerMapC (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 1
  | 5 => 2
  | _ => 0

private def markerSectionC (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 4
  | 2 => 5
  | _ => 0

private def m2MapA (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

private def m2SectionA (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | _ => 0

private def m2MapB (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

private def m2SectionB (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | _ => 0

private def m2MapC (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

private def m2SectionC (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | _ => 0

private def m2MapD (value : Fin 6) : Fin 5 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 4
  | _ => 0

private def m2SectionD (value : Fin 5) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | _ => 0

namespace S6_2741

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 3, 5 => 3
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9bac62ece5a8a7e17458e1f488499af8348cf75477ed25687c37ae920ad38b46"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 4],
   [1, 1, 1, 2, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := m2MapA
  map_mul := by decide
  preimage := m2SectionA
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2741

namespace S6_2753

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 5 => 1
    | 3, 5 => 3
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "84f1b80990308cea65f42dc145e1bf83cac8694fbbc26c46e6ce7218b9bd8a79"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 4],
   [1, 1, 1, 2, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := m2MapB
  map_mul := by decide
  preimage := m2SectionB
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2753

namespace S6_2760

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 5 => 2
    | 3, 5 => 2
    | 4, 2 => 1
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "005b7eaf7a28e3a417f65fabc4c99c2f675fe1e669aa2f45d7673bff8ac53835"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 3],
   [1, 1, 1, 1, 1, 3],
   [1, 1, 2, 2, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapB
  map_mul := by decide
  preimage := markerSectionB
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := m2MapC
  map_mul := by decide
  preimage := m2SectionC
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2760

namespace S6_5247

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 5 => 2
    | 3, 2 => 1
    | 3, 3 => 1
    | 3, 4 => 1
    | 3, 5 => 3
    | 4, 2 => 1
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 3
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cfbea2e4fb87086482d3f0f58d8782b60dc291dfc4a47220801b615405aac6bd"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 3],
   [1, 1, 2, 2, 2, 4],
   [1, 1, 2, 2, 2, 4],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapC
  map_mul := by decide
  preimage := markerSectionC
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  toFun := m2MapD
  map_mul := by decide
  preimage := m2SectionD
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_5247

namespace S6_5211

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 3, 3 => 1
    | 3, 5 => 3
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0a66c3d2ef015f74305c52e3d29e8796d8ca2bb90f567105fbe1530b01dfa2b6"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 2, 1, 4],
   [1, 1, 1, 2, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  toFun := m2MapA
  map_mul := by decide
  preimage := m2SectionA
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_498IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_5211

namespace S6_5222

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 5 => 1
    | 3, 3 => 1
    | 3, 5 => 3
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4372f126ca5104aad25c1570fe77ed55320fd1ed5f8ec96c99c2ff515356c86d"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 2, 1, 4],
   [1, 1, 1, 2, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  toFun := m2MapB
  map_mul := by decide
  preimage := m2SectionB
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_498IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_5222

namespace S6_9306

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 2 => 1
    | 2, 5 => 2
    | 3, 2 => 1
    | 3, 3 => 1
    | 3, 4 => 1
    | 3, 5 => 3
    | 4, 2 => 1
    | 4, 3 => 1
    | 4, 4 => 1
    | 4, 5 => 3
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9788757ab2051548f45e89642ae832a57a943c1c5829257cb534cd6906ee5b1a"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 2, 1, 1, 3],
   [1, 1, 2, 2, 2, 4],
   [1, 1, 2, 2, 2, 4],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapC
  map_mul := by decide
  preimage := markerSectionC
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  toFun := m2MapD
  map_mul := by decide
  preimage := m2SectionD
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_498.table.semigroup where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_498IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_9306

namespace S6_2742

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 3, 4 => 1
    | 3, 5 => 3
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8cc127755e26a0b79684a340b13706a58373283a65a94f662cfe2d2ee5e52f79"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 2, 4],
   [1, 1, 1, 1, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite where
  toFun := m2MapA
  map_mul := by decide
  preimage := m2SectionA
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213OppositeIntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2742

namespace S6_2754

def mul (left right : Fin 6) : Fin 6 :=
  if left.val = 5 then right
  else
    match left.val, right.val with
    | 1, 5 => 1
    | 2, 5 => 1
    | 3, 4 => 1
    | 3, 5 => 3
    | 4, 4 => 1
    | 4, 5 => 4
    | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "438a41a35dd775ac63f7122673aa0aeb4e7d4389e7bc0b61a90533d7c8e23f62"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 1, 2],
   [1, 1, 1, 1, 2, 4],
   [1, 1, 1, 1, 2, 5],
   [1, 2, 3, 4, 5, 6]]

theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def ontoMarker :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := markerMapA
  map_mul := by decide
  preimage := markerSectionA
  right_inverse := by
    intro value
    exact by decide +revert

def ontoM2 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite where
  toFun := m2MapB
  map_mul := by decide
  preimage := m2SectionB
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup.opposite where
  left := ontoMarker
  right := ontoM2
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis : BasisFor table.semigroup basis :=
  Order6FinalMarkerM2.s3_6_s5_213OppositeIntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

theorem basis_complete : BasisFor table.semigroup basis :=
  representative_basis

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis

end S6_2754

end SemigroupBasis.CoRoots.Order6FinalMarkerM2Roots
