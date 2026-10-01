import SemigroupBasis.Subdirect
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

set_option maxRecDepth 100000

/-!
# Ford-Lord corrected-invariant order-six wrapper skeletons

These 18 endpoint tables and quotient pairs are generated from the
msg-0118 residual screen.  They are source-staged scaffolding: the closed
`representative_basis` theorems arrive only with the shared family
normalizers.  The six ce7f endpoints intentionally contain no ce7f
normalizer implementation; that normalizer remains reserved to fable.
-/

namespace SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons

open SemigroupBasis

namespace S6_8206

/-! Preferred msg-0118 factor pair: `S2_4 × S5_400`. -/

/-- Authenticated order-six table, SHA-256 `55f69099b87d80f7c2826ecc9cf245d0b9cff9356ca6de9ae14d567b5ab61a2f`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (0 : Fin 6)
  | 2, 2 => (0 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (0 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "55f69099b87d80f7c2826ecc9cf245d0b9cff9356ca6de9ae14d567b5ab61a2f"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 2, 2],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 0, 0, 4, 4],
    [0, 1, 2, 0, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 1, 0, 0]
def publishedRightMap : List Nat := [0, 1, 2, 0, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 0 => (0 : Fin 2)
  | 1 => (0 : Fin 2)
  | 2 => (0 : Fin 2)
  | 3 => (1 : Fin 2)
  | 4 => (0 : Fin 2)
  | 5 => (0 : Fin 2)
  | _ => (0 : Fin 2)

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (0 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_8206

namespace S6_8264

/-! Preferred msg-0118 factor pair: `S3_15 × S5_400`. -/

/-- Authenticated order-six table, SHA-256 `59d583fdfa332231dafb65072ec5c4658a61547c32d5fafd087b916ca434d8ea`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (0 : Fin 6)
  | 2, 2 => (0 : Fin 6)
  | 2, 3 => (2 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (0 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (4 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (3 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "59d583fdfa332231dafb65072ec5c4658a61547c32d5fafd087b916ca434d8ea"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 2, 2, 2],
    [0, 1, 0, 3, 3, 3],
    [0, 1, 0, 4, 4, 4],
    [0, 1, 2, 3, 3, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 1, 2, 1]
def publishedRightMap : List Nat := [0, 1, 2, 3, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (1 : Fin 3)
  | 4 => (2 : Fin 3)
  | 5 => (1 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_8264

namespace S6_8486

/-! Preferred msg-0118 factor pair: `S3_15 × S5_400`. -/

/-- Authenticated order-six table, SHA-256 `fb128e22a288a862b20aff12671af346e7d09113c1ecd62774c1580bc9f5f21e`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (0 : Fin 6)
  | 2, 2 => (0 : Fin 6)
  | 2, 3 => (2 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (0 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (5 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fb128e22a288a862b20aff12671af346e7d09113c1ecd62774c1580bc9f5f21e"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 0, 0, 2, 2, 2],
    [0, 1, 0, 3, 3, 3],
    [0, 1, 2, 3, 4, 4],
    [0, 1, 2, 3, 5, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_8486

namespace S6_13340

/-! Preferred msg-0118 factor pair: `S2_4 × S5_840`. -/

/-- Authenticated order-six table, SHA-256 `a44acbb90d62743c108e7630bf13cdec46cf214f40016fc93de4e4c7cc5edb47`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (0 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (0 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (0 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a44acbb90d62743c108e7630bf13cdec46cf214f40016fc93de4e4c7cc5edb47"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 0, 0, 2],
    [3, 3, 3, 3, 3, 3],
    [0, 0, 0, 0, 4, 4],
    [0, 1, 2, 0, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 1, 0, 0]
def publishedRightMap : List Nat := [0, 1, 2, 0, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 0 => (0 : Fin 2)
  | 1 => (0 : Fin 2)
  | 2 => (0 : Fin 2)
  | 3 => (1 : Fin 2)
  | 4 => (0 : Fin 2)
  | 5 => (0 : Fin 2)
  | _ => (0 : Fin 2)

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (0 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13340

namespace S6_13376

/-! Preferred msg-0118 factor pair: `S3_15 × S5_840`. -/

/-- Authenticated order-six table, SHA-256 `62ee1fe20101ada894fd2cf3758ba149af82f74e6a68f4a30a761c6911960884`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (2 : Fin 6)
  | 2, 4 => (0 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (0 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (0 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (2 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "62ee1fe20101ada894fd2cf3758ba149af82f74e6a68f4a30a761c6911960884"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 2, 0, 2],
    [0, 1, 3, 3, 0, 3],
    [0, 0, 0, 0, 4, 4],
    [0, 1, 2, 2, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 2, 0, 1]
def publishedRightMap : List Nat := [0, 1, 2, 2, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (2 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (1 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (2 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13376

namespace S6_13610

/-! Preferred msg-0118 factor pair: `S3_15 × S5_840`. -/

/-- Authenticated order-six table, SHA-256 `6916a1f8d009e70ef1421f35146c22cc0ff2d15e7d24f55098d5943fc071b217`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (1 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (0 : Fin 6)
  | 3, 2 => (0 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (5 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6916a1f8d009e70ef1421f35146c22cc0ff2d15e7d24f55098d5943fc071b217"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1],
    [0, 1, 2, 0, 2, 2],
    [0, 0, 0, 3, 3, 3],
    [0, 1, 2, 3, 4, 4],
    [0, 1, 2, 3, 5, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ce7f74c56f7112a3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13610

namespace S6_12950

/-! Preferred msg-0118 factor pair: `S3_15op × S5_788`. -/

/-- Authenticated order-six table, SHA-256 `45e9d5c6aa1a82ca5f2eefa0d50978d736c86e499b8686d0056dd279282afb46`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (4 : Fin 6)
  | 2, 5 => (0 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (0 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (0 : Fin 6)
  | 5, 2 => (0 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (0 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "45e9d5c6aa1a82ca5f2eefa0d50978d736c86e499b8686d0056dd279282afb46"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 1, 2, 0, 4, 0],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 2, 0, 4, 0],
    [0, 0, 0, 3, 0, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 0, 2, 0]
def publishedRightMap : List Nat := [0, 1, 2, 3, 2, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (2 : Fin 3)
  | 5 => (0 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (2 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_12950

namespace S6_13045

/-! Preferred msg-0118 factor pair: `S3_15op × S5_805`. -/

/-- Authenticated order-six table, SHA-256 `a17781c6a1437a5fc779064b91cd962a76166c1003df280fe249b2066cb1710a`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (4 : Fin 6)
  | 2, 5 => (0 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (2 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (4 : Fin 6)
  | 3, 5 => (0 : Fin 6)
  | 4, 0 => (4 : Fin 6)
  | 4, 1 => (4 : Fin 6)
  | 4, 2 => (4 : Fin 6)
  | 4, 3 => (4 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (0 : Fin 6)
  | 5, 2 => (0 : Fin 6)
  | 5, 3 => (0 : Fin 6)
  | 5, 4 => (0 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a17781c6a1437a5fc779064b91cd962a76166c1003df280fe249b2066cb1710a"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 1, 2, 3, 4, 0],
    [0, 1, 2, 3, 4, 0],
    [4, 4, 4, 4, 4, 4],
    [0, 0, 0, 0, 0, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 2, 0, 0]
def publishedRightMap : List Nat := [0, 1, 2, 2, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (2 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (2 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13045

namespace S6_13061

/-! Preferred msg-0118 factor pair: `S3_15op × S5_811`. -/

/-- Authenticated order-six table, SHA-256 `80062688cce7d5a4895154dcfa187350f3bae785b98313cf9e7dec98ba9f061a`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (4 : Fin 6)
  | 2, 5 => (3 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (3 : Fin 6)
  | 5, 0 => (3 : Fin 6)
  | 5, 1 => (3 : Fin 6)
  | 5, 2 => (3 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (3 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "80062688cce7d5a4895154dcfa187350f3bae785b98313cf9e7dec98ba9f061a"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 1, 2, 3, 4, 3],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 2, 3, 4, 3],
    [3, 3, 3, 3, 3, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 0, 2, 0]
def publishedRightMap : List Nat := [0, 1, 2, 3, 2, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (2 : Fin 3)
  | 5 => (0 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (2 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13061

namespace S6_13330

/-! Preferred msg-0118 factor pair: `S3_15op × S5_788`. -/

/-- Authenticated order-six table, SHA-256 `9ec88df1a0e7cc7159b65a9ceb8358e66c987d00253d0d854e51986c7d6e1628`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (0 : Fin 6)
  | 2, 5 => (0 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (0 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (0 : Fin 6)
  | 5, 2 => (0 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9ec88df1a0e7cc7159b65a9ceb8358e66c987d00253d0d854e51986c7d6e1628"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 0, 0, 0],
    [3, 3, 3, 3, 3, 3],
    [0, 0, 0, 3, 4, 5],
    [0, 0, 0, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13330

namespace S6_13407

/-! Preferred msg-0118 factor pair: `S3_15op × S5_805`. -/

/-- Authenticated order-six table, SHA-256 `7d47249c3082eb431dba4c93445e9007ba18adbd1768d5dd92abc0b8ef02627f`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (0 : Fin 6)
  | 2, 5 => (0 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (0 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (0 : Fin 6)
  | 5, 2 => (0 : Fin 6)
  | 5, 3 => (0 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7d47249c3082eb431dba4c93445e9007ba18adbd1768d5dd92abc0b8ef02627f"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 3, 0, 0],
    [3, 3, 3, 3, 3, 3],
    [0, 0, 0, 0, 4, 5],
    [0, 0, 0, 0, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13407

namespace S6_13438

/-! Preferred msg-0118 factor pair: `S3_15op × S5_811`. -/

/-- Authenticated order-six table, SHA-256 `375fdd57af2612a4ad40f56038e637c5807830d29f9c5261b09cc322e228d32f`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (3 : Fin 6)
  | 2, 5 => (3 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (3 : Fin 6)
  | 4, 1 => (3 : Fin 6)
  | 4, 2 => (3 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (3 : Fin 6)
  | 5, 1 => (3 : Fin 6)
  | 5, 2 => (3 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "375fdd57af2612a4ad40f56038e637c5807830d29f9c5261b09cc322e228d32f"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 3, 3, 3],
    [3, 3, 3, 3, 3, 3],
    [3, 3, 3, 3, 4, 5],
    [3, 3, 3, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13438

namespace S6_12965

/-! Preferred msg-0118 factor pair: `S3_15op × S5_794`. -/

/-- Authenticated order-six table, SHA-256 `48e5ccc7399fbb41aec9fb6f8a5a02037c1324845751e67ed8a8f529e35b709c`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (4 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (2 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "48e5ccc7399fbb41aec9fb6f8a5a02037c1324845751e67ed8a8f529e35b709c"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 1, 2, 0, 4, 2],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 2, 0, 4, 2],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 0, 2, 1]
def publishedRightMap : List Nat := [0, 1, 2, 3, 2, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (2 : Fin 3)
  | 5 => (1 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (2 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_12965

namespace S6_13056

/-! Preferred msg-0118 factor pair: `S3_15op × S5_810`. -/

/-- Authenticated order-six table, SHA-256 `31d200459fe533e14fe3ff2f4b8a394e12675072d655ed007bcb9ea47c5a4685`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (0 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (4 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (2 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (4 : Fin 6)
  | 3, 5 => (2 : Fin 6)
  | 4, 0 => (4 : Fin 6)
  | 4, 1 => (4 : Fin 6)
  | 4, 2 => (4 : Fin 6)
  | 4, 3 => (4 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "31d200459fe533e14fe3ff2f4b8a394e12675072d655ed007bcb9ea47c5a4685"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 1, 2, 3, 4, 2],
    [0, 1, 2, 3, 4, 2],
    [4, 4, 4, 4, 4, 4],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 2, 0, 1]
def publishedRightMap : List Nat := [0, 1, 2, 2, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (2 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (1 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (2 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13056

namespace S6_13366

/-! Preferred msg-0118 factor pair: `S3_15op × S5_794`. -/

/-- Authenticated order-six table, SHA-256 `bd0a0c6380a4cf6f5fa605e113cc63a935ab2530e108feb1a580edf7b2afbafd`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (0 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bd0a0c6380a4cf6f5fa605e113cc63a935ab2530e108feb1a580edf7b2afbafd"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 0, 2, 2],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13366

namespace S6_13401

/-! Preferred msg-0118 factor pair: `S3_15op × S5_802`. -/

/-- Authenticated order-six table, SHA-256 `da344b74a6c7d3105160daf5599a999512ce227c260ed88b0dcf57dc1f1857a9`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (2 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "da344b74a6c7d3105160daf5599a999512ce227c260ed88b0dcf57dc1f1857a9"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 2, 2, 2],
    [0, 1, 3, 3, 3, 3],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13401

namespace S6_13433

/-! Preferred msg-0118 factor pair: `S3_15op × S5_810`. -/

/-- Authenticated order-six table, SHA-256 `9fcf00667db46a5384ebc811070cb87056c70d2ee804c7cbc07075de2b43ac52`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (2 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (3 : Fin 6)
  | 3, 1 => (3 : Fin 6)
  | 3, 2 => (3 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (3 : Fin 6)
  | 3, 5 => (3 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (1 : Fin 6)
  | 4, 2 => (2 : Fin 6)
  | 4, 3 => (3 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (5 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9fcf00667db46a5384ebc811070cb87056c70d2ee804c7cbc07075de2b43ac52"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 3, 2, 2],
    [3, 3, 3, 3, 3, 3],
    [0, 1, 2, 3, 4, 5],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 0, 0, 1, 2]
def publishedRightMap : List Nat := [0, 1, 2, 3, 4, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (2 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (3 : Fin 5)
  | 4 => (4 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13433

namespace S6_13411

/-! Preferred msg-0118 factor pair: `S3_15op × S5_840`. -/

/-- Authenticated order-six table, SHA-256 `21b154c93ee169ddcd47b4090971806080c3f81005e6a002765c8ca9805c80d6`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 0, 0 => (0 : Fin 6)
  | 0, 1 => (0 : Fin 6)
  | 0, 2 => (0 : Fin 6)
  | 0, 3 => (0 : Fin 6)
  | 0, 4 => (0 : Fin 6)
  | 0, 5 => (0 : Fin 6)
  | 1, 0 => (0 : Fin 6)
  | 1, 1 => (0 : Fin 6)
  | 1, 2 => (0 : Fin 6)
  | 1, 3 => (0 : Fin 6)
  | 1, 4 => (1 : Fin 6)
  | 1, 5 => (1 : Fin 6)
  | 2, 0 => (0 : Fin 6)
  | 2, 1 => (1 : Fin 6)
  | 2, 2 => (2 : Fin 6)
  | 2, 3 => (3 : Fin 6)
  | 2, 4 => (0 : Fin 6)
  | 2, 5 => (2 : Fin 6)
  | 3, 0 => (0 : Fin 6)
  | 3, 1 => (1 : Fin 6)
  | 3, 2 => (2 : Fin 6)
  | 3, 3 => (3 : Fin 6)
  | 3, 4 => (0 : Fin 6)
  | 3, 5 => (2 : Fin 6)
  | 4, 0 => (0 : Fin 6)
  | 4, 1 => (0 : Fin 6)
  | 4, 2 => (0 : Fin 6)
  | 4, 3 => (0 : Fin 6)
  | 4, 4 => (4 : Fin 6)
  | 4, 5 => (4 : Fin 6)
  | 5, 0 => (0 : Fin 6)
  | 5, 1 => (1 : Fin 6)
  | 5, 2 => (2 : Fin 6)
  | 5, 3 => (3 : Fin 6)
  | 5, 4 => (4 : Fin 6)
  | 5, 5 => (5 : Fin 6)
  | _, _ => (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "21b154c93ee169ddcd47b4090971806080c3f81005e6a002765c8ca9805c80d6"

def publishedRows : List (List Nat) :=
  [
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1],
    [0, 1, 2, 3, 0, 2],
    [0, 1, 2, 3, 0, 2],
    [0, 0, 0, 0, 4, 4],
    [0, 1, 2, 3, 4, 5]
  ]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def publishedLeftMap : List Nat := [0, 0, 1, 2, 0, 1]
def publishedRightMap : List Nat := [0, 1, 2, 2, 3, 4]

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (1 : Fin 3)
  | 3 => (2 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (1 : Fin 3)
  | _ => (0 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (2 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoLeftMap_matches :
    (List.finRange 6).map (fun value => (ontoLeftMap value).val) =
      publishedLeftMap := by
  decide

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => (0 : Fin 5)
  | 1 => (1 : Fin 5)
  | 2 => (2 : Fin 5)
  | 3 => (2 : Fin 5)
  | 4 => (3 : Fin 5)
  | 5 => (4 : Fin 5)
  | _ => (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (4 : Fin 6)
  | 4 => (5 : Fin 6)
  | _ => (0 : Fin 6)

theorem ontoRightMap_matches :
    (List.finRange 6).map (fun value => (ontoRightMap value).val) =
      publishedRightMap := by
  decide

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_9808750adcf41d94.basis

/-- Conditional endpoint hook.  The family normalizer supplies `intersection`. -/
theorem representative_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup basis :=
  intersection.basisFor pair

theorem opposite_basis_of
    (intersection : IntersectionBasis SemigroupBasis.Generated.S3_15.table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of intersection).oppositeReversed

end S6_13411

end SemigroupBasis.Generated.Order6FordLordInvariantWrapperSkeletons
