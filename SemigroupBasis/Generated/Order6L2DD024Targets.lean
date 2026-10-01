import SemigroupBasis.CoRoots.Order6L2DD024
import SemigroupBasis.FiniteReflection

/-!
# The two d024 cut/initial B10 targets

The authenticated order-six representatives below are literal subdirect
products of the direct factors `S3_16` and `S5_804`.  Their representative
endpoints inherit the exact ten-law B10 intersection basis; opposite
endpoints use only `BasisFor.oppositeReversed` and therefore carry
`reversedBasis B10`.

The displayed B10 SHA-256 is
`86a233ce9b903e4df1c4da10183be308432fefdbd9dd753968b369b766c85f59`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6L2DD024Targets

open SemigroupBasis

namespace S6_12953

/-! Authenticated zero-based order-six table. Compact-row SHA-256:
`64a3d391fe00fc7b70cd700dd5c9dbdd9d10e50d5d635556ba64a4f408607b3c`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else if a = 3 then
    if b = 0 then (3 : Fin 6)
    else if b = 1 then (3 : Fin 6)
    else if b = 2 then (3 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if a = 4 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (1 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "64a3d391fe00fc7b70cd700dd5c9dbdd9d10e50d5d635556ba64a4f408607b3c"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 2, 0, 4, 0],
   [3, 3, 3, 3, 3, 3], [0, 1, 2, 0, 4, 1], [0, 0, 0, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3)
  else if a = 1 then (0 : Fin 3)
  else if a = 2 then (0 : Fin 3)
  else if a = 3 then (2 : Fin 3)
  else if a = 4 then (0 : Fin 3)
  else (1 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (5 : Fin 6)
  else (3 : Fin 6)

def ontoS3_16 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_804Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5)
  else if a = 1 then (1 : Fin 5)
  else if a = 2 then (2 : Fin 5)
  else if a = 3 then (0 : Fin 5)
  else if a = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoS5_804Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else if a = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoS5_804 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup where
  toFun := ontoS5_804Map
  map_mul := by decide
  preimage := ontoS5_804Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup where
  left := ontoS3_16
  right := ontoS5_804
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD024.B10

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD024.intersectionBasisS3_16S5_804.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_12953

namespace S6_13047

/-! Authenticated zero-based order-six table. Compact-row SHA-256:
`2b3e99c54d34a589ef20a51e3cc9d592240b44d0b24d24e849d925530d16c1ce`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (0 : Fin 6)
  else if a = 3 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (1 : Fin 6)
  else if a = 4 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (4 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2b3e99c54d34a589ef20a51e3cc9d592240b44d0b24d24e849d925530d16c1ce"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 2, 3, 4, 0],
   [0, 1, 2, 3, 4, 1], [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3)
  else if a = 1 then (0 : Fin 3)
  else if a = 2 then (1 : Fin 3)
  else if a = 3 then (1 : Fin 3)
  else if a = 4 then (2 : Fin 3)
  else (0 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (2 : Fin 6)
  else (4 : Fin 6)

def ontoS3_16 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_804Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5)
  else if a = 1 then (1 : Fin 5)
  else if a = 2 then (2 : Fin 5)
  else if a = 3 then (3 : Fin 5)
  else if a = 4 then (0 : Fin 5)
  else (4 : Fin 5)

def ontoS5_804Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else if a = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoS5_804 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup where
  toFun := ontoS5_804Map
  map_mul := by decide
  preimage := ontoS5_804Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup where
  left := ontoS3_16
  right := ontoS5_804
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD024.B10

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD024.intersectionBasisS3_16S5_804.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_13047

end SemigroupBasis.Generated.Order6L2DD024Targets
