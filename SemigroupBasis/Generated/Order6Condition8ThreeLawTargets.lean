import SemigroupBasis.CoRoots.Order6Condition8ThreeLawNormal

/-!
# Six wrapper endpoints for the Condition-8 three-law lane
(msg-0288 / msg-0294 request)

EVIDENCE LABEL: source-staged, NOT compiled here; all finite claims
(`decide` obligations: homomorphism, section, joint injectivity,
published-row match) re-verified computationally before emission.

Route data (all split subdirect onto pinned catalogue factors; the
`S6_9073` wrapper uses the swapped intersection instance):
  S6_8932   S3_11 x S4_77
  S6_9073   S4_77 x S3_11
  S6_11162  S3_11 x S4_77
  S6_11170  S3_11 x S4_77
  S6_11602  S3_11 x S4_77
  S6_11782  S2_2  x S5_904
Opposite endpoints are `oppositeReversed` throughout.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6Condition8ThreeLawTargets

open SemigroupBasis

namespace S6_8932

/-- Authenticated order-six table, SHA-256 `8ba3d4a8af2a1972588c072df5538ee32d35aca9dd8bc2658add122f8a91488b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "8ba3d4a8af2a1972588c072df5538ee32d35aca9dd8bc2658add122f8a91488b"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 3, 3, 3], [0, 0, 2, 3, 3, 4], [2, 2, 0, 3, 3, 3], [3, 3, 3, 3, 3, 3], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS3_11S4_77.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8932

namespace S6_9073

/-- Authenticated order-six table, SHA-256 `3dc3a28dcecc9d4421cd5e2d89f5f6645679cae4f109c53c4b6b2f9650046e3e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "3dc3a28dcecc9d4421cd5e2d89f5f6645679cae4f109c53c4b6b2f9650046e3e"

def publishedRows : List (List Nat) :=
  [[0, 1, 1, 3, 3, 3], [1, 0, 0, 3, 3, 3], [1, 0, 0, 3, 3, 4], [3, 3, 3, 3, 3, 3], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoLeftSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoRightSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS4_77S3_11.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9073

namespace S6_11162

/-- Authenticated order-six table, SHA-256 `6a664f2ca7a64fc9bd0aa7586e78627e953626650b28ab97e09cd86d5ad80f7e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "6a664f2ca7a64fc9bd0aa7586e78627e953626650b28ab97e09cd86d5ad80f7e"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4], [0, 0, 2, 3, 0, 0], [0, 0, 3, 2, 0, 0], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS3_11S4_77.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11162

namespace S6_11170

/-- Authenticated order-six table, SHA-256 `84274b6c3432a8e726ccec3b9795d9cf8fc00755f102a2811c66fbca9a61ab9d`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "84274b6c3432a8e726ccec3b9795d9cf8fc00755f102a2811c66fbca9a61ab9d"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 4], [4, 4, 2, 3, 4, 4], [4, 4, 3, 2, 4, 4], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS3_11S4_77.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11170

namespace S6_11602

/-- Authenticated order-six table, SHA-256 `d15a71c28901655d85676e530a8cc3c8470d8dfb3bdd56632e6ca5c0915a5949`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d15a71c28901655d85676e530a8cc3c8470d8dfb3bdd56632e6ca5c0915a5949"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 4, 4, 0, 4], [5, 5, 2, 3, 5, 5], [5, 5, 3, 2, 5, 5], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (3 : Fin 4) else if a = 3 then (3 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (2 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S4_77.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS3_11S4_77.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11602

namespace S6_11782

/-- Authenticated order-six table, SHA-256 `8fc8c691583574113db9d81177fe5fa8d855375a8634f54a03f704845ec3386e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "8fc8c691583574113db9d81177fe5fa8d855375a8634f54a03f704845ec3386e"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 3, 0, 0], [0, 0, 2, 3, 0, 4], [2, 2, 2, 3, 2, 2], [3, 3, 3, 2, 3, 3], [4, 4, 2, 3, 4, 4], [5, 5, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (2 : Fin 5) else (3 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_904.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8ThreeLaw.intersectionBasisS2_2S5_904.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11782

end SemigroupBasis.Generated.Order6Condition8ThreeLawTargets
