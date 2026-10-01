import SemigroupBasis.CoRoots.Order6Condition8FiveLawNormal

/-!
# Two wrapper endpoints for the Condition-8 five-law parity pair
(msg-0093 repair / msg-0294 request)

EVIDENCE LABEL: source-staged, NOT compiled here; all finite claims
(`decide` obligations: homomorphism, section, joint injectivity,
published-row match) re-verified computationally before emission.

Route data (both split subdirect onto pinned catalogue factors):
  S6_11550  S3_11 x S5_869
  S6_11554  S3_11 x S5_871
Opposite endpoints are `oppositeReversed` throughout.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6Condition8FiveLawTargets

open SemigroupBasis

namespace S6_11550

/-- Authenticated order-six table, SHA-256 `199eb49393eb85945d8d73bb0b8627956bc44d6262360d1409d833b03871ee25`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "199eb49393eb85945d8d73bb0b8627956bc44d6262360d1409d833b03871ee25"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 4], [0, 0, 2, 3, 0, 5], [0, 0, 3, 2, 0, 5], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

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

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_869.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_869.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8FiveLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8FiveLaw.intersectionBasisS3_11S5_869.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11550

namespace S6_11554

/-- Authenticated order-six table, SHA-256 `42c89f24f004dc4d48490fb862f6dbc41f869075cfa92ebaac8faf66e8d8042f`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "42c89f24f004dc4d48490fb862f6dbc41f869075cfa92ebaac8faf66e8d8042f"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 4], [4, 4, 2, 3, 4, 5], [4, 4, 3, 2, 4, 5], [4, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]]

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

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_871.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_871.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Condition8FiveLaw.sigma

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Condition8FiveLaw.intersectionBasisS3_11S5_871.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11554

end SemigroupBasis.Generated.Order6Condition8FiveLawTargets
