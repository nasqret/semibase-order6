import SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110Normal
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_6S5_110Targets

open SemigroupBasis

namespace S6_1118

/-- Authenticated order-six table, SHA-256 `d0f135faa89febdfb9f88ee4e27f9470068832d6f0fc17f40a23e6ac111cf855`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d0f135faa89febdfb9f88ee4e27f9470068832d6f0fc17f40a23e6ac111cf855"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 3], [0, 0, 0, 2, 0, 4], [0, 1, 2, 3, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1118

namespace S6_1170

/-- Authenticated order-six table, SHA-256 `62baa08e582a007ac9c978f54cfb6f5c22fdb295ef913c08cefca6166abe6349`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "62baa08e582a007ac9c978f54cfb6f5c22fdb295ef913c08cefca6166abe6349"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 0, 4], [0, 1, 2, 3, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1170

namespace S6_1176

/-- Authenticated order-six table, SHA-256 `2364270f20d957f935daf30d9d2d40cf8fc3fb0a504ba26af5e64d4c314ea2df`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "2364270f20d957f935daf30d9d2d40cf8fc3fb0a504ba26af5e64d4c314ea2df"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 3], [0, 3, 3, 0, 0, 4], [0, 1, 2, 3, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1176

end SemigroupBasis.Generated.Order6FactorPairS3_6S5_110Targets
