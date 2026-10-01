import SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20Normal
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets

open SemigroupBasis

namespace S6_9105

/-- Authenticated order-six table, SHA-256 `dd39b74357dcda784f5a162e5bb81fe16267a6ef1c29d32d5a14e1d7d3200f34`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (5 : Fin 6) else (0 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (0 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "dd39b74357dcda784f5a162e5bb81fe16267a6ef1c29d32d5a14e1d7d3200f34"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5], [0, 0, 0, 0, 4, 5], [0, 0, 0, 2, 4, 5], [0, 1, 0, 3, 4, 5], [4, 4, 4, 4, 5, 0], [5, 5, 5, 5, 0, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (3 : Fin 4) else if a = 4 then (0 : Fin 4) else (0 : Fin 4)

def ontoS4Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (3 : Fin 6)

def ontoS4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := ontoS4Map
  map_mul := by decide
  preimage := ontoS4Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  left := ontoS3
  right := ontoS4
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9105

namespace S6_14976

/-- Authenticated order-six table, SHA-256 `c446805642c55e1429e4f07a6d436202176511a5dca4df319e0bed0b425b5d9c`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "c446805642c55e1429e4f07a6d436202176511a5dca4df319e0bed0b425b5d9c"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 3, 4, 4], [0, 0, 0, 3, 4, 4], [0, 1, 2, 3, 4, 4], [3, 3, 3, 4, 0, 0], [4, 4, 4, 0, 3, 3], [4, 4, 5, 0, 3, 3]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (3 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (0 : Fin 4) else (2 : Fin 4)

def ontoS4Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (5 : Fin 6) else (2 : Fin 6)

def ontoS4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := ontoS4Map
  map_mul := by decide
  preimage := ontoS4Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  left := ontoS3
  right := ontoS4
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14976

namespace S6_15941

/-- Authenticated order-six table, SHA-256 `f87d423c94d89840c5a3068b0e8749e231c89ff76f732e14fcf2ea0457699a8e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "f87d423c94d89840c5a3068b0e8749e231c89ff76f732e14fcf2ea0457699a8e"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 3, 3, 3], [0, 1, 2, 3, 3, 5], [2, 2, 3, 0, 0, 0], [3, 3, 0, 2, 2, 2], [3, 4, 0, 2, 2, 2], [3, 3, 0, 2, 2, 2]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (3 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (1 : Fin 4)

def ontoS4Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (4 : Fin 6) else (1 : Fin 6)

def ontoS4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := ontoS4Map
  map_mul := by decide
  preimage := ontoS4Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_18.table.semigroup SemigroupBasis.Generated.S4_20.table.semigroup where
  left := ontoS3
  right := ontoS4
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.basis

/-- Endpoint conditional on the shared completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_15941

end SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets
