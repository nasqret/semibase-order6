import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71TargetHeadScheduler
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS4_69S4_71TargetHead

open SemigroupBasis

def basisSHA256 : String := "bf48e9968fd27f2b614307276ef8f7ab8fc6b10ad7bb62f3c5a2ac11a28ac8b7"

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S4_69.table.semigroup
      SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.factorIntersectionBasis
    SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.targetHeadJointSignatureCanonicalization

namespace S6_7943

/-- Authenticated order-six table, SHA-256 `3f803be8ff68c99dcde95d7cc3e077fa118ea2d018e09aede1f5accbc6d07b42`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "3f803be8ff68c99dcde95d7cc3e077fa118ea2d018e09aede1f5accbc6d07b42"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 0, 0], [0, 1, 0, 0, 4, 4], [0, 1, 0, 0, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7943

namespace S6_7972

/-- Authenticated order-six table, SHA-256 `28059fb958f8e998824d14a8c1bd77bb42cd824ceed4087d70dc68d34b3e1780`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "28059fb958f8e998824d14a8c1bd77bb42cd824ceed4087d70dc68d34b3e1780"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 3, 3], [0, 1, 2, 3, 4, 3], [0, 0, 2, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7972

namespace S6_8020

/-- Authenticated order-six table, SHA-256 `1aa8bd7f827e02e41a3868bb1fc2f6e32c7d4ad44bbf93e464e21c33dc61d384`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "1aa8bd7f827e02e41a3868bb1fc2f6e32c7d4ad44bbf93e464e21c33dc61d384"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 1, 1, 3, 3, 3], [0, 1, 2, 3, 4, 3], [0, 1, 1, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8020

namespace S6_8116

/-- Authenticated order-six table, SHA-256 `6bd02e7ca449f8d048cab85980118afeba6f848ed855c275ce79f0e28ed1e026`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "6bd02e7ca449f8d048cab85980118afeba6f848ed855c275ce79f0e28ed1e026"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [0, 0, 2, 3, 3, 0], [0, 1, 2, 3, 4, 0], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (0 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8116

namespace S6_8119

/-- Authenticated order-six table, SHA-256 `2ca5bdf4a972acfc0c711707a2c3b31301fbcc4993855cd604842881f5da1007`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "2ca5bdf4a972acfc0c711707a2c3b31301fbcc4993855cd604842881f5da1007"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [0, 0, 2, 3, 3, 3], [0, 1, 2, 3, 4, 3], [0, 0, 2, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (2 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8119

namespace S6_8120

/-- Authenticated order-six table, SHA-256 `88634d9124cbd47a79d0e3da98b9686ef0a4a284f6d4b1e7e6575aa6e8df0bda`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "88634d9124cbd47a79d0e3da98b9686ef0a4a284f6d4b1e7e6575aa6e8df0bda"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [0, 1, 2, 3, 0, 3], [0, 0, 0, 0, 4, 0], [0, 1, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (2 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8120

namespace S6_8169

/-- Authenticated order-six table, SHA-256 `402add067d71231be9b893850bf7310b9273677789a9aaee71bea1a79e8f6391`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "402add067d71231be9b893850bf7310b9273677789a9aaee71bea1a79e8f6391"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 2], [0, 0, 2, 3, 0, 0], [0, 1, 0, 0, 4, 4], [0, 1, 0, 0, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (3 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8169

namespace S6_10897

/-- Authenticated order-six table, SHA-256 `7b36a2bdb5bba6d9ba25e7738df9eb912b14429f0387a135978d7a1a51149815`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "7b36a2bdb5bba6d9ba25e7738df9eb912b14429f0387a135978d7a1a51149815"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 2, 2, 2, 2], [0, 1, 2, 2, 2, 3], [0, 1, 2, 3, 4, 2], [0, 1, 2, 2, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (1 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_10897

namespace S6_10906

/-- Authenticated order-six table, SHA-256 `6039e2de88c306b83c1fb1927cb285801fbf32532beae9872772bfbae6abd870`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "6039e2de88c306b83c1fb1927cb285801fbf32532beae9872772bfbae6abd870"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 2, 2, 2, 2], [0, 1, 2, 2, 3, 2], [0, 1, 2, 2, 4, 2], [0, 1, 2, 3, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_69Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (1 : Fin 4) else if a = 4 then (3 : Fin 4) else (2 : Fin 4)

def ontoS4_69Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (5 : Fin 6) else (4 : Fin 6)

def ontoS4_69 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup where
  toFun := ontoS4_69Map
  map_mul := by decide
  preimage := ontoS4_69Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_71Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def ontoS4_71Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)

def ontoS4_71 : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := ontoS4_71Map
  map_mul := by decide
  preimage := ontoS4_71Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S4_69.table.semigroup SemigroupBasis.Generated.S4_71.table.semigroup where
  left := ontoS4_69
  right := ontoS4_71
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_10906

end SemigroupBasis.Generated.Order6FactorPairS4_69S4_71TargetHead
