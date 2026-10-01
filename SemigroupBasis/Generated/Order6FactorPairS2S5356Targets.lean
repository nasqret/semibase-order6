import SemigroupBasis.CoRoots.Order6FactorPairS2S5356Normal
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS2S5356Targets

open SemigroupBasis

private theorem shared_basis_matches_contract :
    SemigroupBasis.CoRoots.Order6FactorPairS2S5356.basis =
      [SemigroupBasis.CoRoots.Order6FactorPairS2S5356.powerLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.tripleLeftContractionLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.endpointTransferLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.splitEndpointContractionLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.squareInterleaveLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.squareFinalSwitchLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.tripleFinalSwitchLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.doubledInitialMoveLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.attachmentXYYZXLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.rightTripleExpansionLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.openInteriorSwapLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.closedInteriorSwapLaw,
        SemigroupBasis.CoRoots.Order6FactorPairS2S5356.repeatedFinalSwapLaw] := by
  rfl

namespace S6_4061

/-- Authenticated order-six table, SHA-256 `90e46d59f8f9f8b9ea900547463f5b3a75cc459c8dc33064840c9d533bda0b8b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "90e46d59f8f9f8b9ea900547463f5b3a75cc459c8dc33064840c9d533bda0b8b"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 3, 0, 0], [0, 0, 0, 3, 0, 0], [0, 0, 0, 3, 2, 2], [3, 3, 3, 0, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoCyclicMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoCyclicSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := ontoCyclicMap
  map_mul := by decide
  preimage := ontoCyclicSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  left := ontoCyclic
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2S5356.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5356.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4061

namespace S6_4166

/-- Authenticated order-six table, SHA-256 `893d0026b9d7276d4cb979f8b86291e06f8f4c0f55b42a7ce907e38f5f59609c`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "893d0026b9d7276d4cb979f8b86291e06f8f4c0f55b42a7ce907e38f5f59609c"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 2, 0, 0], [0, 0, 2, 2, 0, 0], [2, 2, 0, 0, 2, 2], [2, 2, 0, 0, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoCyclicMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (1 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoCyclicSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (2 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := ontoCyclicMap
  map_mul := by decide
  preimage := ontoCyclicSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  left := ontoCyclic
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2S5356.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5356.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4166

namespace S6_4205

/-- Authenticated order-six table, SHA-256 `9c1ba417d5266ca116efdaa4cc158e1c01f045790cdd9bffb278dd734ebb9dc3`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "9c1ba417d5266ca116efdaa4cc158e1c01f045790cdd9bffb278dd734ebb9dc3"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 2, 0, 0], [0, 0, 2, 2, 1, 1], [2, 2, 0, 0, 2, 2], [2, 2, 0, 0, 2, 2], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoCyclicMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (1 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoCyclicSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (2 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := ontoCyclicMap
  map_mul := by decide
  preimage := ontoCyclicSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (1 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  left := ontoCyclic
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2S5356.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5356.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4205

namespace S6_4273

/-- Authenticated order-six table, SHA-256 `9974e8ed1fccda9066165569aee623cd28457fdb9911958e2baa03fb8f9b8480`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "9974e8ed1fccda9066165569aee623cd28457fdb9911958e2baa03fb8f9b8480"

def publishedRows : List (List Nat) :=
  [[0, 1, 1, 1, 0, 0], [1, 0, 0, 0, 1, 1], [1, 0, 0, 0, 1, 1], [1, 0, 0, 0, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoCyclicMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (1 : Fin 2) else if a = 2 then (1 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoCyclicSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := ontoCyclicMap
  map_mul := by decide
  preimage := ontoCyclicSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_2.table.semigroup SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup where
  left := ontoCyclic
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2S5356.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5356.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4273

end SemigroupBasis.Generated.Order6FactorPairS2S5356Targets
