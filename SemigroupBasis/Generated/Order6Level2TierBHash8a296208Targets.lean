import SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6Level2TierBHash8a296208Targets

open SemigroupBasis

namespace S6_7953

/-- Authenticated order-six table, SHA-256 `a3bb5cc7a1a6f8c04059a58b11eb3d54db8f8f752956274a7e663a0e40162c93`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a3bb5cc7a1a6f8c04059a58b11eb3d54db8f8f752956274a7e663a0e40162c93"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 0, 2], [4, 4, 4, 4, 4, 4], [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (4 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7953

namespace S6_7966

/-- Authenticated order-six table, SHA-256 `2d6e72a0122ad03803a372c956758cce177d519321131598c64e899c8f43c575`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "2d6e72a0122ad03803a372c956758cce177d519321131598c64e899c8f43c575"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 2, 3, 3, 2], [0, 0, 2, 4, 4, 2], [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else (4 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7966

namespace S6_8132

/-- Authenticated order-six table, SHA-256 `a50f8b7cd997e908fe5c0cee1124541cf02671cbb08ba2aadd143ad4dc66602d`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a50f8b7cd997e908fe5c0cee1124541cf02671cbb08ba2aadd143ad4dc66602d"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [3, 3, 3, 3, 3, 3], [0, 0, 0, 0, 4, 0], [0, 1, 2, 0, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (3 : Fin 4) else (2 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (5 : Fin 6) else (4 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8132

namespace S6_8157

/-- Authenticated order-six table, SHA-256 `1c867ba7091e34e36c32869a0e9687654ff0c8ae21306a8e71cb0ea430fbc3a1`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "1c867ba7091e34e36c32869a0e9687654ff0c8ae21306a8e71cb0ea430fbc3a1"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0], [3, 3, 3, 3, 3, 3], [0, 1, 2, 0, 4, 1], [3, 3, 3, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (0 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (4 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8157

namespace S6_8251

/-- Authenticated order-six table, SHA-256 `6f7b986c4210da65abb3fc48b64aee9672df7c3477c00aaee8ed9d055b7911fe`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "6f7b986c4210da65abb3fc48b64aee9672df7c3477c00aaee8ed9d055b7911fe"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 2, 0], [0, 1, 2, 3, 3, 1], [0, 1, 2, 4, 4, 1], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (0 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else (4 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_8251

namespace S6_11030

/-- Authenticated order-six table, SHA-256 `297c607c4c75619e6c488fbf8a64aefba1fdd597dafaee152c520aaff78362fe`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "297c607c4c75619e6c488fbf8a64aefba1fdd597dafaee152c520aaff78362fe"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 3], [0, 1, 0, 0, 4, 1], [2, 2, 2, 3, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def componentQuotientMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (2 : Fin 4) else (3 : Fin 4)

def componentQuotientSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)

def componentQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.connectedComponentFour.semigroup where
  toFun := componentQuotientMap
  map_mul := by decide
  preimage := componentQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def multiplicityQuotientMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)

def multiplicityQuotientSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)

def multiplicityQuotient : SplitSurjection table.semigroup SemigroupBasis.Examples.commutativeExponentThree.semigroup where
  toFun := multiplicityQuotientMap
  map_mul := by decide
  preimage := multiplicityQuotientSection
  right_inverse := by
    intro value
    exact by decide +revert

def headMap (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (2 : Fin 6)

def headEmbedding : Embedding SemigroupBasis.Examples.leftZeroTwo.semigroup table.semigroup where
  toFun := headMap
  map_mul := by decide
  injective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    table basis toFinThree (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Level2TierBHash8a296208Direct.basisForOfComponentMultiplicityHeadDetectors
    table.semigroup models componentQuotient
    multiplicityQuotient headEmbedding

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11030

end SemigroupBasis.Generated.Order6Level2TierBHash8a296208Targets
