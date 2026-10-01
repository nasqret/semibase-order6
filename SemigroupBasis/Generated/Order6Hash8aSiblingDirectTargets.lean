import SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead

set_option maxRecDepth 100000

/-!
# Direct-factor endpoints for the hash8a sibling family

The three representatives below have the direct subdirect pairs
`S2_4 x S5_378`, `S3_15 x S5_378`, and `S2_4 x S5_378`.  The tables and
quotient maps are authenticated by finite kernel checks; unrestricted
completeness comes from the shared fixed-head normalizer.
-/

namespace SemigroupBasis.Generated.Order6Hash8aSiblingDirectTargets

open SemigroupBasis

namespace S6_7946

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 2 => 2
  | 3, 3 => 3
  | 4, _ => 4
  | 5, 1 => 1
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9c750d0af0c11650ed19c5872d34fd946352eb5a91cecf333b935fad4cf1d4ac"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 2],
   [0, 0, 2, 3, 0, 0],
   [4, 4, 4, 4, 4, 4],
   [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  if value = 4 then 1 else 0

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 4

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 0
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 5

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_4.table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS2_4S5_378.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7946

namespace S6_7962

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, 5 => 2
  | 3, 2 => 2
  | 3, 3 => 3
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 4
  | 4, 4 => 4
  | 5, 1 => 1
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c6620928c7c0f476fdac9705661283b2230ed1f6f931c37b8ec9c278e37a042d"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 2],
   [0, 0, 2, 3, 3, 0],
   [0, 0, 2, 4, 4, 0],
   [0, 1, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 3 then 1
  else if value = 4 then 2
  else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 3
  else 4

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else if value = 4 then 3
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 5

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS3_15S5_378.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_7962

namespace S6_11025

def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 1, 5 => 1
  | 2, _ => 2
  | 3, 5 => 3
  | 3, _ => 2
  | 4, 1 => 1
  | 4, 4 => 4
  | 5, 3 => 3
  | 5, 5 => 5
  | 5, _ => 2
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cf106375a7a67df2d61bf5d08e8ca9a99375d10e252bb8ecfa254bfff6167202"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 1],
   [2, 2, 2, 2, 2, 2],
   [2, 2, 2, 2, 2, 3],
   [0, 1, 0, 0, 4, 0],
   [2, 2, 2, 3, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  if value = 2 then 1
  else if value = 3 then 1
  else if value = 5 then 1
  else 0

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 2

def ontoLeft : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 2
  else if value = 2 then 0
  else if value = 3 then 1
  else if value = 4 then 3
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 3
  else if value = 2 then 1
  else if value = 3 then 4
  else 5

def ontoRight : SplitSurjection table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S2_4.table.semigroup
    SemigroupBasis.CoRoots.S5_378.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Hash8aSiblingFixedHead.intersectionBasisS2_4S5_378.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11025

end SemigroupBasis.Generated.Order6Hash8aSiblingDirectTargets
