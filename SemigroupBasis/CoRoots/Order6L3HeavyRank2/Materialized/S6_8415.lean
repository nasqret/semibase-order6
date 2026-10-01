import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCompleteness

/-!
# Authenticated Layer-C representative `S6_8415`

Factor pair: `S3_15op x S5_381`. Both coordinate maps are copied from
the authenticated `subdirect408.json` witness and independently validated
against the committed order-six class table and lower-order factor tables.
The unrestricted basis is supplied by the already kernel-green Layer-C
constructor; no factor separation or missing witness is manufactured.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.Materialized.S6_8415

open SemigroupBasis

abbrev leftTable : FiniteTable := SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable

abbrev rightTable : FiniteTable := SemigroupBasis.Generated.Catalogue.S5_381.table

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (1 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (1 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (1 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3)
  else if value = 1 then (0 : Fin 3)
  else if value = 2 then (0 : Fin 3)
  else if value = 3 then (0 : Fin 3)
  else if value = 4 then (1 : Fin 3)
  else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (3 : Fin 5)
  else if value = 4 then (4 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (3 : Fin 6)
  else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

theorem representative_basis :
    BasisFor table.semigroup
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381 :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisForS3_15opS5_381 pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.Materialized.S6_8415
