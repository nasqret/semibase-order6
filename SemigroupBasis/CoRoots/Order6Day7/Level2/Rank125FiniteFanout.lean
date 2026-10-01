import SemigroupBasis.CoRoots.Order6Day7.Level2.SeedRank125

/-!
# Exact missing rank125 class maps

New-consumer finite-screen SHA-256:
`650491c5d105dafad8d90438ca102d84f13af4d63c95c22f71027851ca81a916`.
Both actual representatives use S3_15 opposite and S5_807 direct.
Finite maps alone are not an unrestricted completeness proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125.FiniteFanout

open SemigroupBasis

namespace S6_13051

def sourceTableSHA256 : String :=
  "5892a66a49037b6f6b18d8545cca74bdfeb2b14130dd824fbfb1f528bac12834"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then if right = 5 then 1 else 0
  else if left = 2 ∨ left = 3 then if right = 5 then 1 else right
  else if left = 4 then 4
  else if right = 5 then 5 else 0

theorem table_rows_exact :
    List.ofFn (fun (left : Fin 6) => List.ofFn (fun (right : Fin 6) => (mul left right).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1],
       [0, 1, 2, 3, 4, 1], [0, 1, 2, 3, 4, 1],
       [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 0, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1 else if value = 3 then 2 else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 2 else 3

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 ∨ value = 3 then 2
  else if value = 4 then 3
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 4
  else 5

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

end S6_13051

namespace S6_13419

def sourceTableSHA256 : String :=
  "0ff2c5e8ec131fc67ab1a5fdc940e891bead7313f68dc2104ef25742213f4d9c"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then if right.val < 4 then 0 else 1
  else if left = 2 then if right.val < 4 then right else 1
  else if left = 3 then 3
  else if right.val < 4 then 0 else right

theorem table_rows_exact :
    List.ofFn (fun (left : Fin 6) => List.ofFn (fun (right : Fin 6) => (mul left right).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1],
       [0, 1, 2, 3, 1, 1], [3, 3, 3, 3, 3, 3],
       [0, 0, 0, 0, 4, 5], [0, 0, 0, 0, 4, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 4 then 1 else if value = 5 then 2 else 0

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 4 else 5

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
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
  else 4

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else if value = 3 then 3
  else 4

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

end S6_13419

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125.FiniteFanout
