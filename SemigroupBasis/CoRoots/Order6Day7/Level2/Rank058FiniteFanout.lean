import SemigroupBasis.CoRoots.Order6Day7.Level2.SeedRank058

/-!
# Exact missing S6_5579 finite contract

The literal table and split maps are those in the original direct:17
S3_15/S5_203 payload, not a finite-model inference of completeness.
New-consumer screen SHA:
`1559f84b3f4e5acb169c57460518dac254dce093de4cce939f54df1d96e39ebd`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058.FiniteFanout.S6_5579

open SemigroupBasis

def sourceTableSHA256 : String :=
  "62f3c5f57b83804ff6ff7ed81f93695b56dccf4b0757d5d423db143dcb86f42b"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left.val < 4 then if right = 3 then 1 else 0
  else if right = 0 then 0
  else if right = 1 then 1
  else if right = 2 ∨ right = 3 then 2
  else left

theorem table_rows_exact :
    List.ofFn (fun (left : Fin 6) => List.ofFn (fun (right : Fin 6) => (mul left right).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0],
       [0, 1, 2, 2, 4, 4], [0, 1, 2, 2, 5, 5]] := by decide

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

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058.FiniteFanout.S6_5579
