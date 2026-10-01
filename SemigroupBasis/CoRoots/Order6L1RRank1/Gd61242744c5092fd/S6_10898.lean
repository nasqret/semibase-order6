import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.RouteIntersection

/-! Exact representative and opposite cap-two endpoints for `S6_10898`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.S6_10898

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then 0 else if right = 1 then 0 else if right = 2 then 0 else
    if right = 3 then 0 else if right = 4 then 0 else 0
  else if left = 1 then
    if right = 0 then 0 else if right = 1 then 0 else if right = 2 then 0 else
    if right = 3 then 0 else if right = 4 then 0 else 1
  else if left = 2 then
    if right = 0 then 0 else if right = 1 then 1 else if right = 2 then 2 else
    if right = 3 then 2 else if right = 4 then 2 else 2
  else if left = 3 then
    if right = 0 then 0 else if right = 1 then 1 else if right = 2 then 2 else
    if right = 3 then 2 else if right = 4 then 2 else 3
  else if left = 4 then
    if right = 0 then 0 else if right = 1 then 1 else if right = 2 then 2 else
    if right = 3 then 3 else if right = 4 then 4 else 3
  else
    if right = 0 then 0 else if right = 1 then 1 else if right = 2 then 2 else
    if right = 3 then 2 else if right = 4 then 2 else 5

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1],
   [0, 1, 2, 2, 2, 2], [0, 1, 2, 2, 2, 3],
   [0, 1, 2, 3, 4, 3], [0, 1, 2, 2, 2, 5]]

theorem mul_matches_published :
    ((List.finRange 6).map fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

def projLeft (value : Fin 6) : Fin 4 :=
  if value = 0 then 0 else if value = 1 then 0 else if value = 2 then 0 else
  if value = 3 then 1 else if value = 4 then 2 else 3

def secLeft (value : Fin 4) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 3 else if value = 2 then 4 else 5

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_70.table.semigroup where
  toFun := projLeft
  map_mul := by decide
  preimage := secLeft
  right_inverse := by decide

def projRight (value : Fin 6) : Fin 4 :=
  if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else
  if value = 3 then 2 else if value = 4 then 2 else 3

def secRight (value : Fin 4) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1 else if value = 2 then 2 else 5

def ontoRight : SplitSurjection table.semigroup SemanticBlockSignature.table.semigroup where
  toFun := projRight
  map_mul := by decide
  preimage := secRight
  right_inverse := by decide

private theorem jointly_injective :
    ∀ left right : Fin 6,
      (projLeft left, projRight left) =
        (projLeft right, projRight right) → left = right := by
  decide

def subdirect :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup SemanticBlockSignature.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right agreement
    exact jointly_injective left right agreement

theorem representative_basis :
    BasisFor table.semigroup
      SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.basis :=
  SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.intersectionBasis.basisFor
    subdirect

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.S6_10898
