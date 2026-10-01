import SemigroupBasis.CoRoots.Order6L2DD029
import SemigroupBasis.FiniteReflection

/-!
# The two d029 mod-three/component B16 targets

The authenticated order-six representatives below are literal subdirect
products of `S4_124 × S4_70` and `S4_125 × S4_70`, respectively.  Their
representative endpoints inherit the exact sixteen-law B16 intersection
bases.  Opposite endpoints use only `BasisFor.oppositeReversed` and therefore
carry literal `reversedBasis B16`.

The displayed B16 SHA-256 is
`b07f6a78d49156d1f94c23451b6dd52ef448b2a5158cb108cbd7bf928781d65e`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6L2DD029Targets

open SemigroupBasis

namespace S6_14915

/-! Authenticated zero-based order-six table. Compact-row SHA-256:
`28457beee4c50f3e4c124a2f8f891b3344e13a9c261b2bb9a822c0348c7711e3`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 3 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if a = 4 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (5 : Fin 6)
    else (2 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (5 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (2 : Fin 6)
    else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "28457beee4c50f3e4c124a2f8f891b3344e13a9c261b2bb9a822c0348c7711e3"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 2, 1, 4, 5],
   [0, 0, 0, 3, 0, 0], [0, 1, 4, 1, 5, 2], [0, 1, 5, 1, 2, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_124Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (0 : Fin 4)
  else if a = 2 then (1 : Fin 4)
  else if a = 3 then (0 : Fin 4)
  else if a = 4 then (2 : Fin 4)
  else (3 : Fin 4)

def ontoS4_124Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (2 : Fin 6)
  else if a = 2 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoS4_124 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_124.table.semigroup where
  toFun := ontoS4_124Map
  map_mul := by decide
  preimage := ontoS4_124Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_70Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (1 : Fin 4)
  else if a = 2 then (2 : Fin 4)
  else if a = 3 then (3 : Fin 4)
  else if a = 4 then (2 : Fin 4)
  else (2 : Fin 4)

def ontoS4_70Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else (3 : Fin 6)

def ontoS4_70 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup where
  toFun := ontoS4_70Map
  map_mul := by decide
  preimage := ontoS4_70Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup where
  left := ontoS4_124
  right := ontoS4_70
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD029.B16

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD029.intersectionBasisS4_124S4_70.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14915

namespace S6_14938

/-! Authenticated zero-based order-six table. Compact-row SHA-256:
`8781d367b55b445d9a2d9401a9fba9ba2670a4c41ed4c2d4fa1f75015ef7efc0`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 3 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else if a = 4 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (4 : Fin 6)
    else if b = 4 then (5 : Fin 6)
    else (0 : Fin 6)
  else
    if b = 0 then (5 : Fin 6)
    else if b = 1 then (5 : Fin 6)
    else if b = 2 then (5 : Fin 6)
    else if b = 3 then (5 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8781d367b55b445d9a2d9401a9fba9ba2670a4c41ed4c2d4fa1f75015ef7efc0"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5], [0, 0, 0, 1, 4, 5], [0, 1, 2, 1, 4, 5],
   [0, 0, 0, 3, 4, 5], [4, 4, 4, 4, 5, 0], [5, 5, 5, 5, 0, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS4_125Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (0 : Fin 4)
  else if a = 2 then (0 : Fin 4)
  else if a = 3 then (1 : Fin 4)
  else if a = 4 then (2 : Fin 4)
  else (3 : Fin 4)

def ontoS4_125Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (3 : Fin 6)
  else if a = 2 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoS4_125 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup where
  toFun := ontoS4_125Map
  map_mul := by decide
  preimage := ontoS4_125Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS4_70Map (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (1 : Fin 4)
  else if a = 2 then (2 : Fin 4)
  else if a = 3 then (3 : Fin 4)
  else if a = 4 then (0 : Fin 4)
  else (0 : Fin 4)

def ontoS4_70Section (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else (3 : Fin 6)

def ontoS4_70 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup where
  toFun := ontoS4_70Map
  map_mul := by decide
  preimage := ontoS4_70Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.S4_70.table.semigroup where
  left := ontoS4_125
  right := ontoS4_70
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD029.B16

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD029.intersectionBasisS4_125S4_70.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14938

end SemigroupBasis.Generated.Order6L2DD029Targets
