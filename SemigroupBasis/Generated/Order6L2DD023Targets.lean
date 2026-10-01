import SemigroupBasis.CoRoots.Order6L2DD023
import SemigroupBasis.FiniteReflection

/-!
# The two d023 guarded period-two targets

The authenticated order-six representatives below are subdirect products of
`S2_4` with, respectively, `S5_614ᵒᵖ` and `S5_635ᵒᵖ`.  The direct basis is the
three-law guarded period-two basis `B3`; opposite endpoints use only
`BasisFor.oppositeReversed`.

The displayed basis SHA-256 is
`d00c7a7bccd6b2e20a188a2e0d4959ea5ff8f0024e3db057ed4cb0ff88988775`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6L2DD023Targets

open SemigroupBasis

namespace S6_11453

/-! Authenticated zero-based order-six table.  Compact-row SHA-256:
`06fd85dcad4bf88669585127705c5d2900cbcb8f4b0677721fade9dfe66bd420`. -/
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
    else if b = 2 then (1 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (2 : Fin 6)
  else if a = 3 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (3 : Fin 6)
    else if b = 3 then (2 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (3 : Fin 6)
  else if a = 4 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (4 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "06fd85dcad4bf88669585127705c5d2900cbcb8f4b0677721fade9dfe66bd420"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1], [0, 0, 2, 3, 0, 2],
   [0, 0, 3, 2, 0, 3], [4, 4, 4, 4, 4, 4], [0, 1, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2)
  else if a = 1 then (0 : Fin 2)
  else if a = 2 then (0 : Fin 2)
  else if a = 3 then (0 : Fin 2)
  else if a = 4 then (1 : Fin 2)
  else (0 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else (4 : Fin 6)

def ontoS2_4 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_614opMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5)
  else if a = 1 then (1 : Fin 5)
  else if a = 2 then (2 : Fin 5)
  else if a = 3 then (3 : Fin 5)
  else if a = 4 then (0 : Fin 5)
  else (4 : Fin 5)

def ontoS5_614opSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else if a = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoS5_614op :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite where
  toFun := ontoS5_614opMap
  map_mul := by decide
  preimage := ontoS5_614opSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_614op
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3.B3

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3.intersectionBasisS2_4S5_614op.basisFor
    pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11453

namespace S6_11514

/-! Authenticated zero-based order-six table.  Compact-row SHA-256:
`b27c87760a71f46a1088d7a68c423311d9cfb2668622042b1d93c61bbae0135f`. -/
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
    else if b = 2 then (1 : Fin 6)
    else if b = 3 then (1 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (1 : Fin 6)
  else if a = 2 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)
  else if a = 3 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (1 : Fin 6)
    else if b = 2 then (3 : Fin 6)
    else if b = 3 then (2 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)
  else if a = 4 then
    if b = 0 then (4 : Fin 6)
    else if b = 1 then (4 : Fin 6)
    else if b = 2 then (4 : Fin 6)
    else if b = 3 then (4 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (4 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (5 : Fin 6)
    else if b = 3 then (5 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b27c87760a71f46a1088d7a68c423311d9cfb2668622042b1d93c61bbae0135f"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1], [0, 1, 2, 3, 0, 5],
   [0, 1, 3, 2, 0, 5], [4, 4, 4, 4, 4, 4], [0, 0, 5, 5, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2)
  else if a = 1 then (0 : Fin 2)
  else if a = 2 then (0 : Fin 2)
  else if a = 3 then (0 : Fin 2)
  else if a = 4 then (1 : Fin 2)
  else (0 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else (4 : Fin 6)

def ontoS2_4 :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_635opMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5)
  else if a = 1 then (1 : Fin 5)
  else if a = 2 then (2 : Fin 5)
  else if a = 3 then (3 : Fin 5)
  else if a = 4 then (0 : Fin 5)
  else (4 : Fin 5)

def ontoS5_635opSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (1 : Fin 6)
  else if a = 2 then (2 : Fin 6)
  else if a = 3 then (3 : Fin 6)
  else (5 : Fin 6)

def ontoS5_635op :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.opposite where
  toFun := ontoS5_635opMap
  map_mul := by decide
  preimage := ontoS5_635opSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_635.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_635op
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L2DD023GuardedPeriodTwoB3.B3

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L2DD023.intersectionBasisS2_4S5_635op.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11514

end SemigroupBasis.Generated.Order6L2DD023Targets
