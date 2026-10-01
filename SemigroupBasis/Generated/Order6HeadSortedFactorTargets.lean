import SemigroupBasis.CoRoots.Order6HeadSortedFactorIntersections

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6HeadSortedFactorTargets

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6HeadSortedFactorIntersections

namespace S6_5689

/-- Authenticated order-six table, SHA-256 `564d1c4ecc953ecde4e221a9361424535e76f5966966e3fe870012072ae1c518`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)
  else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "564d1c4ecc953ecde4e221a9361424535e76f5966966e3fe870012072ae1c518"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 2], [0, 2, 0, 1, 0, 3], [4, 4, 4, 4, 4, 4], [0, 1, 2, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (5 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftNormalBandThree.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_217.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftNormalBandThree.semigroup
    SemigroupBasis.CoRoots.S5_217.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedCappedFourBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  cappedFourS3_13S5_217.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5689

namespace S6_5692

/-- Authenticated order-six table, SHA-256 `59fcff60857f201ba751c2ea9adc9c36be7712fa1845d57952a535b9555c3a99`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)
  else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "59fcff60857f201ba751c2ea9adc9c36be7712fa1845d57952a535b9555c3a99"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 2, 1, 1], [0, 0, 0, 0, 2, 2], [0, 2, 0, 1, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftNormalBandFifteen.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_217.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftNormalBandFifteen.semigroup
    SemigroupBasis.CoRoots.S5_217.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedCappedFourBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  cappedFourS3_15S5_217.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5692

namespace S6_5740

/-- Authenticated order-six table, SHA-256 `14c6c9c0dfc40b8d8debd00b516285c3193c1b4b0ae305fcc130afde96c4062d`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)
  else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "14c6c9c0dfc40b8d8debd00b516285c3193c1b4b0ae305fcc130afde96c4062d"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 0, 0, 0], [0, 0, 2, 0, 1, 1], [2, 2, 0, 2, 2, 2], [0, 0, 2, 1, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftNormalBandFifteen.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_223.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftNormalBandFifteen.semigroup
    s5_223.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodTwoFromThreeBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  indexThreePeriodTwoS3_15S5_223.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5740

namespace S6_5754

/-- Authenticated order-six table, SHA-256 `038da660527ea7affea0969bbb209082dd60e6a27281be77e8e0b5028461bdf7`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)
  else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "038da660527ea7affea0969bbb209082dd60e6a27281be77e8e0b5028461bdf7"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 2, 0, 0], [0, 0, 2, 2, 1, 1], [2, 2, 0, 0, 2, 2], [2, 2, 0, 1, 3, 3], [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftNormalBandFifteen.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_226.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftNormalBandFifteen.semigroup
    s5_226.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodTwoFromThreeBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  indexThreePeriodTwoS3_15S5_226.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5754

namespace S6_9595

/-- Authenticated order-six table, SHA-256 `27ab81b122f764c0a3b6f32d528f9a41a7a84f8cbc28910fa3adc8edca47815e`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (0 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (0 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (3 : Fin 6) else (0 : Fin 6)
  else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "27ab81b122f764c0a3b6f32d528f9a41a7a84f8cbc28910fa3adc8edca47815e"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0], [0, 0, 1, 2, 2, 0], [0, 1, 2, 3, 4, 0], [0, 1, 2, 4, 3, 0], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftNormalBandThree.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (0 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_514.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftNormalBandThree.semigroup
    s5_514.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodTwoFromThreeBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  indexThreePeriodTwoS3_13S5_514.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9595

namespace S6_14922

/-- Authenticated order-six table, SHA-256 `182deff9eb0dc0f29054d813a0db72d971796ec8a6798f3d32f988c3d9e3d776`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (3 : Fin 6)
  else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "182deff9eb0dc0f29054d813a0db72d971796ec8a6798f3d32f988c3d9e3d776"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 1], [2, 2, 2, 2, 2, 2], [0, 1, 0, 3, 4, 5], [0, 1, 0, 4, 5, 3], [0, 1, 0, 5, 3, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (1 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoLeftSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (0 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_1001.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1146.table.semigroup
    s5_1001.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodThreeFromTwoBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  periodThreeS5_1146S5_1001.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14922

namespace S6_14941

/-- Authenticated order-six table, SHA-256 `21c0e8d0053359ab76f1dd34254c0965aafd471f273ec1d410659747376d92d0`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 3 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (0 : Fin 6)
  else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (0 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "21c0e8d0053359ab76f1dd34254c0965aafd471f273ec1d410659747376d92d0"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 5], [0, 0, 1, 1, 4, 5], [0, 1, 2, 2, 4, 5], [0, 1, 3, 3, 4, 5], [4, 4, 4, 4, 5, 0], [5, 5, 5, 5, 0, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoLeftSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_1004.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup
    s5_1004.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodThreeFromTwoBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  periodThreeS5_1152S5_1004.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14941

namespace S6_15934

/-- Authenticated order-six table, SHA-256 `a44703e7413f414fb9f11f1b4bea1f150f66d668467d3716ae7a4516136f5010`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)
  else if left = 3 then
    if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6)
  else if left = 4 then
    if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)
  else if right = 0 then (4 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a44703e7413f414fb9f11f1b4bea1f150f66d668467d3716ae7a4516136f5010"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 3, 4, 4], [0, 1, 1, 3, 4, 5], [0, 2, 2, 3, 4, 5], [3, 3, 3, 4, 0, 0], [4, 4, 4, 0, 3, 3], [4, 5, 5, 0, 3, 3]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoLeftMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoLeftSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup s5_1156.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.CoRoots.S5_1146.S5_1152.table.semigroup
    s5_1156.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := headSortedPeriodThreeFromTwoBasis

/-- Complete basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  periodThreeS5_1152S5_1156.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_15934

end SemigroupBasis.Generated.Order6HeadSortedFactorTargets
