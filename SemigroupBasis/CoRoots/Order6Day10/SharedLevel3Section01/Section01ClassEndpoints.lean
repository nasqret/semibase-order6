import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Intersection

/-! S1 fixed-map replica under msg-0379/0380.
Four actual catalogue representatives, two exact DIRECT factor-pair routes.
The displayed B23 is the frozen raw order (reverse of the canonical presentation).
Eight existing quotient maps are replicated; no finite search is performed. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Intersection

namespace S6_3079

/-- Exact one-based catalogue table SHA256: 289204a26cf57488ebd69b9a466bc96cb6e4f8a6d298398a4d69e63f597f5c17. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (leftTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup (rightTable.semigroup) where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : FinitePair table where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite (leftTable.semigroup).opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite (rightTable.semigroup).opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis :=
  basisForOfFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_3079

namespace S6_3141

/-- Exact one-based catalogue table SHA256: 6d7f6a8dab28573d69d82a7958bcbfbdedfb03b24655f7a3035f141778a27750. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 2 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (1 : Fin 2) else if a = 2 then (1 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (0 : Fin 2) else (0 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (leftTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup (rightTable.semigroup) where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : FinitePair table where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite (leftTable.semigroup).opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite (rightTable.semigroup).opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis :=
  basisForOfFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_3141

namespace S6_5793

/-- Exact one-based catalogue table SHA256: 4b31fb7c8443e3addb5f99596ea6373b0c5050d0148bd6c785b6041684862323. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (0 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (alternateTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup (rightTable.semigroup) where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : AlternateFinitePair table where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite (alternateTable.semigroup).opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite (rightTable.semigroup).opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite alternateTable.semigroup.opposite rightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis :=
  basisForOfAlternateFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  alternateIntersectionBasis.oppositeReversed.basisFor pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_5793

namespace S6_5794

/-- Exact one-based catalogue table SHA256: 11f0413c6368331931e27518873132bdd7e5d7f1c42cc56c3be329040bcbb61a. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (1 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (alternateTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup (rightTable.semigroup) where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : AlternateFinitePair table where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite (alternateTable.semigroup).opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite (rightTable.semigroup).opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite alternateTable.semigroup.opposite rightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis :=
  basisForOfAlternateFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  alternateIntersectionBasis.oppositeReversed.basisFor pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_5794

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01ClassEndpoints
