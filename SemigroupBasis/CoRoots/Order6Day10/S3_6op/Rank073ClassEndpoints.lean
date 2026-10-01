import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection

/-! S1 replica consumer under fable msg-0379 whole-family ownership.
The two quotient maps are copied from the exact existing Rank073 contracts;
The canonical contract has opposite orientation; direct B12 is its exact literal word reversal.
No finite search or new mathematical witness is introduced. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay

namespace S6_3334

/-- Exact catalogue table SHA256: 760e1c26ce292f964bc12849464bbac34c1dfbb628e1227c145d9440cdbf5b87. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)

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
  SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection.basisForOfFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pairOpposite

theorem models : Models table.semigroup basis := basisFor.1

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_3334

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073ClassEndpoints
