import SemigroupBasis.CoRoots.Order6LeeZhangClass66

/-!
# Concrete order-six targets in Lee--Zhang class 66

The quotient partitions are

* `[0,0,0,0,0,1]` onto the two-element left-zero semigroup;
* `[0,1,2,3,4,0]` onto `S5_254` for `S6_6536`;
* `[0,1,2,3,4,0]` onto `S5_254^op` for `S6_6602`.

The two quotient coordinates separate all six source elements.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass66
namespace Targets

open SemigroupBasis

private def leftFactor : Semigroup (Fin 2) :=
  SemigroupBasis.Generated.S2_4.table.semigroup

private def rightFactor : Semigroup (Fin 5) :=
  SemigroupBasis.CoRoots.S5_254.table.semigroup

private def rightOppositeFactor : Semigroup (Fin 5) :=
  SemigroupBasis.CoRoots.S5_254.table.semigroup.opposite

private def mul6536 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 3 then 1 else if b = 4 then 1 else 0
  else if a = 2 then
    if b = 3 then 2 else if b = 4 then 2 else 0
  else if a = 3 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2
    else if b = 3 then 3 else if b = 4 then 4 else 0
  else if a = 4 then
    if b = 0 then 0 else if b = 1 then 2 else if b = 2 then 1
    else if b = 3 then 4 else if b = 4 then 3 else 0
  else 5

private def mul6602 (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 3 then 1 else if b = 4 then 2 else 0
  else if a = 2 then
    if b = 3 then 2 else if b = 4 then 1 else 0
  else if a = 3 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2
    else if b = 3 then 3 else if b = 4 then 4 else 0
  else if a = 4 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2
    else if b = 3 then 4 else if b = 4 then 3 else 0
  else 5

private def leftMap (a : Fin 6) : Fin 2 :=
  if a = 5 then 1 else 0

private def rightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 3
  else if a = 4 then 4
  else 0

private def leftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 5

private def rightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 3
  else 4

private theorem coordinates_injective :
    Function.Injective fun value : Fin 6 =>
      (leftMap value, rightMap value) := by
  intro left right
  exact by decide +revert

private def rows (table : FiniteTable) : List (List Nat) :=
  (List.finRange table.order).map fun a =>
    (List.finRange table.order).map fun b => (table.mul a b).val

namespace S6_6536

/-- Authenticated Smallsemi table `S6_6536` in catalogue orientation. -/
def table : FiniteTable where
  order := 6
  mul := mul6536
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 1, 0],
     [0, 0, 0, 2, 2, 0],
     [0, 1, 2, 3, 4, 0],
     [0, 2, 1, 4, 3, 0],
     [5, 5, 5, 5, 5, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMap
  map_mul := by decide
  preimage := leftSection
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor where
  toFun := rightMap
  map_mul := by decide
  preimage := rightSection
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := coordinates_injective

/-- Unconditional complete-basis endpoint for `S6_6536`. -/
theorem basisFor : BasisFor table.semigroup basis :=
  directIntersection.basisFor pair

end S6_6536

namespace S6_6602

/-- Authenticated Smallsemi table `S6_6602` in catalogue orientation. -/
def table : FiniteTable where
  order := 6
  mul := mul6602
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 2, 0],
     [0, 0, 0, 2, 1, 0],
     [0, 1, 2, 3, 4, 0],
     [0, 1, 2, 4, 3, 0],
     [5, 5, 5, 5, 5, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMap
  map_mul := by decide
  preimage := leftSection
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightOppositeFactor where
  toFun := rightMap
  map_mul := by decide
  preimage := rightSection
  right_inverse := by decide

def pair :
    SubdirectPair table.semigroup leftFactor rightOppositeFactor where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := coordinates_injective

/-- Unconditional complete-basis endpoint for `S6_6602`. -/
theorem basisFor : BasisFor table.semigroup basis :=
  oppositeIntersection.basisFor pair

end S6_6602

end Targets
end SemigroupBasis.CoRoots.Order6LeeZhangClass66
