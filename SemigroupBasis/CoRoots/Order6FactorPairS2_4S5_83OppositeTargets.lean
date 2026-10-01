import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83OppositeNormal

/-!
# Concrete order-six targets for the `S2_4` / `S5_83^op` factor-pair family

This file binds the unrestricted intersection theorem to the eight authenticated
order-six packet tables carrying canonical basis hash
`33829fb6383259df1407d689c655ef9c3e268b07e7a94d8cd26e1a40f8c11a29`.
The quotient maps are copied from the packet contracts.  Their homomorphism,
surjectivity, and joint-kernel claims are replayed below by kernel reduction.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite
namespace Targets

open SemigroupBasis

private def leftFactor : Semigroup (Fin 2) :=
  SemigroupBasis.Generated.S2_4.table.semigroup

private def rightFactor83 : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite

private def rightFactor84 : Semigroup (Fin 5) :=
  SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite

/-- Common table form for `S6_3810`, `S6_3816`, `S6_3823`, and `S6_3829`.
`rowThreeLast` selects the last entry of row three; `upperLastBlock` selects
the block containing the last element in the left-zero quotient. -/
private def mulA
    (rowThreeLast upperLastBlock : Bool) (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 5 then 1 else 0
  else if a = 2 then if b = 5 then 2 else 0
  else if a = 3 then
    if b = 2 then 1 else if b = 5 then if rowThreeLast then 1 else 0 else 0
  else if a = 4 then 4
  else if b = 5 then 5 else if upperLastBlock then 4 else 0

/-- Common table form for `S6_6433`, `S6_6438`, `S6_6440`, and `S6_6445`. -/
private def mulB
    (rowTwoLast upperLastBlock : Bool) (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then if b = 5 then 1 else 0
  else if a = 2 then
    if b = 4 then 1 else if b = 5 then if rowTwoLast then 1 else 0 else 0
  else if a = 3 then 3
  else if a = 4 then if b = 5 then 4 else 3
  else if b = 5 then 5 else if upperLastBlock then 3 else 0

private def leftMapA (upperLastBlock : Bool) (a : Fin 6) : Fin 2 :=
  if a = 4 then 1 else if a = 5 then if upperLastBlock then 1 else 0 else 0

private def leftMapB (upperLastBlock : Bool) (a : Fin 6) : Fin 2 :=
  if a = 3 then 1
  else if a = 4 then 1
  else if a = 5 then if upperLastBlock then 1 else 0
  else 0

/-- Packet class map `[0,1,2,3,0,4]`, followed by catalogue map
`[0,1,3,2,4]`. -/
private def rightMapA (a : Fin 6) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 3
  else if a = 3 then 2
  else if a = 4 then 0
  else 4

/-- Packet class map `[0,1,2,0,3,4]`; its catalogue map is the identity. -/
private def rightMapB (a : Fin 6) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 0
  else if a = 4 then 3
  else 4

private def leftSectionA (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 4

private def leftSectionB (a : Fin 2) : Fin 6 :=
  if a = 0 then 0 else 3

private def rightSectionA (a : Fin 5) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 3
  else if a = 3 then 2
  else 5

private def rightSectionB (a : Fin 5) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then 1
  else if a = 2 then 2
  else if a = 3 then 4
  else 5

private theorem coordinatesAFalse_injective :
    ∀ a b : Fin 6,
      (leftMapA false a, rightMapA a) =
          (leftMapA false b, rightMapA b) →
        a = b := by
  decide

private theorem coordinatesATrue_injective :
    ∀ a b : Fin 6,
      (leftMapA true a, rightMapA a) =
          (leftMapA true b, rightMapA b) →
        a = b := by
  decide

private theorem coordinatesBFalse_injective :
    ∀ a b : Fin 6,
      (leftMapB false a, rightMapB a) =
          (leftMapB false b, rightMapB b) →
        a = b := by
  decide

private theorem coordinatesBTrue_injective :
    ∀ a b : Fin 6,
      (leftMapB true a, rightMapB a) =
          (leftMapB true b, rightMapB b) →
        a = b := by
  decide

private def rows (table : FiniteTable) : List (List Nat) :=
  (List.finRange table.order).map fun a =>
    (List.finRange table.order).map fun b => (table.mul a b).val

namespace S6_3810

/-- Authenticated Smallsemi table `S6_3810`, SHA-256
`d537442fbc8bd61594db55bb44eec5e541042f768fc78b830d43bdb425064f60`. -/
def table : FiniteTable where
  order := 6
  mul := mulA false false
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 0, 2],
     [0, 0, 1, 0, 0, 0],
     [4, 4, 4, 4, 4, 4],
     [0, 0, 0, 0, 0, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapA false
  map_mul := by decide
  preimage := leftSectionA
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor83 where
  toFun := rightMapA
  map_mul := by decide
  preimage := rightSectionA
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor83 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesAFalse_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_83Opposite pair

end S6_3810

namespace S6_3816

/-- Authenticated Smallsemi table `S6_3816`, SHA-256
`2095a366863d1623ee046ab4aa207f1d32011b7fe83a4e25527a1e9ba76922c9`. -/
def table : FiniteTable where
  order := 6
  mul := mulA false true
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 0, 2],
     [0, 0, 1, 0, 0, 0],
     [4, 4, 4, 4, 4, 4],
     [4, 4, 4, 4, 4, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapA true
  map_mul := by decide
  preimage := leftSectionA
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor83 where
  toFun := rightMapA
  map_mul := by decide
  preimage := rightSectionA
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor83 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesATrue_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_83Opposite pair

end S6_3816

namespace S6_3823

/-- Authenticated Smallsemi table `S6_3823`, SHA-256
`492737b42beed484eef062355692ffa54104c57374f3c771a9ce8ea7b15222f5`. -/
def table : FiniteTable where
  order := 6
  mul := mulA true false
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 0, 2],
     [0, 0, 1, 0, 0, 1],
     [4, 4, 4, 4, 4, 4],
     [0, 0, 0, 0, 0, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapA false
  map_mul := by decide
  preimage := leftSectionA
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor84 where
  toFun := rightMapA
  map_mul := by decide
  preimage := rightSectionA
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor84 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesAFalse_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_84Opposite pair

end S6_3823

namespace S6_3829

/-- Authenticated Smallsemi table `S6_3829`, SHA-256
`c80ef996416f44247cbc219ece64d6256d4716d3ac7ecc87c4a0defd29ce033d`. -/
def table : FiniteTable where
  order := 6
  mul := mulA true true
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 0, 2],
     [0, 0, 1, 0, 0, 1],
     [4, 4, 4, 4, 4, 4],
     [4, 4, 4, 4, 4, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapA true
  map_mul := by decide
  preimage := leftSectionA
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor84 where
  toFun := rightMapA
  map_mul := by decide
  preimage := rightSectionA
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor84 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesATrue_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_84Opposite pair

end S6_3829

namespace S6_6433

/-- Authenticated Smallsemi table `S6_6433`, SHA-256
`2ac99485495ae342869d6df06d77f91f2bc7b5c8182576c5a8763e005922ee8a`. -/
def table : FiniteTable where
  order := 6
  mul := mulB false false
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 1, 0],
     [3, 3, 3, 3, 3, 3],
     [3, 3, 3, 3, 3, 4],
     [0, 0, 0, 0, 0, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapB false
  map_mul := by decide
  preimage := leftSectionB
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor83 where
  toFun := rightMapB
  map_mul := by decide
  preimage := rightSectionB
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor83 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesBFalse_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_83Opposite pair

end S6_6433

namespace S6_6438

/-- Authenticated Smallsemi table `S6_6438`, SHA-256
`f88dec9106a36002f8fa283e2bb201473af80d15e1f868e99ae9f1ddc04a39fe`. -/
def table : FiniteTable where
  order := 6
  mul := mulB false true
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 1, 0],
     [3, 3, 3, 3, 3, 3],
     [3, 3, 3, 3, 3, 4],
     [3, 3, 3, 3, 3, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapB true
  map_mul := by decide
  preimage := leftSectionB
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor83 where
  toFun := rightMapB
  map_mul := by decide
  preimage := rightSectionB
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor83 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesBTrue_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_83Opposite pair

end S6_6438

namespace S6_6440

/-- Authenticated Smallsemi table `S6_6440`, SHA-256
`32c8ee5dd8a63105c4925396683a024d34507ce1f6ae75684d431f74ca7ee21e`. -/
def table : FiniteTable where
  order := 6
  mul := mulB true false
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 1, 1],
     [3, 3, 3, 3, 3, 3],
     [3, 3, 3, 3, 3, 4],
     [0, 0, 0, 0, 0, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapB false
  map_mul := by decide
  preimage := leftSectionB
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor84 where
  toFun := rightMapB
  map_mul := by decide
  preimage := rightSectionB
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor84 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesBFalse_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_84Opposite pair

end S6_6440

namespace S6_6445

/-- Authenticated Smallsemi table `S6_6445`, SHA-256
`b501c3963a9cf2315e00040e5a00e8034b6661e7d2e9eb564f659ad4327e2bbd`. -/
def table : FiniteTable where
  order := 6
  mul := mulB true true
  assoc := by decide

theorem rows_eq : rows table =
    [[0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1],
     [0, 0, 0, 0, 1, 1],
     [3, 3, 3, 3, 3, 3],
     [3, 3, 3, 3, 3, 4],
     [3, 3, 3, 3, 3, 5]] := by
  decide

def ontoLeft : SplitSurjection table.semigroup leftFactor where
  toFun := leftMapB true
  map_mul := by decide
  preimage := leftSectionB
  right_inverse := by decide

def ontoRight : SplitSurjection table.semigroup rightFactor84 where
  toFun := rightMapB
  map_mul := by decide
  preimage := rightSectionB
  right_inverse := by decide

def pair : SubdirectPair table.semigroup leftFactor rightFactor84 where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b same
    exact coordinatesBTrue_injective a b same

theorem basisFor : BasisFor table.semigroup basis :=
  DualNormal.basisForS5_84Opposite pair

end S6_6445

end Targets
end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Opposite
