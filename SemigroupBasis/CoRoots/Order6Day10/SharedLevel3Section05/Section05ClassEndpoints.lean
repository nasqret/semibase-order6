import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Intersection

/-! Four actual B6 class endpoints and their opposites.
Two root quotient pairs are replicated from exact frozen contracts.
The two leaves use separate root-into-leaf-power embeddings and literal Models.
No root quotient is mislabeled as a leaf transport. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05ClassEndpoints

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Intersection

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

namespace S6_13171

/-- Exact one-based catalogue table SHA256: 1237f8aa9139b6660fac9e5bfdc948a93897122a80259eb27e9b8343fbfdfb6b. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 3], [3, 3, 3, 3, 3, 3], [1, 1, 1, 4, 5, 1], [1, 1, 1, 4, 5, 1], [6, 6, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (0 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (leftTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (0 : Fin 4) else if a = 4 then (0 : Fin 4) else (3 : Fin 4)

def ontoRightSection (a : Fin 4) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)

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

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13171

namespace S6_13196

/-- Exact one-based catalogue table SHA256: 7d85061953359d96f98854d2fe6ea91491ee56ba0aea0c99333d14430a144000. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if a = 4 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 4, 5, 3], [3, 3, 3, 4, 5, 3], [6, 6, 6, 6, 6, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6)

def rootHom0 : Hom S6_13171.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def rootHom1 : Hom S6_13171.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def family (i : Fin 2) : Hom S6_13171.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 2, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding S6_13171.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  S6_13171.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13196

namespace S6_13777

/-- Exact one-based catalogue table SHA256: b091c79869eb4ed132e02819b3b0b787b1c4d01b391eecb57ec89735de86d75f. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)) else if a = 4 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1], [1, 1, 1, 3, 3, 3], [3, 3, 3, 3, 3, 3], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 5, 6], [4, 4, 4, 4, 5, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def rootHom0Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6)

def rootHom0 : Hom S6_13171.table.semigroup table.semigroup where
  toFun := rootHom0Map
  map_mul := by decide

def rootHom1Map (a : Fin 6) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def rootHom1 : Hom S6_13171.table.semigroup table.semigroup where
  toFun := rootHom1Map
  map_mul := by decide

def family (i : Fin 2) : Hom S6_13171.table.semigroup table.semigroup :=
  if i = 0 then rootHom0 else rootHom1

theorem family_separates : ∀ a b : Fin 6,
    (∀ i : Fin 2, (family i).toFun a = (family i).toFun b) → a = b := by decide

def rootPowerEmbedding : Embedding S6_13171.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms family family_separates

theorem basisFor : BasisFor table.semigroup basis :=
  S6_13171.basisFor.inheritAlongPowerEmbedding rootPowerEmbedding models

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basisFor.oppositeReversed

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_13777

namespace S6_14271

/-- Exact one-based catalogue table SHA256: 719a735f443abd9ea1a6ec52cbca8cdbe3c3662a4fb2317036e316763912d5d2. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 2 then (if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 3 then (if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 5, 6], [1, 1, 1, 3, 5, 6], [3, 3, 3, 3, 5, 6], [4, 4, 4, 4, 5, 6], [5, 5, 5, 5, 5, 6], [5, 5, 5, 5, 5, 6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def ontoLeftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (0 : Fin 2) else if a = 4 then (0 : Fin 2) else (1 : Fin 2)

def ontoLeftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (5 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup (alternateLeftTable.semigroup) where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoRight : SplitSurjection table.semigroup (alternateRightTable.semigroup) where
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

def ontoLeftOpposite : SplitSurjection table.semigroup.opposite (alternateLeftTable.semigroup).opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite : SplitSurjection table.semigroup.opposite (alternateRightTable.semigroup).opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite : SubdirectPair table.semigroup.opposite alternateLeftTable.semigroup.opposite alternateRightTable.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

theorem basisFor : BasisFor table.semigroup basis :=
  basisForOfAlternateFinitePair table pair

theorem basisForOpposite : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  alternateIntersectionBasis.oppositeReversed.basisFor pairOpposite

theorem modelsOpposite : Models table.semigroup.opposite (reversedBasis basis) := basisForOpposite.1

end S6_14271

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05ClassEndpoints
