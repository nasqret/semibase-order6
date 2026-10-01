import SemigroupBasis.Subdirect
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.CatalogueOrder5Part05

namespace SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506

open SemigroupBasis

/-- Exact one-based catalogue table hash: `138cb1bd63ba64d8cc1b995efd5c6fd2b6fb3390d779f28d2bcb1e02c569b6bd`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)) else if a = 1 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)) else if a = 2 then (if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)) else if a = 3 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)) else if a = 4 then (if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (0 : Fin 3)

def ontoLeftSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoRightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_636.table.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_636.table.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro a b
    exact by decide +revert

def ontoLeftOpposite :
    SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.S3_6.table.semigroup.opposite where
  toFun := ontoLeftMap
  map_mul := fun a b => ontoLeft.map_mul b a
  preimage := ontoLeftSection
  right_inverse := ontoLeft.right_inverse

def ontoRightOpposite :
    SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_636.table.semigroup.opposite where
  toFun := ontoRightMap
  map_mul := fun a b => ontoRight.map_mul b a
  preimage := ontoRightSection
  right_inverse := ontoRight.right_inverse

def pairOpposite :
    SubdirectPair table.semigroup.opposite
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_636.table.semigroup.opposite where
  left := ontoLeftOpposite
  right := ontoRightOpposite
  jointlyInjective := pair.jointlyInjective

end SemigroupBasis.CoRoots.Order6Day8.S3FiniteWitnesses.Rank014.S6_6506
