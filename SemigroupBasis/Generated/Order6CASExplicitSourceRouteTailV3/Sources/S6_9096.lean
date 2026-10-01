import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots

namespace SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096

open SemigroupBasis

def sourcePairSHA256 : String := "7e995cc71ce0c858b677914f75fcf884d15da80c52176fac15a71295cc1c72f7"
abbrev sourceSemigroup := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_9096.table.semigroup.opposite

def ontoMarkerMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (1 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoMarkerSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)

def ontoMarker : SplitSurjection sourceSemigroup SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite where
  toFun := ontoMarkerMap
  map_mul := by decide
  preimage := ontoMarkerSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoExponentMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoExponentSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoExponent : SplitSurjection sourceSemigroup SemigroupBasis.Examples.s5_1001.semigroup where
  toFun := ontoExponentMap
  map_mul := by decide
  preimage := ontoExponentSection
  right_inverse := by
    intro value
    exact by decide +revert

def sourcePair : SubdirectPair sourceSemigroup
    SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite SemigroupBasis.Examples.s5_1001.semigroup where
  left := ontoMarker
  right := ontoExponent
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.oppositeBasis

theorem basis_complete : BasisFor sourceSemigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_9096.opposite_basis

end SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096
