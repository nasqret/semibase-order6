import SemigroupBasis.Examples.CommutativePeriodThreeFromTwoOrderFive
import SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.S6_15952

open SemigroupBasis

def routeManifestRowSHA256 : String := "83a8004be2e091d9575e0c713511dd9547871778caee6559904dce0c5a2e1ff4"
def witnessRecordSHA256 : String := "2410f5b4df253f39d411d27d8d48890d7294784b926e17525c51c30a92c9a119"
def sourceTableSHA256 : String := "f7634af6a4bec1264f58700216cba26d5caf62f01e7505515302f5deb52e2a3c"
def targetTableSHA256 : String := "0865e35e26f2526c60be2074dda8d9f2a6a00a04b48c9fc9b7582f243f3a3874"
def sourcePairSHA256 : String := "7e995cc71ce0c858b677914f75fcf884d15da80c52176fac15a71295cc1c72f7"
def targetPairSHA256 : String := "d8641cbbc3e980e6625d745e4555a2ba6f6b008f90cb7f4879c7d4f2af481ecf"

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 3, 3, 2], [0, 1, 2, 3, 3, 5], [2, 2, 3, 0, 0, 3], [3, 3, 0, 2, 2, 0], [3, 4, 0, 2, 2, 0], [2, 5, 3, 0, 0, 3]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoMarkerMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (0 : Fin 3)

def ontoMarkerSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (1 : Fin 6)

def ontoMarker : SplitSurjection table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite where
  toFun := ontoMarkerMap
  map_mul := by decide
  preimage := ontoMarkerSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoExponentMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoExponentSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoExponent : SplitSurjection table.semigroup SemigroupBasis.Examples.s5_1156.semigroup where
  toFun := ontoExponentMap
  map_mul := by decide
  preimage := ontoExponentSection
  right_inverse := by
    intro value
    exact by decide +revert

def targetPair : SubdirectPair table.semigroup
    SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite SemigroupBasis.Examples.s5_1156.semigroup where
  left := ontoMarker
  right := ontoExponent
  jointlyInjective := by
    intro left right
    exact by decide +revert

private theorem rightTheory :
    SameIdentityTheoryOver SemigroupBasis.Examples.s5_1001.semigroup
      SemigroupBasis.Examples.s5_1156.semigroup Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.Examples.s5_1001Basis
    SemigroupBasis.Examples.s5_1156Basis

abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096.basis_complete.transferAcrossSubdirectPairs
    SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9096.sourcePair targetPair
    (fun _ => Iff.rfl) rightTheory

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.S6_15952
