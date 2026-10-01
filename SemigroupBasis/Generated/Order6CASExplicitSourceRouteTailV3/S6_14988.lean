import SemigroupBasis.CoRoots.S5_1007Family
import SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9113
import SemigroupBasis.Order6Subdirect.HullFamilyTransfers

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.S6_14988

open SemigroupBasis

def routeManifestRowSHA256 : String := "5cfb41b908c452ef4c7791393b6d2d6d317cd11f728860744e227878e016b47c"
def witnessRecordSHA256 : String := "68a7457bd10f7ae88a2622cfd7dfb72807ef94e2fd2282cf8e47ed5ea9adb278"
def sourceTableSHA256 : String := "1ccbbaed9ad24950153b0ce7b8895a004c187ce692592176589d09f394ef670e"
def targetTableSHA256 : String := "b6f21af91591e863ccd1bb1c4609e6a575a3cb573d6da40d6898206191d3f654"
def sourcePairSHA256 : String := "739abd08b7ef2f2705a4b63c9d8d1bf20f2baa91f40a052417e6160101b30dd3"
def targetPairSHA256 : String := "f990822a87228f7aa13ee91ccc2e5fa997ec0dee56b3f6ac60d3d4dedd952c50"

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def publishedRows : List (List Nat) :=
  [[0, 1, 2, 3, 4, 4], [1, 0, 2, 3, 4, 4], [2, 2, 2, 3, 4, 4], [3, 3, 3, 4, 2, 2], [4, 4, 4, 2, 3, 3], [5, 5, 4, 2, 3, 3]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoMarkerMap (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (1 : Fin 3)

def ontoMarkerSection (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (5 : Fin 6) else (0 : Fin 6)

def ontoMarker : SplitSurjection table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite where
  toFun := ontoMarkerMap
  map_mul := by decide
  preimage := ontoMarkerSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoExponentMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (4 : Fin 5)

def ontoExponentSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoExponent : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup where
  toFun := ontoExponentMap
  map_mul := by decide
  preimage := ontoExponentSection
  right_inverse := by
    intro value
    exact by decide +revert

def targetPair : SubdirectPair table.semigroup
    SemigroupBasis.Examples.finalMarkerThree.semigroup.opposite SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup where
  left := ontoMarker
  right := ontoExponent
  jointlyInjective := by
    intro left right
    exact by decide +revert

private theorem rightTheory :
    SameIdentityTheoryOver SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup
      SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup Nat :=
  SemigroupBasis.Order6Subdirect.HullFamilyTransfers.sameIdentityTheoryOver_of_common_basis
    SemigroupBasis.CoRoots.S5_1007Family.S5_1007.representative_basis
    SemigroupBasis.CoRoots.S5_1007Family.S5_1008.representative_basis

abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9113.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9113.basis_complete.transferAcrossSubdirectPairs
    SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.Sources.S6_9113.sourcePair targetPair
    (fun _ => Iff.rfl) rightTheory

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceRouteTailV3.S6_14988
