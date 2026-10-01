import SemigroupBasis.CoRoots.Order6FactorPairS2S5381Normal
import SemigroupBasis.CoRoots.S5_381Factors
import SemigroupBasis.Generated.S4_31
import SemigroupBasis.Generated.S4_71
import SemigroupBasis.Subdirect

/-!
# Unrestricted L2D rank-41 root: `S4_31op × S4_71`

The exact 13-law system is the delivery-rank-41 design packet with SHA-256
`ba4e34217dcb083d680a3622a00b4ffbf810ca87acc7aa52c909f98a2fc2f769`.
It is literally the existing unrestricted basis for
`S2_2 × S5_381`.  The proof below only reassociates two already certified
subdirect decompositions:

* `S4_31op` is subdirect over `S2_2` and
  `finalMarkerThree.opposite`;
* `S5_381` is subdirect over `S4_71` and the same marker factor.

No bounded closure result is used in the unrestricted theorem.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L2DRank41

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis

def displayedBasisSHA256 : String :=
  "ba4e34217dcb083d680a3622a00b4ffbf810ca87acc7aa52c909f98a2fc2f769"

theorem basis_length : basis.length = 13 := by
  decide

namespace S4_31op

/-! The two zero-based quotient maps are `[0,1,1,0]` and `[0,0,1,2]`. -/

def cyclicMap (a : Fin 4) : Fin 2 :=
  if a = 0 then (0 : Fin 2)
  else if a = 1 then (1 : Fin 2)
  else if a = 2 then (1 : Fin 2)
  else (0 : Fin 2)

def cyclicSection (a : Fin 2) : Fin 4 :=
  if a = 0 then (0 : Fin 4) else (1 : Fin 4)

def cyclicQuotient :
    SplitSurjection
      SemigroupBasis.Generated.S4_31.table.semigroup.opposite
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := cyclicMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := cyclicSection
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def markerMap (a : Fin 4) : Fin 3 :=
  if a = 0 then (0 : Fin 3)
  else if a = 1 then (0 : Fin 3)
  else if a = 2 then (1 : Fin 3)
  else (2 : Fin 3)

def markerSection (a : Fin 3) : Fin 4 :=
  if a = 0 then (0 : Fin 4)
  else if a = 1 then (2 : Fin 4)
  else (3 : Fin 4)

def markerQuotient :
    SplitSurjection
      SemigroupBasis.Generated.S4_31.table.semigroup.opposite
      finalMarkerThree.semigroup.opposite where
  toFun := markerMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := markerSection
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def pair :
    SubdirectPair
      SemigroupBasis.Generated.S4_31.table.semigroup.opposite
      SemigroupBasis.Generated.S2_2.table.semigroup
      finalMarkerThree.semigroup.opposite where
  left := cyclicQuotient
  right := markerQuotient
  jointlyInjective := by
    intro left right
    exact by decide +revert

end S4_31op

private abbrev sourceIntersection :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5381.factorIntersectionBasis

/-! Reassociate the common marker factor:

`Id(S4_31op) ∩ Id(S4_71)`
`= (Id(S2_2) ∩ Id(marker.op)) ∩ Id(S4_71)`
`= Id(S2_2) ∩ Id(S5_381)`.
-/
def factorIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S4_31.table.semigroup.opposite
      SemigroupBasis.Generated.S4_71.table.semigroup
      basis where
  leftModels := by
    intro identity member
    apply (S4_31op.pair.satisfiedBy_iff identity).mpr
    exact
      ⟨sourceIntersection.leftModels identity member,
        SemigroupBasis.CoRoots.S5_381Factors.S5_381.valid_initialMarker
          identity (sourceIntersection.rightModels identity member)⟩
  rightModels := by
    intro identity member
    exact
      SemigroupBasis.CoRoots.S5_381Factors.S5_381.valid_s4_71
        identity (sourceIntersection.rightModels identity member)
  complete := by
    intro identity leftValid rightValid
    have leftFactors :=
      (S4_31op.pair.satisfiedBy_iff identity).mp leftValid
    apply sourceIntersection.complete identity leftFactors.1
    exact
      (SemigroupBasis.CoRoots.S5_381Factors.S5_381.valid_iff_factors
        identity).mpr ⟨rightValid, leftFactors.2⟩

abbrev intersectionBasis := factorIntersectionBasis

end SemigroupBasis.CoRoots.Order6L2DRank41
