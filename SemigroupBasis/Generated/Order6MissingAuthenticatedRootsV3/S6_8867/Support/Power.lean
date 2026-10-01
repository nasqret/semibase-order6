import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.Core
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.RepresentativeMap
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.TransitionMap

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867

open SemigroupBasis

/-- Reduced term-function states embedded in a finite power of the target. -/
def powerCertificate : RightGeneratedPowerCertificate
    (U := Fin 2712)
    (G := Fin 4)
    (I := Fin 29) oppositeTable.semigroup where
  stateVector := stateVector
  generatorVector := generatorVector
  transition := transition
  representativeHead := representativeHead
  representativeTail := representativeTail
  injective := by
    intro left right equalVectors
    exact
      (decodeState_stateVector left).symm.trans <|
        (congrArg decodeState equalVectors).trans <|
          decodeState_stateVector right
  transition_map := transitionMap
  representative_map := representativeMap

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867
