import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.TransitionMapProof
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.Core

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867

open SemigroupBasis

theorem transitionMap :
    ∀ (state : Fin 2712)
      (generator : Fin 4)
      (coordinate : Fin 29),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul
          (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  exact Shards.transitionMap state generator coordinate

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867
