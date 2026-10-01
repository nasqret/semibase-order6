import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Shards.TransitionMapProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841.Support.Core

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841

open SemigroupBasis

theorem transitionMap :
    ∀ (state : Fin 4374)
      (generator : Fin 6)
      (coordinate : Fin 28),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul
          (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  exact Shards.transitionMap state generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6841
