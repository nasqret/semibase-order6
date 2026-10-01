import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.TransitionMapProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Support.Core

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979

open SemigroupBasis

theorem transitionMap :
    ∀ (state : Fin 7782)
      (generator : Fin 6)
      (coordinate : Fin 22),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul
          (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  exact Shards.transitionMap state generator coordinate

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979
