import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Shards.SourceLabelTransitionProof
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867.Support.Core

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867

open SemigroupBasis

theorem sourceLabelTransition :
    ∀ (state : Fin 2712)
      (generator : Fin 4),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_11390.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  exact Shards.sourceLabelTransition state generator

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_8867
