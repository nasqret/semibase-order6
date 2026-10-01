import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Shards.SourceLabelTransitionProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845.Support.Core

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845

open SemigroupBasis

theorem sourceLabelTransition :
    ∀ (state : Fin 4374)
      (generator : Fin 6),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_6196Representative.sourceSemigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  exact Shards.sourceLabelTransition state generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6845
