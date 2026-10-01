import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12198Part01
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12198Part02
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12198Part03
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12198Part04

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_12198

theorem representativeModels : Models table.semigroup betaBasis := by
  rw [betaBasis_eq_parts]
  exact modelsAppend (modelsAppend (modelsAppend modelsPart01 modelsPart02) modelsPart03) modelsPart04

theorem publishedModels :
    Models publishedSemigroup betaBasis :=
  representativeModels

end S6_12198

end SemigroupBasis.CoRoots.Order6SporadicSection14
