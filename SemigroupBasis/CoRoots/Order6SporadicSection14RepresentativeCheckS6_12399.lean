import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12399Part01
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12399Part02
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12399Part03
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_12399Part04

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_12399

theorem representativeModels : Models table.semigroup alphaBasis := by
  rw [alphaBasis_eq_parts]
  exact modelsAppend (modelsAppend (modelsAppend modelsPart01 modelsPart02) modelsPart03) modelsPart04

theorem publishedModels :
    Models publishedSemigroup alphaBasis :=
  representativeModels

end S6_12399

end SemigroupBasis.CoRoots.Order6SporadicSection14
