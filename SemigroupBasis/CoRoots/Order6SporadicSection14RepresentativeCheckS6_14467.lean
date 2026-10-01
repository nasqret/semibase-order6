import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_14467Part01
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_14467Part02
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_14467Part03
import SemigroupBasis.CoRoots.Order6SporadicSection14CheckS6_14467Part04

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_14467

theorem representativeModels : Models table.semigroup oppositeBetaBasis := by
  rw [oppositeBetaBasis_eq_parts]
  exact modelsAppend (modelsAppend (modelsAppend modelsPart01 modelsPart02) modelsPart03) modelsPart04

theorem publishedModels :
    Models publishedSemigroup betaBasis := by
  simpa [publishedSemigroup, oppositeBetaBasis] using
    representativeModels.oppositeReversed

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
