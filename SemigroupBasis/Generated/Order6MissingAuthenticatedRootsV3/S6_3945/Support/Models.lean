import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.ModelsPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.ModelsPart01
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.ModelsPart02
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.ModelsPart03
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945

open SemigroupBasis

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.basis := by
  unfold SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945
