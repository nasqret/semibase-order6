import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Support.ModelsPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Support.ModelsPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268

open SemigroupBasis

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268
