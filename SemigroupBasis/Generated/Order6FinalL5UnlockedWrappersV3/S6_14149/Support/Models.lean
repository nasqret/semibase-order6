import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.ModelsPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149

open SemigroupBasis

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_cons targetLaw6Valid <|
                  FiniteNilpotentCounterexample.models_cons targetLaw7Valid <|
                    FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149
