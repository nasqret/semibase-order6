import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart01
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart02
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart03
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart04
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart05
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart06
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart07
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart08
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart09
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart10
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart11
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart12
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart13
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart14
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart15
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart16
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart17
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart18
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart19
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart20
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart21
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.ModelsPart22
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046

open SemigroupBasis

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.basis := by
  unfold SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_cons targetLaw4Valid <|
              FiniteNilpotentCounterexample.models_cons targetLaw5Valid <|
                FiniteNilpotentCounterexample.models_cons targetLaw6Valid <|
                  FiniteNilpotentCounterexample.models_cons targetLaw7Valid <|
                    FiniteNilpotentCounterexample.models_cons targetLaw8Valid <|
                      FiniteNilpotentCounterexample.models_cons targetLaw9Valid <|
                        FiniteNilpotentCounterexample.models_cons targetLaw10Valid <|
                          FiniteNilpotentCounterexample.models_cons targetLaw11Valid <|
                            FiniteNilpotentCounterexample.models_cons targetLaw12Valid <|
                              FiniteNilpotentCounterexample.models_cons targetLaw13Valid <|
                                FiniteNilpotentCounterexample.models_cons targetLaw14Valid <|
                                  FiniteNilpotentCounterexample.models_cons targetLaw15Valid <|
                                    FiniteNilpotentCounterexample.models_cons targetLaw16Valid <|
                                      FiniteNilpotentCounterexample.models_cons targetLaw17Valid <|
                                        FiniteNilpotentCounterexample.models_cons targetLaw18Valid <|
                                          FiniteNilpotentCounterexample.models_cons targetLaw19Valid <|
                                            FiniteNilpotentCounterexample.models_cons targetLaw20Valid <|
                                              FiniteNilpotentCounterexample.models_cons targetLaw21Valid <|
                                                FiniteNilpotentCounterexample.models_cons targetLaw22Valid <|
                                                  FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9046
