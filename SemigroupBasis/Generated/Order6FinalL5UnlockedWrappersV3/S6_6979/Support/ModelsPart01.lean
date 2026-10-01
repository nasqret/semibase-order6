import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979

open SemigroupBasis

private def targetLaw1ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw1FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem targetLaw1Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979
