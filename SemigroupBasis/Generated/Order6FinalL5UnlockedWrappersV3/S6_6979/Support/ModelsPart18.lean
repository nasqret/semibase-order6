import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979

open SemigroupBasis

private def targetLaw18ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw18FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem targetLaw18Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.law18.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative.law18
    targetLaw18ToFinite targetLaw18FromFinite (by decide) (by decide)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979
