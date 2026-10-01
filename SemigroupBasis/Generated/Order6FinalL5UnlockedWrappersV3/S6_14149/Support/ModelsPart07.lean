import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149.Support.Quotient

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149

open SemigroupBasis

private def targetLaw7ToFinite : Nat -> Fin 4
  | 0 => (0 : Fin 4)
  | 1 => (1 : Fin 4)
  | 2 => (2 : Fin 4)
  | 3 => (3 : Fin 4)
  | _ => (0 : Fin 4)

private def targetLaw7FromFinite (index : Fin 4) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem targetLaw7Valid :
    SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.law7.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7644Representative.law7
    targetLaw7ToFinite targetLaw7FromFinite (by decide) (by decide)

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14149
