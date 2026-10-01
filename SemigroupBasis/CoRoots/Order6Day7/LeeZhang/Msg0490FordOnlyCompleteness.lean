import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlyNormalForms

/-! The two remaining siblings need only the exact finite power embeddings
requested from S3. No arbitrary-word premise remains. These declarations
are explicitly conditional and are not positive class endpoints yet. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Order6Sunday

abbrev Transfer5563 := Embedding L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
  (FordOnlyExactFinite.S6_5563.table.semigroup.pi (Fin 3))
abbrev Transfer9657 := Embedding L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
  (FordOnlyExactFinite.S6_9657.table.semigroup.pi (Fin 3))

theorem representative_basis5563_of_transfer (transfer : Transfer5563) :
    BasisFor FordOnlyExactFinite.S6_5563.table.semigroup basis :=
  representative_basis5553.inheritAlongPowerEmbedding transfer FordOnlyExactFinite.S6_5563.models

theorem opposite_basis5563_of_transfer (transfer : Transfer5563) :
    BasisFor FordOnlyExactFinite.S6_5563.table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis5563_of_transfer transfer).oppositeReversed

theorem representative_basis9657_of_transfer (transfer : Transfer9657) :
    BasisFor FordOnlyExactFinite.S6_9657.table.semigroup basis :=
  representative_basis5553.inheritAlongPowerEmbedding transfer FordOnlyExactFinite.S6_9657.models

theorem opposite_basis9657_of_transfer (transfer : Transfer9657) :
    BasisFor FordOnlyExactFinite.S6_9657.table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis9657_of_transfer transfer).oppositeReversed

theorem signature_of_valid5563_of_transfer (transfer : Transfer5563) (identity : Identity Nat)
    (valid : identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_valid5553 identity
    (transfer.pullback_identity identity (identity.satisfiedByPi _ (Fin 3) valid))

theorem signature_of_valid9657_of_transfer (transfer : Transfer9657) (identity : Identity Nat)
    (valid : identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_valid5553 identity
    (transfer.pullback_identity identity (identity.satisfiedByPi _ (Fin 3) valid))

theorem normal_eq_iff_valid5563_of_transfer (transfer : Transfer5563) (identity : Identity Nat) :
    normal identity.lhs = normal identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup :=
  normal_eq_iff_valid_of_basis _ (representative_basis5563_of_transfer transfer) identity

theorem oppositeNormal_eq_iff_valid5563_of_transfer (transfer : Transfer5563) (identity : Identity Nat) :
    oppositeNormal identity.lhs = oppositeNormal identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid_of_basis _ (representative_basis5563_of_transfer transfer) identity

theorem normal_eq_iff_valid9657_of_transfer (transfer : Transfer9657) (identity : Identity Nat) :
    normal identity.lhs = normal identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup :=
  normal_eq_iff_valid_of_basis _ (representative_basis9657_of_transfer transfer) identity

theorem oppositeNormal_eq_iff_valid9657_of_transfer (transfer : Transfer9657) (identity : Identity Nat) :
    oppositeNormal identity.lhs = oppositeNormal identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid_of_basis _ (representative_basis9657_of_transfer transfer) identity

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly
