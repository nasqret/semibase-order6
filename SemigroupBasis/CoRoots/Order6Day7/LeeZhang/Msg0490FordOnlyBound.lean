import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlyCompleteness
import SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactTransfers

/-! Close the two finite-only FORDONLY interfaces using S3's actual,
independently recorded embeddings. The basis, core normalization proof,
literal tables, and finite proofs are unchanged. All endpoints here are
unconditional; the normal functions reuse the computable core algorithms. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Order6Sunday

theorem representative_basis5563 :
    BasisFor FordOnlyExactFinite.S6_5563.table.semigroup basis :=
  representative_basis5563_of_transfer FordOnlyExactTransfers.powerEmbedding5563

theorem opposite_basis5563 :
    BasisFor FordOnlyExactFinite.S6_5563.table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis5563_of_transfer FordOnlyExactTransfers.powerEmbedding5563

theorem representative_basis9657 :
    BasisFor FordOnlyExactFinite.S6_9657.table.semigroup basis :=
  representative_basis9657_of_transfer FordOnlyExactTransfers.powerEmbedding9657

theorem opposite_basis9657 :
    BasisFor FordOnlyExactFinite.S6_9657.table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis9657_of_transfer FordOnlyExactTransfers.powerEmbedding9657

theorem signature_of_valid5563 (identity : Identity Nat)
    (valid : identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_valid5563_of_transfer FordOnlyExactTransfers.powerEmbedding5563 identity valid

theorem signature_of_valid9657 (identity : Identity Nat)
    (valid : identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_valid9657_of_transfer FordOnlyExactTransfers.powerEmbedding9657 identity valid

abbrev normal5563 : Word Nat → Word Nat := normal
abbrev oppositeNormal5563 : Word Nat → Word Nat := oppositeNormal
abbrev normal9657 : Word Nat → Word Nat := normal
abbrev oppositeNormal9657 : Word Nat → Word Nat := oppositeNormal

theorem normal_eq_iff_valid5563 (identity : Identity Nat) :
    normal5563 identity.lhs = normal5563 identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup :=
  normal_eq_iff_valid5563_of_transfer FordOnlyExactTransfers.powerEmbedding5563 identity

theorem oppositeNormal_eq_iff_valid5563 (identity : Identity Nat) :
    oppositeNormal5563 identity.lhs = oppositeNormal5563 identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_5563.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid5563_of_transfer FordOnlyExactTransfers.powerEmbedding5563 identity

theorem normal_eq_iff_valid9657 (identity : Identity Nat) :
    normal9657 identity.lhs = normal9657 identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup :=
  normal_eq_iff_valid9657_of_transfer FordOnlyExactTransfers.powerEmbedding9657 identity

theorem oppositeNormal_eq_iff_valid9657 (identity : Identity Nat) :
    oppositeNormal9657 identity.lhs = oppositeNormal9657 identity.rhs ↔
      identity.SatisfiedBy FordOnlyExactFinite.S6_9657.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid9657_of_transfer FordOnlyExactTransfers.powerEmbedding9657 identity

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly
