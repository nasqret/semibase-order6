import SemigroupBasis.CoRoots.Order6SporadicSection12
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Generated.S3_4
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S4_40
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Generated.S4_70
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

def IdempotentSeparable (candidate : FiniteTable) : Prop :=
  ∀ x y : Fin candidate.order, x ≠ y →
    (∃ leftIdempotent : Fin candidate.order,
      candidate.mul leftIdempotent leftIdempotent = leftIdempotent ∧
      candidate.mul leftIdempotent x ≠ candidate.mul leftIdempotent y) ∧
    (∃ rightIdempotent : Fin candidate.order,
      candidate.mul rightIdempotent rightIdempotent = rightIdempotent ∧
      candidate.mul x rightIdempotent ≠ candidate.mul y rightIdempotent)

namespace S6_5597

def l_2_1Embedding :
    Embedding Generated.S3_16.table.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_l_2_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  l_2_1Embedding.pullback_identity identity valid

def n_2_1Embedding :
    Embedding Generated.S3_8.table.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_n_2_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_8.table.semigroup :=
  n_2_1Embedding.pullback_identity identity valid

def n_3Embedding :
    Embedding Generated.S3_4.table.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (3 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_n_3
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_4.table.semigroup :=
  n_3Embedding.pullback_identity identity valid

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_j
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid


end S6_5597

namespace S6_5625

def n_3_1Embedding :
    Embedding Generated.S4_40.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_n_3_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  n_3_1Embedding.pullback_identity identity valid

def b0Embedding :
    Embedding Generated.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_b0
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S4_69.table.semigroup :=
  b0Embedding.pullback_identity identity valid


theorem idempotentSeparable : IdempotentSeparable table := by
  intro x y different
  revert x y
  decide

private def a0Countervaluation (letter : Nat) : Fin 4 :=
  if letter = 0 then 2 else if letter = 1 then 3 else 0

theorem a0CounterexampleLeft :
    Generated.S4_70.table.semigroup.eval a0Countervaluation
      word_12_4_empty_left = (1 : Fin 4) := by
  decide

theorem a0CounterexampleRight :
    Generated.S4_70.table.semigroup.eval a0Countervaluation
      word_12_4_empty_right = (0 : Fin 4) := by
  decide

theorem a0FailsExtraLaw :
    ¬law_12_4_empty.SatisfiedBy Generated.S4_70.table.semigroup := by
  intro valid
  have equality := valid a0Countervaluation
  change
    Generated.S4_70.table.semigroup.eval a0Countervaluation
        word_12_4_empty_left =
      Generated.S4_70.table.semigroup.eval a0Countervaluation
        word_12_4_empty_right at equality
  rw [a0CounterexampleLeft, a0CounterexampleRight] at equality
  have distinct : (1 : Fin 4) ≠ 0 := by decide
  exact distinct equality

end S6_5625

namespace S6_5626

def n_3_1Embedding :
    Embedding Generated.S4_40.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_n_3_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  n_3_1Embedding.pullback_identity identity valid

def a0Embedding :
    Embedding Generated.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_a0
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S4_70.table.semigroup :=
  a0Embedding.pullback_identity identity valid


theorem idempotentSeparable : IdempotentSeparable table := by
  intro x y different
  revert x y
  decide

end S6_5626


end SemigroupBasis.CoRoots.Order6SporadicSection12
