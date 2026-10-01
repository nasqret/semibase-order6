import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecks
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

namespace S6_2771

def countEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countEmbedding.pullback_identity identity valid
def finalEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalEmbedding.pullback_identity identity valid
def initialEmbedding :
    Embedding Generated.S3_6.table.semigroup.opposite publishedSemigroup where
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

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (3 : Fin 6)
  else (2 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (0 : Fin 6) (1 : Fin 6)
      (2 : Fin 6) (3 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_2771
namespace S6_2772

def countEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countEmbedding.pullback_identity identity valid
def finalEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalEmbedding.pullback_identity identity valid
def initialDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def initialDivisorTable : FiniteTable where
  order := 6
  mul := initialDivisorMul
  assoc := by decide

def initialDivisorEmbedding :
    Embedding initialDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def initialDivisorQuotient :
    SplitSurjection initialDivisorTable.semigroup Generated.S3_6.table.semigroup.opposite where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialDivisorQuotient.pushforwardIdentity identity <|
    initialDivisorEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (3 : Fin 6)
  else (2 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (0 : Fin 6) (1 : Fin 6)
      (2 : Fin 6) (3 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_2772
namespace S6_2773

def countEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countEmbedding.pullback_identity identity valid
def finalDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def finalDivisorTable : FiniteTable where
  order := 6
  mul := finalDivisorMul
  assoc := by decide

def finalDivisorEmbedding :
    Embedding finalDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup Generated.S3_6.table.semigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity <|
    finalDivisorEmbedding.pullback_identity identity valid
def initialDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def initialDivisorTable : FiniteTable where
  order := 6
  mul := initialDivisorMul
  assoc := by decide

def initialDivisorEmbedding :
    Embedding initialDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def initialDivisorQuotient :
    SplitSurjection initialDivisorTable.semigroup Generated.S3_6.table.semigroup.opposite where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialDivisorQuotient.pushforwardIdentity identity <|
    initialDivisorEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (3 : Fin 6)
  else (2 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (0 : Fin 6) (1 : Fin 6)
      (2 : Fin 6) (3 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_2773
namespace S6_5240

def countEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedSemigroup where
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

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countEmbedding.pullback_identity identity valid
def finalDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def finalDivisorTable : FiniteTable where
  order := 6
  mul := finalDivisorMul
  assoc := by decide

def finalDivisorEmbedding :
    Embedding finalDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup Generated.S3_6.table.semigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity <|
    finalDivisorEmbedding.pullback_identity identity valid
def initialDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def initialDivisorTable : FiniteTable where
  order := 6
  mul := initialDivisorMul
  assoc := by decide

def initialDivisorEmbedding :
    Embedding initialDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def initialDivisorQuotient :
    SplitSurjection initialDivisorTable.semigroup Generated.S3_6.table.semigroup.opposite where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialDivisorQuotient.pushforwardIdentity identity <|
    initialDivisorEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (4 : Fin 6)
  else (2 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (0 : Fin 6) (1 : Fin 6)
      (2 : Fin 6) (4 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_5240
namespace S6_5241

def countEmbedding :
    Embedding Generated.S4_40.table.semigroup publishedSemigroup where
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

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countEmbedding.pullback_identity identity valid
def finalDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def finalDivisorTable : FiniteTable where
  order := 6
  mul := finalDivisorMul
  assoc := by decide

def finalDivisorEmbedding :
    Embedding finalDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup Generated.S3_6.table.semigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (4 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity <|
    finalDivisorEmbedding.pullback_identity identity valid
def initialDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def initialDivisorTable : FiniteTable where
  order := 6
  mul := initialDivisorMul
  assoc := by decide

def initialDivisorEmbedding :
    Embedding initialDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def initialDivisorQuotient :
    SplitSurjection initialDivisorTable.semigroup Generated.S3_6.table.semigroup.opposite where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialDivisorQuotient.pushforwardIdentity identity <|
    initialDivisorEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (4 : Fin 6)
  else (2 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (0 : Fin 6) (1 : Fin 6)
      (2 : Fin 6) (4 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_5241
namespace S6_9313

def countDivisorMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (1 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (1 : Fin 5) else (3 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (1 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)

def countDivisorTable : FiniteTable where
  order := 5
  mul := countDivisorMul
  assoc := by decide

def countDivisorEmbedding :
    Embedding countDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 5 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published congruence quotient identifying this divisor. -/
def countDivisorQuotient :
    SplitSurjection countDivisorTable.semigroup Generated.S4_40.table.semigroup where
  toFun := fun a : Fin 5 => if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 4 => if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_40.table.semigroup :=
  countDivisorQuotient.pushforwardIdentity identity <|
    countDivisorEmbedding.pullback_identity identity valid
def finalDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def finalDivisorTable : FiniteTable where
  order := 6
  mul := finalDivisorMul
  assoc := by decide

def finalDivisorEmbedding :
    Embedding finalDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup Generated.S3_6.table.semigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (2 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_final
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity <|
    finalDivisorEmbedding.pullback_identity identity valid
def initialDivisorMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def initialDivisorTable : FiniteTable where
  order := 6
  mul := initialDivisorMul
  assoc := by decide

def initialDivisorEmbedding :
    Embedding initialDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The published Rees quotient identifying this divisor. -/
def initialDivisorQuotient :
    SplitSurjection initialDivisorTable.semigroup Generated.S3_6.table.semigroup.opposite where
  toFun := fun a : Fin 6 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (0 : Fin 3) else (2 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 6) else if b = 1 then (3 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_initial
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup.opposite :=
  initialDivisorQuotient.pushforwardIdentity identity <|
    initialDivisorEmbedding.pullback_identity identity valid

def fssValuation (a : Nat) : Fin 6 :=
  if a = 0 then (5 : Fin 6)
  else if a = 1 then (2 : Fin 6)
  else (3 : Fin 6)

theorem directedSimpleAdjacencyLaws :
    DirectedSimpleAdjacencyLaws publishedSemigroup
      (1 : Fin 6) (0 : Fin 6)
      (3 : Fin 6) (2 : Fin 6)
      (5 : Fin 6) := by
  constructor <;> decide

theorem fssExclusionValues :
    publishedSemigroup.eval fssValuation fssExclusionIdentity.lhs ≠
      publishedSemigroup.eval fssValuation fssExclusionIdentity.rhs := by
  decide

theorem not_fssExclusionIdentity :
    ¬ fssExclusionIdentity.SatisfiedBy publishedSemigroup := by
  intro valid
  exact fssExclusionValues (valid fssValuation)

theorem publishedBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_completeness publishedSemigroup publishedModels
    valid_count valid_final valid_initial completion

theorem representativeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : Completeness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_9313

end SemigroupBasis.CoRoots.Order6SporadicSection15
