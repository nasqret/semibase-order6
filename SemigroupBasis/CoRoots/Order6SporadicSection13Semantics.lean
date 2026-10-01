import SemigroupBasis.CoRoots.Order6SporadicSection13
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

namespace S6_10203

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_10203
namespace S6_10409

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_10409
namespace S6_10218

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_10218
namespace S6_10410

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (4 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_10410
namespace S6_10411

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_10411
namespace S6_9882

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (2 : Fin 6)
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
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (0 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_9882
namespace S6_8921

def jEmbedding :
    Embedding Generated.S3_6.table.semigroup publishedSemigroup where
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

theorem valid_j
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
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

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_8921
namespace S6_9062

/-- The published subsemigroup `{2,3,4,5}` used by the G5 divisor. -/
def jDivisorMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (2 : Fin 4) else (2 : Fin 4) else if a = 1 then if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4) else if a = 2 then if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4) else if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)

def jDivisorTable : FiniteTable where
  order := 4
  mul := jDivisorMul
  assoc := by decide

def jDivisorEmbedding :
    Embedding jDivisorTable.semigroup publishedSemigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (1 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- Collapse the ideal `{2,4}` and identify the three quotient classes with J. -/
def jDivisorQuotient :
    SplitSurjection jDivisorTable.semigroup
      Generated.S3_6.table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else (1 : Fin 3)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b : Fin 3 => if b = 0 then (0 : Fin 4) else if b = 1 then (3 : Fin 4) else (1 : Fin 4)
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem valid_j
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_6.table.semigroup :=
  jDivisorQuotient.pushforwardIdentity identity <|
    jDivisorEmbedding.pullback_identity identity valid

def oEmbedding :
    Embedding Generated.S4_96.table.semigroup.opposite publishedSemigroup where
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

theorem valid_o
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite :=
  oEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor publishedSemigroup basis :=
  basisFor_of_joinCompleteness publishedSemigroup publishedModels
    valid_j valid_o completion

theorem representativeOppositeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup.opposite basis :=
  publishedBasisFor_of_joinCompleteness completion

theorem representativeBasisFor_of_joinCompleteness
    (completion : JoinCompleteness) :
    BasisFor table.semigroup oppositeBasis := by
  simpa [publishedSemigroup, oppositeBasis] using
    (publishedBasisFor_of_joinCompleteness completion).oppositeReversed

end S6_9062

end SemigroupBasis.CoRoots.Order6SporadicSection13
