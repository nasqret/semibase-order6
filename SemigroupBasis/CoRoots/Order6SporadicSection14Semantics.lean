import SemigroupBasis.CoRoots.Order6SporadicSection14
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

namespace S6_12198

def lEmbedding :
    Embedding Generated.S3_16.table.semigroup publishedSemigroup where
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

theorem valid_l
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  lEmbedding.pullback_identity identity valid
def rEmbedding :
    Embedding Generated.S2_4.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 2 => if a = 0 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_r
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S2_4.table.semigroup.opposite :=
  rEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor publishedSemigroup betaBasis :=
  betaBasisFor_of_completeness publishedSemigroup publishedModels
    completion

theorem representativeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup betaBasis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBetaBasis := by
  simpa [oppositeBetaBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_12198
namespace S6_12399

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
def lEmbedding :
    Embedding Generated.S3_16.table.semigroup publishedSemigroup where
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

theorem valid_l
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  lEmbedding.pullback_identity identity valid
def rEmbedding :
    Embedding Generated.S2_4.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 2 => if a = 0 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_r
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S2_4.table.semigroup.opposite :=
  rEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_completeness
    (completion : AlphaCompleteness publishedSemigroup) :
    BasisFor publishedSemigroup alphaBasis :=
  alphaBasisFor_of_completeness publishedSemigroup publishedModels
    completion

theorem representativeBasisFor_of_completeness
    (completion : AlphaCompleteness publishedSemigroup) :
    BasisFor table.semigroup alphaBasis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : AlphaCompleteness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeAlphaBasis := by
  simpa [oppositeAlphaBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_12399
namespace S6_12526

def lEmbedding :
    Embedding Generated.S3_16.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_l
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  lEmbedding.pullback_identity identity valid
def rEmbedding :
    Embedding Generated.S2_4.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 2 => if a = 0 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_r
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S2_4.table.semigroup.opposite :=
  rEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor publishedSemigroup betaBasis :=
  betaBasisFor_of_completeness publishedSemigroup publishedModels
    completion

theorem representativeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup betaBasis :=
  publishedBasisFor_of_completeness completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup.opposite oppositeBetaBasis := by
  simpa [oppositeBetaBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_12526
namespace S6_14467

def lEmbedding :
    Embedding Generated.S3_16.table.semigroup publishedSemigroup where
  toFun := fun a : Fin 3 => if a = 0 then (3 : Fin 6) else if a = 1 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_l
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  lEmbedding.pullback_identity identity valid
def rEmbedding :
    Embedding Generated.S2_4.table.semigroup.opposite publishedSemigroup where
  toFun := fun a : Fin 2 => if a = 0 then (0 : Fin 6) else (2 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_r
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedSemigroup) :
    identity.SatisfiedBy Generated.S2_4.table.semigroup.opposite :=
  rEmbedding.pullback_identity identity valid

theorem publishedBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor publishedSemigroup betaBasis :=
  betaBasisFor_of_completeness publishedSemigroup publishedModels
    completion

theorem representativeOppositeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup.opposite betaBasis :=
  publishedBasisFor_of_completeness completion

theorem representativeBasisFor_of_completeness
    (completion : BetaCompleteness publishedSemigroup) :
    BasisFor table.semigroup oppositeBetaBasis := by
  simpa [publishedSemigroup, oppositeBetaBasis] using
    (publishedBasisFor_of_completeness completion).oppositeReversed

end S6_14467

end SemigroupBasis.CoRoots.Order6SporadicSection14
