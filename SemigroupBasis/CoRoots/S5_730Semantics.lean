import SemigroupBasis.CoRoots.S5_730Invariant
import SemigroupBasis.Examples.NormalBandFour
import SemigroupBasis.Transfer

/-!
Source-only semantic separation for the exact `S5_730` catalogue table.

The two embeddings recover the four necessary signature coordinates. No
derivational completeness claim is made here.
-/

namespace SemigroupBasis.CoRoots.S5_730

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact zero-based normal-band embedding `[0, 2, 3, 4]`. -/
def normalBandEmbedding :
    Embedding normalBandFour.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The exact zero-based final-marker embedding `[0, 1, 2]`. -/
def finalMarkerEmbedding :
    Embedding finalMarkerThree.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- Every identity valid in the exact `S5_730` table preserves the certified
head/support/final/simple-final signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    S5_730Invariant.SameSignature identity.lhs identity.rhs := by
  have normalBandValid :
      identity.SatisfiedBy normalBandFour.semigroup :=
    normalBandEmbedding.pullback_identity identity valid
  have finalMarkerValid :
      identity.SatisfiedBy finalMarkerThree.semigroup :=
    finalMarkerEmbedding.pullback_identity identity valid
  exact
    ⟨normalBandValid_head_eq identity normalBandValid,
      normalBandValid_support_eq identity normalBandValid,
      normalBandValid_final_eq identity normalBandValid,
      S5_196.finalMarkerValid_simpleFinal identity finalMarkerValid⟩

end SemigroupBasis.CoRoots.S5_730
