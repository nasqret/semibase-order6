import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_793Invariant
import SemigroupBasis.CoRoots.S5_794Derivations
import SemigroupBasis.Generated.S4_71

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis
open SemigroupBasis.Examples

/-- The literal `S4_71` submonoid `{0,a,b,1}` of Edmunds' `M14`. -/
def s4_71Embedding :
    Embedding Generated.S4_71.table.semigroup
      publishedM14Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The literal left-regular-band submonoid `{b,1,c}` of `M14`. -/
def lrbEmbedding :
    Embedding leftRegularBandThree.semigroup
      publishedM14Table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨2, by decide⟩ else
      if value.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_s4_71
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM14Table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  s4_71Embedding.pullback_identity identity valid

theorem valid_lrb
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM14Table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  lrbEmbedding.pullback_identity identity valid

/-- Every `M14` identity preserves the complete sequence of first
occurrences. -/
theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM14Table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity (valid_lrb identity valid)

private theorem head_eq_of_firstOccurrenceSequence_eq
    {left right : Word Nat}
    (equal :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  have heads := congrArg List.head? equal
  simpa [Word.toList, firstOccurrenceSequence] using heads

/-- The `S4_71` component supplies capped multiplicities, the ordered
linear variables, and every last-occurrence gap. -/
theorem valid_blockSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM14Table.semigroup) :
    S5_793Invariant.SameFirstSimpleLastGapSignature
      identity.lhs identity.rhs := by
  have firstSequence := valid_firstOccurrenceSequence_eq identity valid
  exact S5_793Invariant.sameSignature_of_s4_71_valid_head_eq
    identity (valid_s4_71 identity valid)
    (head_eq_of_firstOccurrenceSequence_eq firstSequence)

/-- Kernel-facing package of the two independent invariants used in
Edmunds' block-permutation proof. The original `M14` validity certificate
is retained so recursive block rearrangements can compose semantically. -/
structure SameSignature (left right : Word Nat) : Prop where
  m14Theory :
    (Identity.mk left right).SatisfiedBy publishedM14Table.semigroup
  block :
    S5_793Invariant.SameFirstSimpleLastGapSignature left right
  firstSequence :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList

theorem sameSignature_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedM14Table.semigroup) :
    SameSignature identity.lhs identity.rhs :=
  ⟨valid, valid_blockSignature identity valid,
    valid_firstOccurrenceSequence_eq identity valid⟩

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  sameSignature_of_valid ⟨word, word⟩ (fun _ => rfl)

theorem symm {left right : Word Nat}
    (same : SameSignature left right) :
    SameSignature right left :=
  sameSignature_of_valid ⟨right, left⟩
    (fun valuation => (same.m14Theory valuation).symm)

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle)
    (second : SameSignature middle right) :
    SameSignature left right :=
  sameSignature_of_valid ⟨left, right⟩
    (fun valuation =>
      (first.m14Theory valuation).trans
        (second.m14Theory valuation))

end SameSignature

/-- Every derivation from the twelve laws preserves the exact `M14`
signature, including the full first-occurrence sequence. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSignature left right :=
  sameSignature_of_valid ⟨left, right⟩
    (fun valuation =>
      derivation.sound publishedM14Models valuation)

end SemigroupBasis.CoRoots.S5_794
