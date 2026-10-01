import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitialBasis
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_804Semantics

/-!
# The exact cut/initial signature for the d024 B10 root

The direct `S5_804` factor records the ordered connected components, unary
repeat flags, and each component's literal final variable.  The direct
`S3_16` factor records the complete global first-occurrence sequence.  This
module packages those coordinates and defines the deterministic final-aware
renderer used by the B10 normalizer.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

open SemigroupBasis
open SemigroupBasis.Examples

/-- Equality of the exact `S5_804` connected-cut data together with equality
of the complete global first-occurrence sequence. -/
structure SameCutInitialSignature
    (left right : Word Nat) : Prop where
  cuts :
    S5_804.SameConnectedCutSignature left right
  initials :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList

namespace SameCutInitialSignature

theorem refl (word : Word Nat) :
    SameCutInitialSignature word word :=
  ⟨S5_804.SameConnectedCutSignature.refl word, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameCutInitialSignature left right) :
    SameCutInitialSignature right left :=
  ⟨same.cuts.symm, same.initials.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameCutInitialSignature left middle)
    (second : SameCutInitialSignature middle right) :
    SameCutInitialSignature left right :=
  ⟨first.cuts.trans second.cuts,
    first.initials.trans second.initials⟩

end SameCutInitialSignature

/-- Identities valid in both selected direct factors preserve the complete
cut/initial signature. -/
theorem sameCutInitialSignature_of_factor_valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup) :
    SameCutInitialSignature identity.lhs identity.rhs := by
  have canonicalLeftValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup := by
    simpa only
      [SemigroupBasis.Generated.S3_16.table_eq_catalogue_model] using
        leftValid
  exact
    ⟨S5_804.valid_sameConnectedCutSignature identity rightValid,
      S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity canonicalLeftValid⟩

/-- Every derivation from literal B10 preserves both semantic coordinates. -/
theorem derives_sameCutInitialSignature
    {left right : Word Nat}
    (derivation : Derives B10 left right) :
    SameCutInitialSignature left right := by
  let identity : Identity Nat := Identity.mk left right
  exact sameCutInitialSignature_of_factor_valid identity
    (fun valuation => derivation.sound s3_16_models valuation)
    (fun valuation => derivation.sound s5_804_models valuation)

/-! ## Deterministic final-aware initial-order renderer -/

/-- Render one exact connected-cut component in the order induced by the
global first-occurrence sequence.  The empty branches totalize data that
cannot arise from a nonempty component with its genuine global initials.
For a multi-letter component, the first local initial closes the envelope;
the recorded final is appended exactly when it differs from that head. -/
def renderCutInitialComponent
    (globalInitials : List Nat)
    (signature : S5_804.ConnectedCutComponentSignature) : List Nat :=
  let order :=
    globalInitials.filter fun letter =>
      decide (letter ∈ signature.base.support)
  match signature.base.support with
  | [] => []
  | [_] =>
      match order with
      | [] => []
      | head :: _ =>
          if signature.base.repeatedUnary then [head, head] else [head]
  | _ :: _ :: _ =>
      match order with
      | [] => []
      | head :: _ =>
          if signature.final = head then
            order ++ [head]
          else
            order ++ [head, signature.final]

/-- The deterministic list normal form attached to the full joint
signature.  Component order and literal finals come from `S5_804`; the
within-component order comes from the global `S3_16` coordinate. -/
def cutInitialNormalList (word : Word Nat) : List Nat :=
  let initials := firstOccurrenceSequence word.toList
  (S5_804.connectedCutSignaturesWord word).flatMap
    (renderCutInitialComponent initials)

/-- Equal joint signatures produce literally equal deterministic renders. -/
theorem cutInitialNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameCutInitialSignature left right) :
    cutInitialNormalList left = cutInitialNormalList right := by
  unfold cutInitialNormalList
  rw [same.cuts, same.initials]

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial
