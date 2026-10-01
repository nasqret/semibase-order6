import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointMeasureDecrease
import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.SemanticBlockSignature
import SemigroupBasis.CoRoots.S5_790Invariant

/-!
# Forward semantic transport for endpoint progress

The structural dispatcher is a literal permutation and a contextual frozen
derivation.  This module records exactly the two consequences needed by the
component induction: support is unchanged, and the selected green catalogue
table validates the displayed source/target identity.  Semantic equality is
used only in this forward direction; it is never read backwards as a
derivation or as a canonicalization theorem.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1
open SemigroupBasis.Examples

/-- Direct soundness certificate for the selected public catalogue table.
This avoids any equality bridge through the generated Edmunds table. -/
theorem routeRightModels :
    Models SemanticBlockSignature.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemanticBlockSignature.table basis toFinThree (by decide)

/-- Direct soundness certificate for the public component table. -/
theorem routeLeftModels :
    Models Generated.S4_70.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    Generated.S4_70.table basis toFinThree (by decide)

/-- List-level semantic agreement.  `blockTheory` is phrased for all possible
nonempty decompositions so the relation itself remains total on lists; the
empty case is harmless and never used for a connected component. -/
structure EndpointSemanticAgreement
    (left right : List Nat) : Prop where
  support : sortedSupport left = sortedSupport right
  componentTheory :
    ∀ leftHead leftTail rightHead rightTail,
      left = leftHead :: leftTail →
      right = rightHead :: rightTail →
      connectedComponentSignaturesWord
          (S5_107.listWordOfCons leftHead leftTail) =
        connectedComponentSignaturesWord
          (S5_107.listWordOfCons rightHead rightTail)
  blockTheory :
    ∀ leftHead leftTail rightHead rightTail,
      left = leftHead :: leftTail →
      right = rightHead :: rightTail →
      (Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
          SemanticBlockSignature.table.semigroup

namespace EndpointSemanticAgreement

theorem refl (letters : List Nat) :
    EndpointSemanticAgreement letters letters := by
  refine ⟨rfl, ?_, ?_⟩
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    rw [leftShape] at rightShape
    obtain ⟨headEqual, tailEqual⟩ := List.cons.inj rightShape
    subst rightHead
    subst rightTail
    rfl
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    rw [leftShape] at rightShape
    obtain ⟨headEqual, tailEqual⟩ := List.cons.inj rightShape
    subst rightHead
    subst rightTail
    intro valuation
    rfl

theorem symm {left right : List Nat}
    (same : EndpointSemanticAgreement left right) :
    EndpointSemanticAgreement right left := by
  refine ⟨same.support.symm, ?_, ?_⟩
  · intro rightHead rightTail leftHead leftTail rightShape leftShape
    exact (same.componentTheory leftHead leftTail rightHead rightTail
      leftShape rightShape).symm
  · intro rightHead rightTail leftHead leftTail rightShape leftShape
    intro valuation
    exact (same.blockTheory leftHead leftTail rightHead rightTail
      leftShape rightShape valuation).symm

theorem trans {left middle right : List Nat}
    (first : EndpointSemanticAgreement left middle)
    (second : EndpointSemanticAgreement middle right) :
    EndpointSemanticAgreement left right := by
  refine ⟨first.support.trans second.support, ?_, ?_⟩
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    cases middle with
    | nil =>
        have inLeft : leftHead ∈ left := by
          rw [leftShape]
          simp
        have inSupport : leftHead ∈ sortedSupport left :=
          (mem_sortedSupport_iff leftHead left).mpr inLeft
        rw [first.support] at inSupport
        have impossible :=
          (mem_sortedSupport_iff leftHead []).mp inSupport
        simp at impossible
    | cons middleHead middleTail =>
        exact
          (first.componentTheory leftHead leftTail
            middleHead middleTail leftShape rfl).trans
          (second.componentTheory middleHead middleTail
            rightHead rightTail rfl rightShape)
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    cases middle with
    | nil =>
        have inLeft : leftHead ∈ left := by
          rw [leftShape]
          simp
        have inSupport : leftHead ∈ sortedSupport left :=
          (mem_sortedSupport_iff leftHead left).mpr inLeft
        rw [first.support] at inSupport
        have impossible :=
          (mem_sortedSupport_iff leftHead []).mp inSupport
        simp at impossible
    | cons middleHead middleTail =>
        have leftValid := first.blockTheory
          leftHead leftTail middleHead middleTail leftShape rfl
        have rightValid := second.blockTheory
          middleHead middleTail rightHead rightTail rfl rightShape
        intro valuation
        exact (leftValid valuation).trans (rightValid valuation)

/-- The accelerated public signature is equal whenever the agreement is
instantiated at nonempty endpoints. -/
theorem make_eq
    {left right : List Nat}
    (same : EndpointSemanticAgreement left right)
    (leftHead rightHead : Nat) (leftTail rightTail : List Nat)
    (leftShape : left = leftHead :: leftTail)
    (rightShape : right = rightHead :: rightTail) :
    SemanticBlockSignature.make (sortedSupport left)
        (S5_107.listWordOfCons leftHead leftTail) =
      SemanticBlockSignature.make (sortedSupport right)
        (S5_107.listWordOfCons rightHead rightTail) := by
  exact SemanticBlockSignature.make_eq_of_support_eq_of_valid
    same.support
    (same.blockTheory leftHead leftTail rightHead rightTail
      leftShape rightShape)

end EndpointSemanticAgreement

/-- A contextual frozen route which is also a literal permutation preserves
both semantic factors and the literal support. -/
theorem semanticAgreement_of_reachable_permutation
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right)
    (permutation : left.Perm right) :
    EndpointSemanticAgreement left right := by
  refine ⟨?_, ?_, ?_⟩
  · apply sortedSupport_eq_of_mem_iff
    intro tested
    exact permutation.mem_iff
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    have listed := contextualFrozenRTC_listDerives reachable
    rw [leftShape, rightShape] at listed
    have derived := S5_107.ListDerives.toWord listed
    let identity : Identity Nat :=
      Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail)
    have valid : identity.SatisfiedBy
        Generated.S4_70.table.semigroup := by
      intro valuation
      exact derived.sound routeLeftModels valuation
    exact
      SemigroupBasis.CoRoots.S5_790Invariant.sameComponents_of_s4_70_valid
        identity valid
  · intro leftHead leftTail rightHead rightTail leftShape rightShape
    have listed := contextualFrozenRTC_listDerives reachable
    rw [leftShape, rightShape] at listed
    have derived := S5_107.ListDerives.toWord listed
    intro valuation
    exact derived.sound routeRightModels valuation

/-- Every exact endpoint-measure progress move transports the route-local
support and selected-table semantics forward. -/
theorem endpointDisorder_progress_semantic
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters)
    (positive : (endpointMeasure letters).Positive) :
    ∃ next,
      ContextualFrozenRTC letters next ∧
      letters.Perm next ∧
      next ≠ letters ∧
      EndpointMeasure.Lt (endpointMeasure next)
        (endpointMeasure letters) ∧
      EndpointSemanticAgreement letters next := by
  obtain ⟨next, reachable, permutation, changed, decrease⟩ :=
    endpointDisorder_progress_measure twoLimited connected positive
  exact ⟨next, reachable, permutation, changed, decrease,
    semanticAgreement_of_reachable_permutation reachable permutation⟩

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
