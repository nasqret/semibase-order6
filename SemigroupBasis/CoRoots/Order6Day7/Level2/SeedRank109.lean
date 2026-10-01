import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109FinalEnvelope
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Unrestricted rank109 intersection completeness

The actual S5_804 factor aligns the complete component-final signatures.
The actual S3_8 factor supplies cap-two counts. Disjoint support projects
those counts into each component, whose unrestricted comparison is already
proved. The resulting component derivations concatenate without a bound.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open FinalEnvelope

theorem deriveAlignedComponents (leftComponents rightComponents : List (List Nat))
    (signatures : leftComponents.map S5_804.connectedCutComponentSignatureOfList =
      rightComponents.map S5_804.connectedCutComponentSignatureOfList)
    (derive : ∀ left, left ∈ leftComponents → ∀ right, right ∈ rightComponents →
      S5_804.connectedCutComponentSignatureOfList left = S5_804.connectedCutComponentSignatureOfList right →
      ListDerives left right) :
    ListDerives leftComponents.flatten rightComponents.flatten := by
  induction leftComponents generalizing rightComponents with
  | nil =>
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons head tail => simp at signatures
  | cons head tail induction =>
      cases rightComponents with
      | nil => simp at signatures
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          have headDerivation := derive head (by simp) rightHead (by simp) signatures.1
          have tailDerivation := induction rightTail signatures.2 (by
            intro left leftMember right rightMember same
            exact derive left (List.mem_cons_of_mem head leftMember)
              right (List.mem_cons_of_mem rightHead rightMember) same)
          simpa only [List.flatten_cons] using
            (headDerivation.append tail.flatten).trans (tailDerivation.prepend rightHead)

theorem derives_of_signatures {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signatures : leftComponents.map S5_804.connectedCutComponentSignatureOfList =
      rightComponents.map S5_804.connectedCutComponentSignatureOfList := by
    simpa [leftComponents, rightComponents, S5_804.SameConnectedCutSignature,
      S5_804.connectedCutSignaturesWord, S5_804.connectedCutSignaturesList,
      connectedComponentDecomposeWord] using same.componentFinal
  have leftFlatten : leftComponents.flatten = left.toList := connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList := connectedComponentDecomposeWord_flatten right
  have wholeCounts : ∀ tested, min (leftComponents.flatten.count tested) 2 =
      min (rightComponents.flatten.count tested) 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact same.counts tested
  have leftPairwise := connectedComponentDecomposeWord_pairwiseDisjoint left
  have rightPairwise := connectedComponentDecomposeWord_pairwiseDisjoint right
  have joined := deriveAlignedComponents leftComponents rightComponents signatures (by
    intro leftComponent leftMember rightComponent rightMember signature
    have baseEqual : connectedComponentSignatureOfList leftComponent =
        connectedComponentSignatureOfList rightComponent :=
      congrArg S5_804.ConnectedCutComponentSignature.base signature
    have finalEqual : S5_804.componentFinal leftComponent = S5_804.componentFinal rightComponent :=
      congrArg S5_804.ConnectedCutComponentSignature.final signature
    exact listDerivesConnectedFinal
      (connectedComponentDecomposeWord_nonempty_components left leftComponent leftMember)
      (connectedComponentDecomposeWord_nonempty_components right rightComponent rightMember)
      (connectedComponentDecomposeWord_supportConnected left leftComponent leftMember)
      (connectedComponentDecomposeWord_supportConnected right rightComponent rightMember)
      finalEqual
      (S3_16.Rank105.Seed.componentCappedCounts leftPairwise rightPairwise
        leftMember rightMember baseEqual wholeCounts))
  have listDerivation : ListDerives left.toList right.toList := by
    rw [leftFlatten, rightFlatten] at joined
    exact joined
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord listDerivation

theorem derives_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_signatures (sameSignature_of_factorValid identity leftValid rightValid)

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

noncomputable def normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersectionBasis

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109.Seed
