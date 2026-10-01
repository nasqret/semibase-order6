import SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unrestricted rank127 intersection completeness

All nonfinal connected components may use the complete lower multiplicity
calculus because a genuine nonempty right context remains. The final
component uses the already proved rank109 fixed-final comparison. This
separates the two roles of the guard and avoids unguarded cancellation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

theorem flattenNonempty {components : List (List Nat)}
    (nonempty : components ≠ []) (allNonempty : ∀ component ∈ components, component ≠ []) :
    components.flatten ≠ [] := by
  cases components with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      have headNonempty := allNonempty head (by simp)
      rw [List.flatten_cons]
      intro empty
      cases head with
      | nil => exact headNonempty rfl
      | cons letter remaining => simp at empty

private theorem getLastD_append_nonempty (left : List Nat) (leftHead rightHead : Nat)
    (rightTail : List Nat) :
    (left ++ rightHead :: rightTail).getLastD leftHead = rightTail.getLastD rightHead := by
  induction left generalizing leftHead with
  | nil => simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction letter

theorem componentFinal_append (left right : List Nat) (rightNonempty : right ≠ []) :
    S5_804.componentFinal (left ++ right) = S5_804.componentFinal right := by
  obtain ⟨rightHead, rightTail, rfl⟩ := List.exists_cons_of_ne_nil rightNonempty
  cases left with
  | nil => rfl
  | cons leftHead leftTail =>
      simp only [List.cons_append, S5_804.componentFinal]
      exact getLastD_append_nonempty leftTail leftHead rightHead rightTail

/-- Concatenate guarded earlier-component derivations and one unguarded
final-component derivation. All callbacks retain the original whole-word
invariants; the recursion does not silently promote a guarded equality. -/
theorem deriveAlignedFinalComponents (leftComponents rightComponents : List (List Nat))
    (signatures : leftComponents.map connectedComponentSignatureOfList =
      rightComponents.map connectedComponentSignatureOfList)
    (leftNonempty : ∀ component ∈ leftComponents, component ≠ [])
    (rightNonempty : ∀ component ∈ rightComponents, component ≠ [])
    (sameFinal : S5_804.componentFinal leftComponents.flatten =
      S5_804.componentFinal rightComponents.flatten)
    (deriveEarlier : ∀ left, left ∈ leftComponents → ∀ right, right ∈ rightComponents →
      connectedComponentSignatureOfList left = connectedComponentSignatureOfList right →
      ∀ guard : List Nat, guard ≠ [] → ListDerives (left ++ guard) (right ++ guard))
    (deriveLast : ∀ left, left ∈ leftComponents → ∀ right, right ∈ rightComponents →
      connectedComponentSignatureOfList left = connectedComponentSignatureOfList right →
      S5_804.componentFinal left = S5_804.componentFinal right → ListDerives left right) :
    ListDerives leftComponents.flatten rightComponents.flatten := by
  induction leftComponents generalizing rightComponents with
  | nil =>
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons head tail => simp at signatures
  | cons leftHead leftTail induction =>
      cases rightComponents with
      | nil => simp at signatures
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  have finalAgreement : S5_804.componentFinal leftHead = S5_804.componentFinal rightHead := by
                    simpa using sameFinal
                  simpa using deriveLast leftHead (by simp) rightHead (by simp) signatures.1 finalAgreement
              | cons next rest => simp at signatures
          | cons next rest =>
              cases rightTail with
              | nil => simp at signatures
              | cons rightNext rightRest =>
                  have leftTailNonempty : ∀ component ∈ next :: rest, component ≠ [] := by
                    intro component member
                    exact leftNonempty component (List.mem_cons_of_mem leftHead member)
                  have rightTailNonempty : ∀ component ∈ rightNext :: rightRest, component ≠ [] := by
                    intro component member
                    exact rightNonempty component (List.mem_cons_of_mem rightHead member)
                  have leftFlatNonempty := flattenNonempty (by simp : next :: rest ≠ []) leftTailNonempty
                  have rightFlatNonempty := flattenNonempty (by simp : rightNext :: rightRest ≠ []) rightTailNonempty
                  have tailFinal : S5_804.componentFinal (next :: rest).flatten =
                      S5_804.componentFinal (rightNext :: rightRest).flatten := by
                    have agreement := sameFinal
                    change S5_804.componentFinal (leftHead ++ (next :: rest).flatten) =
                      S5_804.componentFinal (rightHead ++ (rightNext :: rightRest).flatten) at agreement
                    rw [componentFinal_append leftHead _ leftFlatNonempty,
                      componentFinal_append rightHead _ rightFlatNonempty] at agreement
                    exact agreement
                  have first := deriveEarlier leftHead (by simp) rightHead (by simp)
                    signatures.1 (next :: rest).flatten leftFlatNonempty
                  have remaining := induction (rightNext :: rightRest) signatures.2
                    leftTailNonempty rightTailNonempty tailFinal
                    (by
                      intro left leftMember right rightMember signature guard guardNonempty
                      exact deriveEarlier left (List.mem_cons_of_mem leftHead leftMember)
                        right (List.mem_cons_of_mem rightHead rightMember) signature guard guardNonempty)
                    (by
                      intro left leftMember right rightMember signature finalAgreement
                      exact deriveLast left (List.mem_cons_of_mem leftHead leftMember)
                        right (List.mem_cons_of_mem rightHead rightMember) signature finalAgreement)
                  simpa only [List.flatten_cons] using first.trans (remaining.prepend rightHead)

theorem derives_of_signatures {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signatures : leftComponents.map connectedComponentSignatureOfList =
      rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents, connectedComponentSignaturesWord,
      connectedComponentSignaturesList, connectedComponentDecomposeWord] using
      S5_379.sameComponentSignatures_of_sameComponentSimpleSignature same.componentSimple
  have leftFlatten : leftComponents.flatten = left.toList := connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList := connectedComponentDecomposeWord_flatten right
  have wholeCounts : ∀ tested, min (leftComponents.flatten.count tested) 2 =
      min (rightComponents.flatten.count tested) 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact S5_379.cappedCounts_eq_of_sameComponentSimpleSignature same.componentSimple tested
  have wholeFinal : S5_804.componentFinal leftComponents.flatten =
      S5_804.componentFinal rightComponents.flatten := by
    rw [leftFlatten, rightFlatten]
    exact same.final
  have leftPairwise := connectedComponentDecomposeWord_pairwiseDisjoint left
  have rightPairwise := connectedComponentDecomposeWord_pairwiseDisjoint right
  have componentCounts : ∀ leftComponent, leftComponent ∈ leftComponents →
      ∀ rightComponent, rightComponent ∈ rightComponents →
      connectedComponentSignatureOfList leftComponent = connectedComponentSignatureOfList rightComponent →
      ∀ tested, min (leftComponent.count tested) 2 = min (rightComponent.count tested) 2 := by
    intro leftComponent leftMember rightComponent rightMember signature
    exact S3_16.Rank105.Seed.componentCappedCounts leftPairwise rightPairwise
      leftMember rightMember signature wholeCounts
  have joined := deriveAlignedFinalComponents leftComponents rightComponents signatures
    (connectedComponentDecomposeWord_nonempty_components left)
    (connectedComponentDecomposeWord_nonempty_components right) wholeFinal
    (by
      intro leftComponent leftMember rightComponent rightMember signature guard guardNonempty
      have lower := S5_379.listDerivesConnectedComponents_of_cappedCounts
        (connectedComponentDecomposeWord_nonempty_components left leftComponent leftMember)
        (connectedComponentDecomposeWord_nonempty_components right rightComponent rightMember)
        (connectedComponentDecomposeWord_supportConnected left leftComponent leftMember)
        (connectedComponentDecomposeWord_supportConnected right rightComponent rightMember)
        (componentCounts leftComponent leftMember rightComponent rightMember signature)
      exact lowerListUnderRight lower guard guardNonempty)
    (by
      intro leftComponent leftMember rightComponent rightMember signature finalAgreement
      exact transport109List (Rank109.FinalEnvelope.listDerivesConnectedFinal
        (connectedComponentDecomposeWord_nonempty_components left leftComponent leftMember)
        (connectedComponentDecomposeWord_nonempty_components right rightComponent rightMember)
        (connectedComponentDecomposeWord_supportConnected left leftComponent leftMember)
        (connectedComponentDecomposeWord_supportConnected right rightComponent rightMember)
        finalAgreement (componentCounts leftComponent leftMember rightComponent rightMember signature)))
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

/-- S6_8254 requires the opposite S5_379 table. Reuse the already proved
unrestricted theory implication through the approved shared transport API. -/
noncomputable def rightOppositeNormalizer :
    IntersectionNormalizer leftTable.semigroup rightOppositeTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer normalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid)
    S3_16.Rank105.FiniteFanout.rightTheoryFromOpposite

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank127.Seed
