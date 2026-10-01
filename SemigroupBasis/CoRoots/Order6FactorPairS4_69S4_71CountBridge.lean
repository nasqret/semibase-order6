import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71Completeness
import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71CountReduction

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-- Endpoint-count reduction preserves the complete semantic signature of the
two factors. This is stronger than the individual support and order fields
recorded by `CountReductionResult`: it also retains every exact separator cut
and the full `S4_71` block certificate. -/
theorem sameJointSignature_countReducedWord (word : Word Nat) :
    SameJointSignature word (countReducedWord word) := by
  have derivation := derivesCountReducedWord word
  exact
    sameJointSignature_of_factor_valid
      ⟨word, countReducedWord word⟩
      (fun valuation => derivation.sound modelsS4_69 valuation)
      (fun valuation => derivation.sound modelsS4_71 valuation)

/-- If two words have the same joint signature, their deterministic
count-reduced representatives still have that same signature. -/
theorem countReducedWord_sameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    SameJointSignature
      (countReducedWord left) (countReducedWord right) :=
  (sameJointSignature_countReducedWord left).symm.trans <|
    same.trans (sameJointSignature_countReducedWord right)

/-- The reusable two-sided count-reduction package consumed by the event
normalizer. -/
structure CountReducedPair (left right : Word Nat) : Prop where
  leftDerives :
    Derives basis left (countReducedWord left)
  rightDerives :
    Derives basis right (countReducedWord right)
  reducedSame :
    SameJointSignature
      (countReducedWord left) (countReducedWord right)
  leftTwoLimited :
    ∀ tested,
      (countReducedWord left).toList.count tested ≤ 2
  rightTwoLimited :
    ∀ tested,
      (countReducedWord right).toList.count tested ≤ 2

theorem countReducedPair
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    CountReducedPair left right := by
  refine
    ⟨derivesCountReducedWord left,
      derivesCountReducedWord right,
      countReducedWord_sameJointSignature same,
      ?_, ?_⟩
  · exact (countReductionResult left).twoLimited
  · exact (countReductionResult right).twoLimited

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
