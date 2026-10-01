import SemigroupBasis.CoRoots.Order6SporadicSection17C5InternalBlocks

/-! Complete the beta case from actual semantic data. The gap permutation,
both boundary words and both power-marker comparisons are all discharged. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics
open SemigroupBasis

theorem SameEval.beta_iff {which : Bool} {left right : List Nat}
    (same : SameEval which left right) :
    (∃ x, Unrestricted x left) ↔ (∃ x, Unrestricted x right) := by
  constructor
  · rintro ⟨x,unrestricted⟩
    exact ⟨x,(same.unrestricted x).mp unrestricted⟩
  · rintro ⟨x,unrestricted⟩
    exact ⟨x,(same.unrestricted x).mpr unrestricted⟩

theorem SameEval.betaForms_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (beta : ∃ x, Unrestricted x left) :
    ListDerives (betaInputWord left) (betaInputWord right) := by
  have rightBeta := same.beta_iff.mp beta
  have cubeContent : ∀ x, x ∈ unrestrictedMarkers left ↔ x ∈ unrestrictedMarkers right := by
    intro x
    exact (unrestrictedMarkers_mem left x).trans
      ((same.unrestricted x).trans (unrestrictedMarkers_mem right x).symm)
  have cubeNonempty : unrestrictedMarkers left ≠ [] := by
    rcases beta with ⟨x,unrestricted⟩
    have member := (unrestrictedMarkers_mem left x).mpr unrestricted
    intro empty
    rw [empty] at member
    cases member
  have replay := betaPermutation_replay same.collectedSquares_perm cubeContent
    same.populatedInternal_perm cubeNonempty (populatedInternal_nonempty left)
    (populatedInputForm left).initial (populatedTerminal left)
  have initialEqual := same.populatedInitial_eq
  have terminalEqual := same.betaTerminal_eq beta
  rw [betaInputWord_presentation left beta,betaInputWord_presentation right rightBeta]
  rw [← initialEqual,← terminalEqual]
  exact replay

theorem SameEval.beta_derives {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (beta : ∃ x, Unrestricted x left) :
    ListDerives left right := by
  have leftReduction : ListDerives left (betaInputWord left) := betaInputWord_derives left beta
  have rightReduction : ListDerives right (betaInputWord right) :=
    betaInputWord_derives right (same.beta_iff.mp beta)
  have comparison : ListDerives (betaInputWord left) (betaInputWord right) := same.betaForms_derives beta
  exact leftReduction.trans (comparison.trans rightReduction.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.beta_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.betaForms_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.beta_derives

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics
