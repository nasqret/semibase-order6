import SemigroupBasis.Examples.ConnectedComponentFourNormalize
import SemigroupBasis.Examples.ConnectedComponentFourSemanticComplete
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Unrestricted completeness of the six-law identity basis for the
catalogue representative `S4_70`. -/
theorem connectedComponentFourBasis_complete :
    BasisFor connectedComponentFour.semigroup
      connectedComponentFourBasis := by
  refine ⟨connectedComponentFourBasis_models, ?_⟩
  intro identity valid
  have lhsDerivation :=
    connectedComponentFour_derivesCanonical identity.lhs
  have rhsDerivation :=
    connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.lhs) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      lhsDerivation.sound
        connectedComponentFourBasis_models valuation
    have rhsSound :=
      rhsDerivation.sound
        connectedComponentFourBasis_models valuation
    exact lhsSound.symm.trans <|
      (valid valuation).trans rhsSound
  have signaturesEqual :
      connectedComponentSignaturesWord identity.lhs =
        connectedComponentSignaturesWord identity.rhs := by
    apply connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical identity.lhs)
      (connectedComponentFourSignaturesWord_canonical identity.rhs)
      (connectedComponentCanonicalRender identity.lhs)
      (connectedComponentCanonicalRender identity.rhs)
    · change
        (connectedComponentCanonicalRender identity.lhs).toList =
          connectedComponentCanonicalRenderList identity.lhs.toList
      exact connectedComponentCanonicalRender_toList identity.lhs
    · change
        (connectedComponentCanonicalRender identity.rhs).toList =
          connectedComponentCanonicalRenderList identity.rhs.toList
      exact connectedComponentCanonicalRender_toList identity.rhs
    · exact normalizedEval
  have normalWordsEqual :
      connectedComponentCanonicalRender identity.lhs =
        connectedComponentCanonicalRender identity.rhs :=
    connectedComponentCanonicalRender_eq_of_signature_eq
      signaturesEqual
  have bridge :
      Derives connectedComponentFourBasis
        (connectedComponentCanonicalRender identity.lhs)
        (connectedComponentCanonicalRender identity.rhs) := by
    rw [normalWordsEqual]
    exact Derives.refl _
  exact lhsDerivation.trans <|
    bridge.trans rhsDerivation.symm

def connectedComponentFourOppositeBasis : List (Identity Nat) :=
  reversedBasis connectedComponentFourBasis

/-- The formally reversed six-law basis is complete for the opposite
semigroup. -/
theorem connectedComponentFourOppositeBasis_complete :
    BasisFor connectedComponentFour.semigroup.opposite
      connectedComponentFourOppositeBasis := by
  simpa [connectedComponentFourOppositeBasis] using
    connectedComponentFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
