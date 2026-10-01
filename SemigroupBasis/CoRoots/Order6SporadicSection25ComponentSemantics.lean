import SemigroupBasis.CoRoots.Order6SporadicSection25ConnectedClosure
import SemigroupBasis.CoRoots.Order6SporadicSection25LibraryBridges
import SemigroupBasis.Generated.S4_70

/-! Extract the actual ordered component signature from the S4_70 factor.
The lower-order normalizer is used only to prove a semantic invariant.
Its arbitrary-interior permutation rules are not replayed in our raw basis. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem supportConnected_iff_library (word : List Nat) :
    SupportConnected word ↔ Examples.ConnectedComponentSupportConnected word := Iff.rfl

theorem actualDecomposition_supportConnected (word : Word Nat) :
    ∀ component ∈ Examples.connectedComponentDecomposeWord word,
      SupportConnected component := by
  intro component member
  exact (supportConnected_iff_library component).2
    (Examples.connectedComponentDecomposeWord_supportConnected word component member)

theorem actualF4Valid_componentSignatures (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup) :
    Examples.connectedComponentSignaturesWord identity.lhs =
      Examples.connectedComponentSignaturesWord identity.rhs := by
  have modelValid : identity.SatisfiedBy Examples.connectedComponentFour.semigroup := by
    change identity.SatisfiedBy Generated.S4_70.table.semigroup
    rw [Generated.S4_70.table_eq_canonical_catalogue]
    exact valid
  have leftDerivation := Examples.connectedComponentFour_derivesCanonical identity.lhs
  have rightDerivation := Examples.connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval : ∀ valuation : Nat → Fin 4,
      Examples.connectedComponentFour.semigroup.eval valuation
          (Examples.connectedComponentCanonicalRender identity.lhs) =
        Examples.connectedComponentFour.semigroup.eval valuation
          (Examples.connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have leftSound := leftDerivation.sound Examples.connectedComponentFourBasis_models valuation
    have rightSound := rightDerivation.sound Examples.connectedComponentFourBasis_models valuation
    exact leftSound.symm.trans ((modelValid valuation).trans rightSound)
  apply Examples.connectedComponentCanonical_eq_of_equalEval
    (Examples.connectedComponentFourSignaturesWord_canonical identity.lhs)
    (Examples.connectedComponentFourSignaturesWord_canonical identity.rhs)
    (Examples.connectedComponentCanonicalRender identity.lhs)
    (Examples.connectedComponentCanonicalRender identity.rhs)
  · change (Examples.connectedComponentCanonicalRender identity.lhs).toList =
      Examples.connectedComponentCanonicalRenderList identity.lhs.toList
    exact Examples.connectedComponentCanonicalRender_toList identity.lhs
  · change (Examples.connectedComponentCanonicalRender identity.rhs).toList =
      Examples.connectedComponentCanonicalRenderList identity.rhs.toList
    exact Examples.connectedComponentCanonicalRender_toList identity.rhs
  · exact normalizedEval

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.supportConnected_iff_library
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualDecomposition_supportConnected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualF4Valid_componentSignatures

end SemigroupBasis.CoRoots.Order6SporadicSection25
