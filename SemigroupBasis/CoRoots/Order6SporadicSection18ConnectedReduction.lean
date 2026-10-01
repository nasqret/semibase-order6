import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedMerge
import SemigroupBasis.CoRoots.Order6SporadicSection18SimpleFree

/-! Exact assembly boundaries after C7 connectedization. These implications
retain an explicit unresolved completeness premise; neither is an unconditional
basis certificate for C7. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection12

/-- It suffices to derive valid identities between closed envelopes containing
a simple letter. All unrestricted reduction and simple-free cases are proved. -/
theorem basisFor_of_simpleClosedEnvelopes
    (complete : ∀ (x y : Nat) (leftInterior rightInterior : List Nat),
      (Identity.mk (closedEnvelopeWord x leftInterior)
        (closedEnvelopeWord y rightInterior)).SatisfiedBy Actual.table.semigroup →
      Canonical.HasSimple (closedEnvelopeWord x leftInterior).toList →
      Derives basis (closedEnvelopeWord x leftInterior) (closedEnvelopeWord y rightInterior)) :
    BasisFor Actual.table.semigroup basis := by
  apply Reduction.basisFor_of_simplePairwiseConnected
  intro identity valid leftProduct rightProduct simple
  obtain ⟨x, leftInterior, _, leftDerivation⟩ :=
    existsMatchingConnectedDerivative identity.lhs leftProduct
  obtain ⟨y, rightInterior, _, rightDerivation⟩ :=
    existsMatchingConnectedDerivative identity.rhs rightProduct
  have normalizedValid :
      (Identity.mk (closedEnvelopeWord x leftInterior)
        (closedEnvelopeWord y rightInterior)).SatisfiedBy Actual.table.semigroup := by
    intro valuation
    have leftEqual := Derives.sound Actual.models leftDerivation valuation
    have rightEqual := Derives.sound Actual.models rightDerivation valuation
    exact leftEqual.symm.trans ((valid valuation).trans rightEqual)
  have leftSame := Actual.derives_sameEval (S5_107.ListDerives.ofWord leftDerivation)
  have normalizedSimple : Canonical.HasSimple (closedEnvelopeWord x leftInterior).toList := by
    obtain ⟨letter, one⟩ := simple
    exact ⟨letter, (leftSame.countOne letter).mp one⟩
  have middle := complete x y leftInterior rightInterior normalizedValid normalizedSimple
  exact leftDerivation.trans (middle.trans rightDerivation.symm)

/-- A completeness theorem on simple-containing connected identities also
discharges the same full C7 BasisFor goal. The premise is still open. -/
theorem basisFor_of_simpleConnected
    (complete : ∀ identity : Identity Nat,
      identity.SatisfiedBy Actual.table.semigroup →
      Connected identity.lhs → Connected identity.rhs →
      Canonical.HasSimple identity.lhs.toList →
      Derives basis identity.lhs identity.rhs) :
    BasisFor Actual.table.semigroup basis := by
  apply basisFor_of_simpleClosedEnvelopes
  intro x y leftInterior rightInterior valid simple
  exact complete ⟨closedEnvelopeWord x leftInterior, closedEnvelopeWord y rightInterior⟩ valid
    (closedEnvelopeWord_connected x leftInterior)
    (closedEnvelopeWord_connected y rightInterior) simple

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.basisFor_of_simpleClosedEnvelopes
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization.basisFor_of_simpleConnected

end SemigroupBasis.CoRoots.Order6SporadicSection18.Connectedization
