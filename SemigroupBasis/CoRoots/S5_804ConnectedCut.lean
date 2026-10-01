import SemigroupBasis.CoRoots.S5_804ListDerives
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_804

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Right-to-left connected-envelope replay -/

private theorem reverse_perm
    {left right : List Nat} (permutation : left.Perm right) :
    left.reverse.Perm right.reverse := by
  rw [List.perm_iff_count] at permutation ⊢
  intro tested
  simpa using permutation tested

/-- Support-connectedness is invariant under reversing the displayed list. -/
theorem connectedComponentSupportConnected_reverse
    {letters : List Nat}
    (connected : ConnectedComponentSupportConnected letters) :
    ConnectedComponentSupportConnected letters.reverse := by
  intro left right shape leftNonempty rightNonempty
  have originalShape :
      letters = right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have rightReverseNonempty : right.reverse ≠ [] := by
    simpa using rightNonempty
  have leftReverseNonempty : left.reverse ≠ [] := by
    simpa using leftNonempty
  obtain ⟨letter, rightMember, leftMember⟩ :=
    connected right.reverse left.reverse originalShape
      rightReverseNonempty leftReverseNonempty
  exact ⟨letter, by simpa using leftMember, by simpa using rightMember⟩

/-- Replay the generic connected-envelope plan from right to left. Reversal
is used only in the combinatorial relation; every resulting derivation is a
direct derivation from the `S5_804` basis. -/
theorem reverseEnvelopePlanDerives
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior) :
    ListDerives
      (connectedComponentEnvelopeRender endpoint interior suffix).reverse
      (connectedComponentEnvelopeRender endpoint finalInterior []).reverse := by
  let relation : List Nat → List Nat → Prop :=
    fun left right => ListDerives left.reverse right.reverse
  have relationRefl : ∀ letters, relation letters letters := by
    intro letters
    exact S5_107.ListDerives.refl _
  have relationTrans :
      ∀ {left middle right},
        relation left middle →
          relation middle right →
            relation left right := by
    intro left middle right first second
    exact first.trans second
  have interiorPermutation :
      ∀ (currentEndpoint : Nat) (currentSuffix : List Nat)
        {left right : List Nat},
        left.Perm right →
          relation
            (connectedComponentEnvelopeRender
              currentEndpoint left currentSuffix)
            (connectedComponentEnvelopeRender
              currentEndpoint right currentSuffix) := by
    intro currentEndpoint currentSuffix left right permutation
    have reversedPermutation := reverse_perm permutation
    have core :=
      listDerivesInteriorPermutation currentEndpoint []
        reversedPermutation
    simpa [relation, connectedComponentEnvelopeRender,
      List.reverse_append, List.reverse_cons, List.append_assoc] using
        core.prepend currentSuffix.reverse
  have crossingAbsorption :
      ∀ (currentEndpoint crossing : Nat)
        (middle before after : List Nat),
        relation
          (connectedComponentEnvelopeRender currentEndpoint
            (crossing :: middle) (before ++ crossing :: after))
          (connectedComponentEnvelopeRender currentEndpoint
            (crossing :: middle ++ before) after) := by
    intro currentEndpoint crossing middle before after
    have core :=
      listDerivesRightCrossingAbsorption
        currentEndpoint crossing before.reverse middle.reverse []
    simpa [relation, connectedComponentEnvelopeRender,
      List.reverse_append, List.reverse_cons, List.append_assoc] using
        core.prepend after.reverse
  have endpointAbsorption :
      ∀ (currentEndpoint : Nat) (currentInterior before after : List Nat),
        relation
          (connectedComponentEnvelopeRender currentEndpoint
            currentInterior (before ++ currentEndpoint :: after))
          (connectedComponentEnvelopeRender currentEndpoint
            (currentInterior ++ before) after) := by
    intro currentEndpoint currentInterior before after
    have core :=
      listDerivesEndpointAbsorption currentEndpoint
        before.reverse currentInterior.reverse []
    simpa [relation, connectedComponentEnvelopeRender,
      List.reverse_append, List.reverse_cons, List.append_assoc] using
        core.prepend after.reverse
  exact plan.replay relation relationRefl relationTrans
    interiorPermutation crossingAbsorption endpointAbsorption

/-- Every non-unary support-connected component derives to an envelope whose
two endpoints are its actual final variable. The returned interior has
exactly the remaining support, before duplicate removal or sorting. -/
theorem existsConnectedComponentFinalEnvelope
    (stem : List Nat) (endpoint : Nat)
    (prefixNonempty : stem ≠ [])
    (connected :
      ConnectedComponentSupportConnected (stem ++ [endpoint])) :
    ∃ interior,
      ListDerives
        (stem ++ [endpoint])
        (endpoint :: interior ++ [endpoint]) ∧
      (∀ tested,
        (tested = endpoint ∨ tested ∈ interior) ↔
          tested ∈ stem ++ [endpoint]) := by
  have reversedConnected :
      ConnectedComponentSupportConnected
        (endpoint :: stem.reverse) := by
    have reversed :=
      connectedComponentSupportConnected_reverse connected
    simpa [List.reverse_append, List.reverse_cons] using reversed
  have lengthAtLeastTwo : 2 ≤ (endpoint :: stem.reverse).length := by
    have positive : 0 < stem.length :=
      List.length_pos_iff.mpr prefixNonempty
    simp only [List.length_cons, List.length_reverse]
    omega
  obtain ⟨initialInterior, suffix, initialShape, state⟩ :=
    connectedComponent_exists_initial_envelope
      reversedConnected lengthAtLeastTwo
  obtain ⟨finalInterior, plan⟩ := state.exists_plan
  have raw := reverseEnvelopePlanDerives plan
  have renderShape :
      connectedComponentEnvelopeRender
          endpoint initialInterior suffix =
        endpoint :: stem.reverse := by
    simpa [connectedComponentEnvelopeRender,
      List.append_assoc] using initialShape.symm
  rw [renderShape] at raw
  have absorbed :
      ListDerives
        (stem ++ [endpoint])
        (endpoint :: finalInterior.reverse ++ [endpoint]) := by
    simpa [connectedComponentEnvelopeRender, List.reverse_append,
      List.reverse_cons, List.append_assoc] using raw
  refine ⟨finalInterior.reverse, absorbed, ?_⟩
  intro tested
  have sourceSupport :
      (tested = endpoint ∨
          tested ∈ initialInterior ∨ tested ∈ suffix) ↔
        tested ∈ stem ++ [endpoint] := by
    calc
      (tested = endpoint ∨
          tested ∈ initialInterior ∨ tested ∈ suffix) ↔
          tested ∈
            connectedComponentEnvelopeRender
              endpoint initialInterior suffix := by
            simp [connectedComponentEnvelopeRender,
              List.mem_append, or_assoc, or_left_comm, or_comm]
      _ ↔ tested ∈ endpoint :: stem.reverse := by
            rw [renderShape]
      _ ↔ tested ∈ (stem ++ [endpoint]).reverse := by
            simp [List.reverse_append]
      _ ↔ tested ∈ stem ++ [endpoint] := by
            exact List.mem_reverse
  simpa using (plan.support_iff tested).trans sourceSupport

end SemigroupBasis.CoRoots.S5_804
