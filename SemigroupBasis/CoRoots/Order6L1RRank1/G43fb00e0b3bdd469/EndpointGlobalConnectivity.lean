import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.EndpointSaturation

/-!
# Global endpoint-pivot connectivity for G43

This off-tree module closes the fresh endpoint route.  It uses only the
contextual closure of the 52 frozen paths, the saturated endpoint state, and
the strictly decreasing endpoint bubble.  It does not import the retired G43
`Primitives`, `Normalization`, or `Completeness` modules.

Static review only: this source has not been elaborated locally.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis

/-- The unique raw endpoint list determined by the complete Layer-A
signature: all first endpoints followed by all last endpoints. -/
def endpointPivot (anchor : Word Nat) : List Nat :=
  (jointSignature anchor).factorNormal.dropLast ++
    (jointSignature anchor).lastOrder

/-- Every contextual frozen step can be traversed backwards because the
witness records both orientations of every frozen path. -/
theorem contextualFrozenStep_symm
    {left right : List Nat}
    (step : ContextualFrozenStep left right) :
    ContextualFrozenStep right left := by
  obtain ⟨witness, rfl, rfl⟩ := step
  cases witness with
  | mk rule direction leftContext rightContext =>
      cases direction with
      | forward =>
          exact
            ⟨⟨rule, .reverse, leftContext, rightContext⟩, rfl, rfl⟩
      | reverse =>
          exact
            ⟨⟨rule, .forward, leftContext, rightContext⟩, rfl, rfl⟩

/-- Reverse an exact contextual frozen-path chain. -/
theorem ContextualFrozenRTC.symm
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right) :
    ContextualFrozenRTC right left := by
  induction reachable with
  | refl letters => exact ContextualFrozenRTC.refl letters
  | cons step rest inductionHypothesis =>
      exact ContextualFrozenRTC.trans inductionHypothesis
        (ContextualFrozenRTC.cons
          (contextualFrozenStep_symm step)
          (ContextualFrozenRTC.refl _))

private theorem firstProjection_eq_nil_of_firstEndpointCount_eq_zero :
    ∀ tags : List EndpointTag,
      firstEndpointCount tags = 0 → firstProjection tags = []
  | [], _ => rfl
  | ⟨letter, .first⟩ :: rest, zero => by
      simp [firstEndpointCount] at zero
  | ⟨letter, .last⟩ :: rest, zero => by
      have restZero : firstEndpointCount rest = 0 := by
        simpa [firstEndpointCount] using zero
      simpa [firstProjection] using
        firstProjection_eq_nil_of_firstEndpointCount_eq_zero rest restZero

/-- A tag list with no `last`-before-`first` inversion is exactly its first
projection, tagged `first`, followed by its last projection, tagged `last`. -/
private theorem endpointTags_eq_projections_of_lfInversions_eq_zero :
    ∀ tags : List EndpointTag,
      lfInversions tags = 0 →
        tags =
          (firstProjection tags).map EndpointTag.first ++
            (lastProjection tags).map EndpointTag.last
  | [], _ => rfl
  | ⟨letter, .first⟩ :: rest, zero => by
      have restZero : lfInversions rest = 0 := by
        simpa [lfInversions] using zero
      have restShape :=
        endpointTags_eq_projections_of_lfInversions_eq_zero rest restZero
      simpa [firstProjection, lastProjection, EndpointTag.first] using
        congrArg (List.cons (EndpointTag.first letter)) restShape
  | ⟨letter, .last⟩ :: rest, zero => by
      have countZero : firstEndpointCount rest = 0 := by
        simp only [lfInversions] at zero
        omega
      have restZero : lfInversions rest = 0 := by
        simp only [lfInversions] at zero
        omega
      have firstNil :=
        firstProjection_eq_nil_of_firstEndpointCount_eq_zero rest countZero
      have restShape :=
        endpointTags_eq_projections_of_lfInversions_eq_zero rest restZero
      simpa [firstProjection, lastProjection, EndpointTag.last, firstNil] using
        congrArg (List.cons (EndpointTag.last letter)) restShape

/-- Bubble a saturated endpoint state to the signature-determined pivot.
Termination is the strict decrease supplied by `saturated_bubble_progress`. -/
theorem saturatedEndpointState_reaches_endpointPivot
    (anchor : Word Nat) {letters : List Nat}
    (state : SaturatedEndpointState anchor letters) :
    ContextualFrozenRTC letters (endpointPivot anchor) := by
  by_cases zero : lfInversions (tagEndpoints letters) = 0
  · have tagsShape :=
      endpointTags_eq_projections_of_lfInversions_eq_zero
        (tagEndpoints letters) zero
    have erased := congrArg (List.map EndpointTag.letter) tagsShape
    have erasedShape :
        letters =
          firstProjection (tagEndpoints letters) ++
            lastProjection (tagEndpoints letters) := by
      simpa [List.map_append, Function.comp_def,
        EndpointTag.first, EndpointTag.last] using erased
    have lettersShape : letters = endpointPivot anchor := by
      calc
        letters =
            firstProjection (tagEndpoints letters) ++
              lastProjection (tagEndpoints letters) := erasedShape
        _ = (jointSignature anchor).factorNormal.dropLast ++
              (jointSignature anchor).lastOrder := by
                rw [state.firstOrder, state.lastOrder]
        _ = endpointPivot anchor := rfl
    rw [lettersShape]
    exact ContextualFrozenRTC.refl _
  · have positive : 0 < lfInversions (tagEndpoints letters) :=
      Nat.pos_of_ne_zero zero
    obtain ⟨next, oneStep, nextState, decrease⟩ :=
      saturated_bubble_progress anchor state positive
    exact ContextualFrozenRTC.trans oneStep
      (saturatedEndpointState_reaches_endpointPivot anchor nextState)
termination_by lfInversions (tagEndpoints letters)
decreasing_by exact decrease

/-- Every nonempty word reaches its unique signature-determined endpoint
pivot through exact contextual applications of the 52 frozen paths. -/
theorem contextualFrozenRTC_endpointPivot (anchor : Word Nat) :
    ContextualFrozenRTC anchor.toList (endpointPivot anchor) := by
  obtain ⟨letters, saturationRoute, state⟩ :=
    existsSaturatedEndpointState anchor
  exact ContextualFrozenRTC.trans saturationRoute
    (saturatedEndpointState_reaches_endpointPivot anchor state)

/-- Equal complete Layer-A signatures are connected by the exact contextual
closure of the 52 frozen paths, via their common endpoint pivot. -/
theorem contextualFrozenRTC_of_jointSignature_eq
    {left right : Word Nat}
    (same : jointSignature left = jointSignature right) :
    ContextualFrozenRTC left.toList right.toList := by
  have leftRoute := contextualFrozenRTC_endpointPivot left
  have rightRoute := contextualFrozenRTC_endpointPivot right
  have pivotEq : endpointPivot left = endpointPivot right := by
    unfold endpointPivot
    rw [same]
  exact ContextualFrozenRTC.trans leftRoute (by
    rw [pivotEq]
    exact ContextualFrozenRTC.symm rightRoute)

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
