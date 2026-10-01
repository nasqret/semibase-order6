import SemigroupBasis.CoRoots.S5_441GapMixedParityDerivations
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCombinatorics

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

/-- Swap two nonempty leading interior blocks while retaining an arbitrary
interior tail and suffix after the closing endpoint. The empty-tail case is
the primitive anchored swap; the nonempty-tail case uses the audited
adjacent-block replay. -/
theorem listDerivesParityEnvelopeBlockSwap
    (endpoint leftHead rightHead : Nat)
    (leftTail rightTail trailing suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        ((leftHead :: leftTail) ++
          (rightHead :: rightTail) ++ trailing) suffix)
      (parityEnvelopeRender endpoint
        ((rightHead :: rightTail) ++
          (leftHead :: leftTail) ++ trailing) suffix) := by
  let anchor := Word.singleton endpoint
  let left := S5_107.listWordOfCons leftHead leftTail
  let right := S5_107.listWordOfCons rightHead rightTail
  cases trailing with
  | nil =>
      simpa [parityEnvelopeRender, anchor, left, right,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          ListDerives.append
            (ListDerives.ofWord
              (derivesInteriorSwap anchor left right))
            suffix
  | cons trailingHead trailingTail =>
      let retained :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [parityEnvelopeRender, anchor, left, right, retained,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_singleton, List.append_assoc] using
          listDerivesAdjacentInteriorBlockSwapContext
            [] suffix anchor left right retained

/-- Any permutation of an initial envelope-interior segment is derivable
while an arbitrary interior tail and outer suffix remain fixed. The `cons`
case moves the fixed head behind the permuted segment, applies the induction
hypothesis with that head in the retained tail, and moves it back. -/
theorem listDerivesParityEnvelopeInteriorPermutationWithTrailing
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    ∀ (trailing suffix : List Nat),
      ListDerives
        (parityEnvelopeRender endpoint
          (left ++ trailing) suffix)
        (parityEnvelopeRender endpoint
          (right ++ trailing) suffix) := by
  induction permutation with
  | nil =>
      intro trailing suffix
      exact ListDerives.refl _
  | @cons letter source target permutation ih =>
      intro trailing suffix
      cases source with
      | nil =>
          have targetEmpty : target = [] :=
            permutation.nil_eq.symm
          subst target
          exact ListDerives.refl _
      | cons sourceHead sourceTail =>
          have targetNonempty : target ≠ [] := by
            intro targetEmpty
            subst target
            have lengthEq := permutation.length_eq
            simp at lengthEq
          obtain ⟨targetHead, targetTail, rfl⟩ :=
            List.exists_cons_of_ne_nil targetNonempty
          have moveHeadRight :=
            listDerivesParityEnvelopeBlockSwap
              endpoint letter sourceHead
              [] sourceTail trailing suffix
          have permuteTail :=
            ih (letter :: trailing) suffix
          have permuteTail' :
              ListDerives
                (parityEnvelopeRender endpoint
                  ((sourceHead :: sourceTail) ++
                    [letter] ++ trailing) suffix)
                (parityEnvelopeRender endpoint
                  ((targetHead :: targetTail) ++
                    [letter] ++ trailing) suffix) := by
            simpa [List.append_assoc] using permuteTail
          have moveHeadLeft :=
            ListDerives.symm <|
              listDerivesParityEnvelopeBlockSwap
                endpoint letter targetHead
                [] targetTail trailing suffix
          simpa [List.append_assoc] using
            ListDerives.trans moveHeadRight <|
              ListDerives.trans permuteTail' moveHeadLeft
  | swap first second rest =>
      intro trailing suffix
      simpa [List.append_assoc] using
        listDerivesParityEnvelopeBlockSwap
          endpoint second first [] []
          (rest ++ trailing) suffix
  | trans _ _ ihFirst ihSecond =>
      intro trailing suffix
      exact
        ListDerives.trans
          (ihFirst trailing suffix)
          (ihSecond trailing suffix)

/-- Any permutation of the full interior between matching endpoints is
derivable while the suffix after the closing endpoint remains fixed. -/
theorem listDerivesParityEnvelopeInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (permutation : left.Perm right) :
    ListDerives
      (parityEnvelopeRender endpoint left suffix)
      (parityEnvelopeRender endpoint right suffix) := by
  simpa using
    listDerivesParityEnvelopeInteriorPermutationWithTrailing
      endpoint permutation [] suffix

namespace ParityEnvelopeStep

private theorem replayCrossing
    {endpoint crossing : Nat}
    {interior middle before after : List Nat}
    (arrange : interior.Perm (crossing :: middle)) :
    ListDerives
      (parityEnvelopeRender endpoint interior
        (before ++ crossing :: after))
      (parityEnvelopeRender endpoint
        (crossing :: crossing :: (middle ++ before)) after) := by
  have arrangeInterior :
      ListDerives
        (parityEnvelopeRender endpoint interior
          (before ++ crossing :: after))
        (parityEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after)) :=
    listDerivesParityEnvelopeInteriorPermutation
      endpoint (before ++ crossing :: after) arrange
  have absorbCrossing :
      ListDerives
        (parityEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after))
        (parityEnvelopeRender endpoint
          (crossing :: crossing :: (middle ++ before))
          after) := by
    simpa [parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        ListDerives.append
          (listDerivesRetainedCrossing
            (Word.singleton endpoint)
            (Word.singleton crossing)
            middle before)
          after
  exact ListDerives.trans arrangeInterior absorbCrossing

private theorem replayEndpoint
    {endpoint : Nat}
    {interior before after : List Nat} :
    ListDerives
      (parityEnvelopeRender endpoint interior
        (before ++ endpoint :: after))
      (parityEnvelopeRender endpoint
        (interior ++ before ++ [endpoint]) after) := by
  simpa [parityEnvelopeRender, Word.toList_singleton,
    List.append_assoc] using
      ListDerives.append
        (listDerivesRetainedEndpoint
          (Word.singleton endpoint) interior before)
        after

/-- Replay every abstract parity-envelope transition as an `S5_441`
`ListDerives` derivation. Crossing steps first realize their recorded
interior permutation and then apply the retained-crossing rewrite. Endpoint
steps are exactly the retained-endpoint rewrite. -/
theorem replay
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    ListDerives
      (parityEnvelopeRender endpoint interior suffix)
      (parityEnvelopeRender endpoint
        nextInterior nextSuffix) := by
  cases step with
  | crossing arrange =>
      exact replayCrossing arrange
  | endpoint =>
      exact replayEndpoint

/-- Replay a parity-envelope transition inside arbitrary outer contexts. -/
theorem replayContext
    (pre post : List Nat)
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    ListDerives
      (pre ++ parityEnvelopeRender endpoint interior suffix ++ post)
      (pre ++ parityEnvelopeRender endpoint
        nextInterior nextSuffix ++ post) :=
  ListDerives.context pre post step.replay

end ParityEnvelopeStep

namespace ParityEnvelopePlan

/-- Replay a complete parity-envelope plan as one concrete derivation. -/
theorem replay
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    ListDerives
      (parityEnvelopeRender endpoint interior suffix)
      (parityEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact ListDerives.refl _
  | advance step remaining ih =>
      exact ListDerives.trans step.replay ih

/-- Replay a complete parity-envelope plan inside arbitrary outer contexts. -/
theorem replayContext
    (pre post : List Nat)
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    ListDerives
      (pre ++ parityEnvelopeRender endpoint interior suffix ++ post)
      (pre ++ parityEnvelopeRender endpoint finalInterior [] ++ post) :=
  ListDerives.context pre post plan.replay

end ParityEnvelopePlan

namespace ParityEnvelopeState

/-- A linked suffix admits both an abstract terminating plan and its concrete
`ListDerives` replay. -/
theorem exists_replay
    {endpoint : Nat} {interior suffix : List Nat}
    (state : ParityEnvelopeState endpoint interior suffix) :
    ∃ finalInterior,
      ParityEnvelopePlan endpoint
          interior suffix finalInterior ∧
        ListDerives
          (parityEnvelopeRender endpoint interior suffix)
          (parityEnvelopeRender endpoint finalInterior []) := by
  obtain ⟨finalInterior, plan⟩ := state.exists_plan
  exact ⟨finalInterior, plan, plan.replay⟩

end ParityEnvelopeState

/-- Every support-connected list of length at least two concretely derives
to a fixed-endpoint parity envelope with empty unprocessed suffix. -/
theorem exists_parityEnvelopeDerivation_of_connected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
        (head :: tail)
        (parityEnvelopeRender head finalInterior []) := by
  obtain
    ⟨interior, suffix, finalInterior, shape, _state, plan⟩ :=
      exists_parityEnvelopePlan_of_connected
        connected lengthAtLeastTwo
  refine ⟨finalInterior, ?_⟩
  rw [shape]
  exact plan.replay

end SemigroupBasis.CoRoots.S5_441
