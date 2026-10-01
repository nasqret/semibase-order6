import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Basis
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCombinatorics

/-!
# Literal-B16 connected-component envelopes for d029

The scanner in `S5_441ParityEnvelopeCombinatorics` is purely combinatorial:
its steps preserve the exact rendered list.  This file replays those steps
using only literal substitutions of the d029 B16 laws.  In particular, no
derivation theorem specialized to the `S5_442` basis is imported or
retargeted.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact-count envelope renderer used by the structural scanner. -/
abbrev modThreeEnvelopeRender := S5_441.parityEnvelopeRender

namespace B16ListDerives

theorem refl (letters : List Nat) : B16ListDerives letters letters :=
  S5_107.ListDerives.refl (basis := B16) letters

theorem symm {left right : List Nat}
    (derivation : B16ListDerives left right) :
    B16ListDerives right left :=
  S5_107.ListDerives.symm (basis := B16) derivation

theorem trans {left middle right : List Nat}
    (first : B16ListDerives left middle)
    (second : B16ListDerives middle right) :
    B16ListDerives left right :=
  S5_107.ListDerives.trans (basis := B16) first second

theorem prepend (pre : List Nat) {left right : List Nat}
    (derivation : B16ListDerives left right) :
    B16ListDerives (pre ++ left) (pre ++ right) :=
  S5_107.ListDerives.prepend (basis := B16) pre derivation

theorem append {left right : List Nat}
    (derivation : B16ListDerives left right) (suffix : List Nat) :
    B16ListDerives (left ++ suffix) (right ++ suffix) :=
  S5_107.ListDerives.append (basis := B16) derivation suffix

theorem context (pre suffix : List Nat) {left right : List Nat}
    (derivation : B16ListDerives left right) :
    B16ListDerives
      (pre ++ left ++ suffix) (pre ++ right ++ suffix) :=
  S5_107.ListDerives.context
    (basis := B16) pre suffix derivation

theorem ofWord {left right : Word Nat}
    (derivation : Derives B16 left right) :
    B16ListDerives left.toList right.toList :=
  S5_107.ListDerives.ofWord (basis := B16) derivation

end B16ListDerives

/-- Swap two nonempty blocks in a closed singleton envelope. -/
theorem derivesEnvelopeInteriorSwap
    (endpoint left right : Word Nat) :
    Derives B16
      (((endpoint ++ left) ++ right) ++ endpoint)
      (((endpoint ++ right) ++ left) ++ endpoint) :=
  derivesAnchoredSwap endpoint left right

/-- Swap the first two interior blocks while retaining a nonempty trailing
block.  Law 9 first moves the first block behind the whole remainder; law 14
then swaps it back across the retained trailing block. -/
theorem derivesEnvelopeAdjacentSwapWithTrailing
    (endpoint left right trailing : Word Nat) :
    Derives B16
      ((((endpoint ++ left) ++ right) ++ trailing) ++ endpoint)
      ((((endpoint ++ right) ++ left) ++ trailing) ++ endpoint) := by
  have rotate :
      Derives B16
        ((((endpoint ++ left) ++ right) ++ trailing) ++ endpoint)
        ((((endpoint ++ right) ++ trailing) ++ left) ++ endpoint) := by
    simpa [Word.append_assoc] using
      derivesAnchoredSwap endpoint left (right ++ trailing)
  have restore :
      Derives B16
        ((((endpoint ++ right) ++ trailing) ++ left) ++ endpoint)
        ((((endpoint ++ right) ++ left) ++ trailing) ++ endpoint) := by
    simpa [Word.append_assoc] using
      derivesLongInteriorABCDA endpoint right trailing left
  exact rotate.trans restore

private theorem derivesRetainedCrossingBothNonempty
    (a b before after : Word Nat) :
    Derives B16
      (((((a ++ b) ++ before) ++ a) ++ after) ++ b)
      (((((a ++ b) ++ b) ++ before) ++ after) ++ a) := by
  have arrange :
      Derives B16
        (((((a ++ b) ++ before) ++ a) ++ after) ++ b)
        (((((a ++ b) ++ a) ++ before) ++ after) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a
        (derivesEnvelopeAdjacentSwapWithTrailing b before a after)
  have attach :
      Derives B16
        (((((a ++ b) ++ a) ++ before) ++ after) ++ b)
        (((((a ++ b) ++ b) ++ before) ++ after) ++ a) := by
    simpa [Word.append_assoc] using
      derivesAttachmentXYYZX a b (before ++ after)
  exact arrange.trans attach

private theorem derivesRetainedCrossingLeftEmpty
    (a b after : Word Nat) :
    Derives B16
      ((((a ++ b) ++ a) ++ after) ++ b)
      ((((a ++ b) ++ b) ++ after) ++ a) :=
  derivesAttachmentXYYZX a b after

private theorem derivesRetainedCrossingRightEmpty
    (a b before : Word Nat) :
    Derives B16
      ((((a ++ b) ++ before) ++ a) ++ b)
      ((((a ++ b) ++ b) ++ before) ++ a) := by
  have arrange :
      Derives B16
        ((((a ++ b) ++ before) ++ a) ++ b)
        ((((a ++ b) ++ a) ++ before) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a
        (derivesEnvelopeInteriorSwap b before a)
  exact arrange.trans (derivesAttachmentXYYZX a b before)

private theorem derivesRetainedCrossingBothEmpty
    (a b : Word Nat) :
    Derives B16
      (((a ++ b) ++ a) ++ b)
      (((a ++ b) ++ b) ++ a) :=
  derivesSquareFinalSwitch a b

/-- Retain both copies of a crossing while absorbing the suffix copy into
the envelope interior. -/
theorem listDerivesRetainedCrossing
    (a b : Word Nat) (before after : List Nat) :
    B16ListDerives
      (a.toList ++ b.toList ++ before ++ a.toList ++ after ++ b.toList)
      (a.toList ++ b.toList ++ b.toList ++ before ++ after ++ a.toList) := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          simpa [Word.toList_append, List.append_assoc] using
            B16ListDerives.ofWord
              (derivesRetainedCrossingBothEmpty a b)
      | cons afterHead afterTail =>
          let afterWord := S5_107.listWordOfCons afterHead afterTail
          simpa [afterWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              B16ListDerives.ofWord
                (derivesRetainedCrossingLeftEmpty a b afterWord)
  | cons beforeHead beforeTail =>
      let beforeWord := S5_107.listWordOfCons beforeHead beforeTail
      cases after with
      | nil =>
          simpa [beforeWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              B16ListDerives.ofWord
                (derivesRetainedCrossingRightEmpty a b beforeWord)
      | cons afterHead afterTail =>
          let afterWord := S5_107.listWordOfCons afterHead afterTail
          simpa [beforeWord, afterWord, S5_107.listWordOfCons,
            Word.toList, Word.toList_append, List.append_assoc] using
              B16ListDerives.ofWord
                (derivesRetainedCrossingBothNonempty
                  a b beforeWord afterWord)

private theorem derivesRetainedEndpointBothNonempty
    (endpoint before after : Word Nat) :
    Derives B16
      ((((endpoint ++ before) ++ endpoint) ++ after) ++ endpoint)
      ((((endpoint ++ before) ++ after) ++ endpoint) ++ endpoint) := by
  have first :
      Derives B16
        ((((endpoint ++ before) ++ endpoint) ++ after) ++ endpoint)
        ((((endpoint ++ after) ++ before) ++ endpoint) ++ endpoint) := by
    simpa [Word.append_assoc] using
      derivesEnvelopeInteriorSwap endpoint (before ++ endpoint) after
  have second :
      Derives B16
        ((((endpoint ++ after) ++ before) ++ endpoint) ++ endpoint)
        ((((endpoint ++ before) ++ after) ++ endpoint) ++ endpoint) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesEnvelopeInteriorSwap endpoint after before) endpoint
  exact first.trans second

/-- Move a later endpoint occurrence next to the closing endpoint pair. -/
theorem listDerivesRetainedEndpoint
    (endpoint : Word Nat) (before after : List Nat) :
    B16ListDerives
      (endpoint.toList ++ before ++ endpoint.toList ++ after ++
        endpoint.toList)
      (endpoint.toList ++ before ++ after ++ endpoint.toList ++
        endpoint.toList) := by
  cases after with
  | nil =>
      simpa [List.append_assoc] using
        B16ListDerives.refl
          (endpoint.toList ++ before ++ endpoint.toList ++
            endpoint.toList)
  | cons afterHead afterTail =>
      let afterWord := S5_107.listWordOfCons afterHead afterTail
      cases before with
      | nil =>
          simpa [afterWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              B16ListDerives.ofWord
                (derivesEndpointTransfer endpoint afterWord)
      | cons beforeHead beforeTail =>
          let beforeWord := S5_107.listWordOfCons beforeHead beforeTail
          simpa [beforeWord, afterWord, S5_107.listWordOfCons,
            Word.toList, Word.toList_append, List.append_assoc] using
              B16ListDerives.ofWord
                (derivesRetainedEndpointBothNonempty
                  endpoint beforeWord afterWord)

/-- Swap two nonempty leading interior blocks while retaining an arbitrary
interior tail and outer suffix. -/
theorem listDerivesEnvelopeBlockSwap
    (endpoint leftHead rightHead : Nat)
    (leftTail rightTail trailing suffix : List Nat) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint
        ((leftHead :: leftTail) ++
          (rightHead :: rightTail) ++ trailing) suffix)
      (modThreeEnvelopeRender endpoint
        ((rightHead :: rightTail) ++
          (leftHead :: leftTail) ++ trailing) suffix) := by
  let anchor := Word.singleton endpoint
  let left := S5_107.listWordOfCons leftHead leftTail
  let right := S5_107.listWordOfCons rightHead rightTail
  cases trailing with
  | nil =>
      simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
        anchor, left, right, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          B16ListDerives.append
            (B16ListDerives.ofWord
              (derivesEnvelopeInteriorSwap anchor left right))
            suffix
  | cons trailingHead trailingTail =>
      let retained :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
        anchor, left, right, retained, S5_107.listWordOfCons,
        Word.toList, Word.toList_singleton, List.append_assoc] using
          B16ListDerives.context [] suffix <|
            B16ListDerives.ofWord <|
              derivesEnvelopeAdjacentSwapWithTrailing
                anchor left right retained

/-- Any permutation of an initial interior segment is derivable while the
remaining interior and outer suffix stay fixed. -/
theorem listDerivesEnvelopeInteriorPermutationWithTrailing
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    ∀ (trailing suffix : List Nat),
      B16ListDerives
        (modThreeEnvelopeRender endpoint (left ++ trailing) suffix)
        (modThreeEnvelopeRender endpoint (right ++ trailing) suffix) := by
  induction permutation with
  | nil =>
      intro trailing suffix
      exact B16ListDerives.refl _
  | @cons letter source target permutation induction =>
      intro trailing suffix
      cases source with
      | nil =>
          have targetEmpty : target = [] := permutation.nil_eq.symm
          subst target
          exact B16ListDerives.refl _
      | cons sourceHead sourceTail =>
          have targetNonempty : target ≠ [] := by
            intro targetEmpty
            subst target
            have lengthEq := permutation.length_eq
            simp at lengthEq
          obtain ⟨targetHead, targetTail, rfl⟩ :=
            List.exists_cons_of_ne_nil targetNonempty
          have moveHeadRight :=
            listDerivesEnvelopeBlockSwap
              endpoint letter sourceHead
              [] sourceTail trailing suffix
          have permuteTail := induction (letter :: trailing) suffix
          have permuteTail' :
              B16ListDerives
                (modThreeEnvelopeRender endpoint
                  ((sourceHead :: sourceTail) ++
                    [letter] ++ trailing) suffix)
                (modThreeEnvelopeRender endpoint
                  ((targetHead :: targetTail) ++
                    [letter] ++ trailing) suffix) := by
            simpa [List.append_assoc] using permuteTail
          have moveHeadLeft :=
            B16ListDerives.symm <|
              listDerivesEnvelopeBlockSwap
                endpoint letter targetHead
                [] targetTail trailing suffix
          simpa [List.append_assoc] using
            B16ListDerives.trans moveHeadRight <|
              B16ListDerives.trans permuteTail' moveHeadLeft
  | swap first second rest =>
      intro trailing suffix
      simpa [List.append_assoc] using
        listDerivesEnvelopeBlockSwap
          endpoint second first [] [] (rest ++ trailing) suffix
  | trans _ _ inductionFirst inductionSecond =>
      intro trailing suffix
      exact
        B16ListDerives.trans
          (inductionFirst trailing suffix)
          (inductionSecond trailing suffix)

/-- Any permutation of the full closed-envelope interior is derivable. -/
theorem listDerivesEnvelopeInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint left suffix)
      (modThreeEnvelopeRender endpoint right suffix) := by
  simpa using
    listDerivesEnvelopeInteriorPermutationWithTrailing
      endpoint permutation [] suffix

private theorem replayEnvelopeCrossing
    {endpoint crossing : Nat}
    {interior middle before after : List Nat}
    (arrange : interior.Perm (crossing :: middle)) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior
        (before ++ crossing :: after))
      (modThreeEnvelopeRender endpoint
        (crossing :: crossing :: (middle ++ before)) after) := by
  have arrangeInterior :
      B16ListDerives
        (modThreeEnvelopeRender endpoint interior
          (before ++ crossing :: after))
        (modThreeEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after)) :=
    listDerivesEnvelopeInteriorPermutation
      endpoint (before ++ crossing :: after) arrange
  have absorbCrossing :
      B16ListDerives
        (modThreeEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after))
        (modThreeEnvelopeRender endpoint
          (crossing :: crossing :: (middle ++ before)) after) := by
    simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
      Word.toList_singleton, List.append_assoc] using
        B16ListDerives.append
          (listDerivesRetainedCrossing
            (Word.singleton endpoint)
            (Word.singleton crossing) middle before)
          after
  exact B16ListDerives.trans arrangeInterior absorbCrossing

private theorem replayEnvelopeEndpoint
    {endpoint : Nat} {interior before after : List Nat} :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior
        (before ++ endpoint :: after))
      (modThreeEnvelopeRender endpoint
        (interior ++ before ++ [endpoint]) after) := by
  simpa [modThreeEnvelopeRender, S5_441.parityEnvelopeRender,
    Word.toList_singleton, List.append_assoc] using
      B16ListDerives.append
        (listDerivesRetainedEndpoint
          (Word.singleton endpoint) interior before)
        after

/-- Replay one exact-count scanner step over literal B16. -/
theorem envelopeStepReplay
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      S5_441.ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior suffix)
      (modThreeEnvelopeRender endpoint nextInterior nextSuffix) := by
  cases step with
  | crossing arrange => exact replayEnvelopeCrossing arrange
  | endpoint => exact replayEnvelopeEndpoint

/-- Replay a terminating exact-count scanner plan over literal B16. -/
theorem envelopePlanReplay
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      S5_441.ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    B16ListDerives
      (modThreeEnvelopeRender endpoint interior suffix)
      (modThreeEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current => exact B16ListDerives.refl _
  | advance step remaining induction =>
      exact B16ListDerives.trans
        (envelopeStepReplay step) induction

/-- Every support-connected component of length at least two derives to a
closed exact-count envelope at its first letter. -/
theorem exists_envelopeDerivation_of_connected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      B16ListDerives
          (head :: tail)
          (modThreeEnvelopeRender head finalInterior []) ∧
        (head :: tail).Perm
          (modThreeEnvelopeRender head finalInterior []) := by
  obtain
    ⟨interior, suffix, finalInterior, shape, _state, plan⟩ :=
      S5_441.exists_parityEnvelopePlan_of_connected
        connected lengthAtLeastTwo
  refine ⟨finalInterior, ?_, ?_⟩
  · rw [shape]
    exact envelopePlanReplay plan
  · rw [shape]
    exact S5_441.ParityEnvelopePlan.render_perm plan

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16
