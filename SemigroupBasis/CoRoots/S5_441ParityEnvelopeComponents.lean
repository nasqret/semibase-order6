import SemigroupBasis.CoRoots.S5_441GapSeparatorFree
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeReplay
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCombine

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

/-- A support-connected component normalizes to a closed parity envelope
without changing its exact multiset of letters. -/
theorem exists_parityEnvelopeDerivation_of_connected_with_perm
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
          (head :: tail)
          (parityEnvelopeRender head finalInterior []) ∧
        (head :: tail).Perm
          (parityEnvelopeRender head finalInterior []) := by
  obtain
    ⟨interior, suffix, finalInterior, shape, _state, plan⟩ :=
      exists_parityEnvelopePlan_of_connected
        connected lengthAtLeastTwo
  refine ⟨finalInterior, ?_, ?_⟩
  · rw [shape]
    exact plan.replay
  · rw [shape]
    exact plan.render_perm

/-- The adjacent-envelope combine target is an exact permutation of the two
source envelopes. -/
theorem adjacentParityEnvelopeCombine_perm
    (a b : Nat) (p q : List Nat) :
    (parityEnvelopeRender a p [] ++
        parityEnvelopeRender b q []).Perm
      (parityEnvelopeRender a
        (p ++ [b, b] ++ q) []) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [parityEnvelopeRender, List.count_cons,
    List.count_append, List.count_nil]
  omega

/-- A nonempty list of support-connected components, each of length at least
two, folds to one closed parity envelope. The fold preserves the exact
multiset of the flattened component list. -/
theorem exists_parityEnvelopeDerivation_of_components
    (components : List (List Nat))
    (componentsNonempty : components ≠ [])
    (supportConnected :
      ∀ component ∈ components,
        ConnectedComponentSupportConnected component)
    (lengthAtLeastTwo :
      ∀ component ∈ components, 2 ≤ component.length) :
    ∃ endpoint finalInterior,
      ListDerives
          components.flatten
          (parityEnvelopeRender endpoint finalInterior []) ∧
        components.flatten.Perm
          (parityEnvelopeRender endpoint finalInterior []) := by
  induction components with
  | nil =>
      exact False.elim (componentsNonempty rfl)
  | cons component rest ih =>
      have componentLengthAtLeastTwo :
          2 ≤ component.length :=
        lengthAtLeastTwo component (by simp)
      have componentNonempty : component ≠ [] := by
        intro componentEmpty
        subst component
        simp at componentLengthAtLeastTwo
      obtain ⟨endpoint, tail, rfl⟩ :=
        List.exists_cons_of_ne_nil componentNonempty
      obtain
        ⟨interior, componentDerivation, componentPermutation⟩ :=
          exists_parityEnvelopeDerivation_of_connected_with_perm
            (supportConnected (endpoint :: tail) (by simp))
            componentLengthAtLeastTwo
      cases rest with
      | nil =>
          refine ⟨endpoint, interior, ?_, ?_⟩
          · simpa using componentDerivation
          · simpa using componentPermutation
      | cons next remaining =>
          obtain
            ⟨restEndpoint, restInterior,
              restDerivation, restPermutation⟩ :=
                ih
                  (by simp)
                  (fun current member =>
                    supportConnected current
                      (List.Mem.tail (endpoint :: tail) member))
                  (fun current member =>
                    lengthAtLeastTwo current
                      (List.Mem.tail (endpoint :: tail) member))
          have normalizeFirst :
              ListDerives
                ((endpoint :: tail) ++
                  (next :: remaining).flatten)
                (parityEnvelopeRender endpoint interior [] ++
                  (next :: remaining).flatten) :=
            ListDerives.append
              componentDerivation (next :: remaining).flatten
          have normalizeRest :
              ListDerives
                (parityEnvelopeRender endpoint interior [] ++
                  (next :: remaining).flatten)
                (parityEnvelopeRender endpoint interior [] ++
                  parityEnvelopeRender
                    restEndpoint restInterior []) :=
            ListDerives.prepend
              (parityEnvelopeRender endpoint interior [])
              restDerivation
          have combine :
              ListDerives
                (parityEnvelopeRender endpoint interior [] ++
                  parityEnvelopeRender
                    restEndpoint restInterior [])
                (parityEnvelopeRender endpoint
                  (interior ++
                    [restEndpoint, restEndpoint] ++
                    restInterior) []) := by
            simpa [parityEnvelopeRender, List.append_assoc] using
              listDerivesAdjacentParityEnvelopeCombine
                endpoint restEndpoint interior restInterior
          have normalizePermutation :
              ((endpoint :: tail) ++
                  (next :: remaining).flatten).Perm
                (parityEnvelopeRender endpoint interior [] ++
                  parityEnvelopeRender
                    restEndpoint restInterior []) :=
            List.Perm.append
              componentPermutation restPermutation
          have combinePermutation :
              (parityEnvelopeRender endpoint interior [] ++
                  parityEnvelopeRender
                    restEndpoint restInterior []).Perm
                (parityEnvelopeRender endpoint
                  (interior ++
                    [restEndpoint, restEndpoint] ++
                    restInterior) []) :=
            adjacentParityEnvelopeCombine_perm
              endpoint restEndpoint interior restInterior
          refine
            ⟨endpoint,
              interior ++
                [restEndpoint, restEndpoint] ++
                restInterior,
              ?_, ?_⟩
          · simpa using
              ListDerives.trans normalizeFirst <|
                ListDerives.trans normalizeRest combine
          · simpa using
              normalizePermutation.trans combinePermutation

/-- A nonempty exact-cut-free gap folds through its deterministic support
components to one closed parity envelope, with exact multiset preservation. -/
theorem exists_parityEnvelopeDerivation_of_no_exactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right)
    (gapNonempty : gap ≠ []) :
    ∃ endpoint finalInterior,
      ListDerives
          gap
          (parityEnvelopeRender endpoint finalInterior []) ∧
        gap.Perm
          (parityEnvelopeRender endpoint finalInterior []) := by
  obtain
    ⟨endpoint, finalInterior, derivation, permutation⟩ :=
      exists_parityEnvelopeDerivation_of_components
        (connectedComponentDecomposeList gap)
        (connectedComponentDecomposeList_nonempty gapNonempty)
        (connectedComponentDecomposeList_supportConnected gap)
        (connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
          noExactCut)
  rw [connectedComponentDecomposeList_flatten gap]
    at derivation permutation
  exact ⟨endpoint, finalInterior, derivation, permutation⟩

end SemigroupBasis.CoRoots.S5_441
