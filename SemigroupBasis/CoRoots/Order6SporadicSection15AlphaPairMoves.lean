import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

/-! ## Paired-label transpositions for the alpha branch

This file packages one local consequence of (15.1b): two adjacent paired
labels may be transposed while the three displayed gaps stay in their
original positions.  The renderer below records those positions explicitly.
Nothing here pairs arbitrary occurrences or proves alpha normalization.
-/

/-- Transpose two adjacent paired labels while preserving the three list
gaps between their four displayed occurrences and arbitrary outer context.

The derivation is the four-step chain
`x x y y -> x y x y -> x y y x -> y x y x -> y y x x`, with the
same `h`, `k`, and `t` inserted between consecutive displayed letters. -/
theorem listDerivesSwapAdjacentAlphaPairs
    (before after h k t : List Nat) (x y : Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [y] ++ t ++ [y] ++ after)
      (before ++ [y] ++ h ++ [y] ++ k ++ [x] ++ t ++ [x] ++ after) := by
  have exposeAlternating :=
    (listDerives15_1bMiddleSwap before after x y h k t).symm
  have closeRight :=
    listDerives15_1bRightSwap before after x y h k t
  have rotateAlternating :=
    (listDerives15_1bLeftSwap before after y x h k t).symm
  have closeLeft :=
    listDerives15_1bMiddleSwap before after y x h k t
  exact exposeAlternating.trans
    (closeRight.trans (rotateAlternating.trans closeLeft))

namespace AlphaPairMoves

/-- Render paired labels against fixed positional slots.  Each slot contains
the gap inside one pair and the gap following that pair.  The final following
gap is retained, so outer material can be represented without a special last
case.

The renderer deliberately stops when either list is exhausted.  The public
permutation theorem requires equal lengths, which is the honest well-formed
contract for this total helper. -/
def renderPairedLabels :
    List Nat -> List (List Nat × List Nat) -> List Nat
  | label :: labels, (inside, trailing) :: slots =>
      [label] ++ inside ++ [label] ++ trailing ++
        renderPairedLabels labels slots
  | _, _ => []

/-- The direct pair transposition expressed through `renderPairedLabels`.
Only the first two labels move; both slot records and the remaining rendering
are unchanged. -/
theorem listDerivesSwapRenderedHeadAlphaPairs
    (before after : List Nat) (x y : Nat)
    (h k t u : List Nat) (labels : List Nat)
    (slots : List (List Nat × List Nat)) :
    ListDerives
      (before ++ renderPairedLabels
        (x :: y :: labels) ((h, k) :: (t, u) :: slots) ++ after)
      (before ++ renderPairedLabels
        (y :: x :: labels) ((h, k) :: (t, u) :: slots) ++ after) := by
  simpa [renderPairedLabels, List.append_assoc] using
    listDerivesSwapAdjacentAlphaPairs
      before (u ++ renderPairedLabels labels slots ++ after)
      h k t x y

/-- A permutation of paired labels is derivable while the positional slot
list remains fixed.  Equal lengths prevent the total renderer's truncating
fallback from hiding an unmatched label or slot.

This is only a permutation closure for an already paired rendering.  It does
not derive such a rendering from an arbitrary alpha word. -/
theorem listDerivesPermuteRenderedAlphaPairs
    (before after : List Nat) (slots : List (List Nat × List Nat))
    {source target : List Nat}
    (balanced : slots.length = source.length)
    (permutation : source.Perm target) :
    ListDerives
      (before ++ renderPairedLabels source slots ++ after)
      (before ++ renderPairedLabels target slots ++ after) := by
  induction permutation generalizing before slots with
  | nil =>
      have slotsEmpty : slots = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst slots
      exact S5_107.ListDerives.refl _
  | @cons head source target permutation induction =>
      cases slots with
      | nil =>
          simp at balanced
      | cons slot slots =>
          rcases slot with ⟨inside, trailing⟩
          have tailBalanced : slots.length = source.length := by
            simpa using balanced
          have tailDerivation :=
            induction
              (before ++ [head] ++ inside ++ [head] ++ trailing)
              slots tailBalanced
          simpa [renderPairedLabels, List.append_assoc] using tailDerivation
  | swap first second rest =>
      cases slots with
      | nil =>
          simp at balanced
      | cons firstSlot remainingSlots =>
          cases remainingSlots with
          | nil =>
              simp at balanced
          | cons secondSlot restSlots =>
              rcases firstSlot with ⟨firstInside, firstTrailing⟩
              rcases secondSlot with ⟨secondInside, secondTrailing⟩
              exact listDerivesSwapRenderedHeadAlphaPairs
                before after second first
                firstInside firstTrailing secondInside secondTrailing
                rest restSlots
  | @trans source middle target firstPermutation secondPermutation
      firstInduction secondInduction =>
      have firstDerivation := firstInduction before slots balanced
      have middleBalanced : slots.length = middle.length :=
        balanced.trans firstPermutation.length_eq
      exact firstDerivation.trans
        (secondInduction before slots middleBalanced)

end AlphaPairMoves

end SemigroupBasis.CoRoots.Order6SporadicSection15
