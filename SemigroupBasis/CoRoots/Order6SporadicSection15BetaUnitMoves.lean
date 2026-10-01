import SemigroupBasis.CoRoots.Order6SporadicSection15BetaMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-! ## Permuting beta units under a repeated nonempty anchor -/

/-- Render a sequence of unit blocks after an initial anchor.  Each unit is
followed by another copy of the same anchor, so
`anchor ++ renderBetaUnitBlocks anchor units` has the shape required by
successive instances of (15.1f). -/
def renderBetaUnitBlocks
    (anchor : List Nat) : List (List Nat) → List Nat
  | [] => []
  | unit :: units =>
      unit ++ anchor ++ renderBetaUnitBlocks anchor units

/-- Transpose two adjacent nonempty unit blocks between repeated copies of
one explicit nonempty anchor block.  The hypotheses are exactly those needed
to instantiate the three nonempty words in (15.1f). -/
theorem listDerivesSwapAdjacentBetaUnitBlocks
    (before after anchor left right : List Nat)
    (anchorNonempty : anchor ≠ [])
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    ListDerives
      (before ++ anchor ++ left ++ anchor ++ right ++ anchor ++ after)
      (before ++ anchor ++ right ++ anchor ++ left ++ anchor ++ after) := by
  rcases List.exists_cons_of_ne_nil anchorNonempty with
    ⟨anchorHead, anchorTail, rfl⟩
  rcases List.exists_cons_of_ne_nil leftNonempty with
    ⟨leftHead, leftTail, rfl⟩
  rcases List.exists_cons_of_ne_nil rightNonempty with
    ⟨rightHead, rightTail, rfl⟩
  simpa [List.append_assoc] using
    (listDerivesSwapSimpleRunUnitsUnderNonemptyAnchor
      before after anchorHead leftHead rightHead
      anchorTail leftTail rightTail)

/-- Every permutation of nonempty unit blocks is derivable when the units are
rendered between repeated copies of one nonempty anchor block.  Nonemptiness
of target blocks is transported through the permutation instead of assumed
separately. -/
theorem listDerivesBetaUnitBlockPermutation
    (anchor : List Nat) (anchorNonempty : anchor ≠ [])
    {source target : List (List Nat)}
    (permutation : source.Perm target) :
    ∀ suffix : List Nat,
      (∀ unit ∈ source, unit ≠ []) →
      ListDerives
        (anchor ++ renderBetaUnitBlocks anchor source ++ suffix)
        (anchor ++ renderBetaUnitBlocks anchor target ++ suffix) := by
  induction permutation with
  | nil =>
      intro suffix _
      simpa [renderBetaUnitBlocks] using
        (S5_107.ListDerives.refl (basis := basis) (anchor ++ suffix))
  | @cons unit source target permutation ih =>
      intro suffix nonempty
      have tailNonempty :
          ∀ candidate ∈ source, candidate ≠ [] := by
        intro candidate member
        exact nonempty candidate
          (List.mem_cons_of_mem unit member)
      have tailStep := ih suffix tailNonempty
      simpa [renderBetaUnitBlocks, List.append_assoc] using
        tailStep.prepend (anchor ++ unit)
  | swap left right rest =>
      intro suffix nonempty
      have leftNonempty : left ≠ [] :=
        nonempty left (by simp)
      have rightNonempty : right ≠ [] :=
        nonempty right (by simp)
      have swapped :=
        listDerivesSwapAdjacentBetaUnitBlocks
          [] (renderBetaUnitBlocks anchor rest ++ suffix)
          anchor left right anchorNonempty leftNonempty rightNonempty
      simpa [renderBetaUnitBlocks, List.append_assoc] using swapped.symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro suffix nonempty
      have middleNonempty :
          ∀ unit ∈ middle, unit ≠ [] := by
        intro unit member
        exact nonempty unit (first.mem_iff.mpr member)
      exact
        (ihFirst suffix nonempty).trans
          (ihSecond suffix middleNonempty)

/-- Contextual form of `listDerivesBetaUnitBlockPermutation`, convenient when
the repeated-anchor segment is embedded in a larger beta word. -/
theorem listDerivesBetaUnitBlockPermutationInContext
    (before after anchor : List Nat) (anchorNonempty : anchor ≠ [])
    {source target : List (List Nat)}
    (permutation : source.Perm target)
    (sourceNonempty : ∀ unit ∈ source, unit ≠ []) :
    ListDerives
      (before ++ anchor ++ renderBetaUnitBlocks anchor source ++ after)
      (before ++ anchor ++ renderBetaUnitBlocks anchor target ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesBetaUnitBlockPermutation
      anchor anchorNonempty permutation after sourceNonempty).prepend before

end SemigroupBasis.CoRoots.Order6SporadicSection15
