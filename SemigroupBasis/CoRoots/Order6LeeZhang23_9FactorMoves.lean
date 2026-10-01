import SemigroupBasis.CoRoots.Order6LeeZhang23_9Moves
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner

/-!
# B4 moves for Lee--Zhang successor factors

This module is the derivational bridge between the pure successor scanner and
the later Proposition 23.12 canonicalizer.  It contains only consequences of
the published four-law basis `B4Basis`: rendered-factor count bookkeeping,
Lemma 23.10 swaps with a nonempty controlled tail, permutations that leave the
last factor fixed, and the local expansions that expose a square before one
selected factor.

No canonical data are chosen here, and no derivation theorem for the fixed
`S5_402` basis is imported or invoked.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9FactorMoves

open SemigroupBasis
open Order6LeeZhang23_9Moves
open Order6LeeZhang23_9Scanner

/-! ## Word and list renderers -/

/-- The nonempty word carried by one marker-followed-by-block factor. -/
def successorFactorWord (factor : SuccessorFactor) : Word Nat :=
  ⟨factor.1, factor.2⟩

@[simp]
theorem successorFactorWord_toList (factor : SuccessorFactor) :
    (successorFactorWord factor).toList =
      renderSuccessorFactor factor := by
  rcases factor with ⟨marker, block⟩
  rfl

@[simp]
theorem successorFactorWord_head (factor : SuccessorFactor) :
    (successorFactorWord factor).head = factor.1 := by
  rcases factor with ⟨marker, block⟩
  rfl

/-- A nonempty controlled suffix consisting of zero or more movable factors
followed by one fixed final factor. -/
def controlledSuccessorTail :
    List SuccessorFactor → SuccessorFactor → Word Nat
  | [], final => successorFactorWord final
  | factor :: rest, final =>
      successorFactorWord factor ++ controlledSuccessorTail rest final

@[simp]
theorem controlledSuccessorTail_toList :
    ∀ (after : List SuccessorFactor) (final : SuccessorFactor),
      (controlledSuccessorTail after final).toList =
        renderSuccessorFactors after ++
          renderSuccessorFactor final
  | [], final => by
      rfl
  | factor :: rest, final => by
      simp [controlledSuccessorTail, renderSuccessorFactors,
        controlledSuccessorTail_toList, List.append_assoc]

@[simp]
theorem controlledSuccessorTail_head_nil
    (final : SuccessorFactor) :
    (controlledSuccessorTail [] final).head = final.1 := by
  simp [controlledSuccessorTail]

@[simp]
theorem controlledSuccessorTail_head_cons
    (factor : SuccessorFactor) (rest : List SuccessorFactor)
    (final : SuccessorFactor) :
    (controlledSuccessorTail (factor :: rest) final).head =
      factor.1 := by
  simp [controlledSuccessorTail]

/-- Rendering respects permutations of whole successor factors. -/
theorem renderSuccessorFactors_perm
    {source target : List SuccessorFactor}
    (permutation : source.Perm target) :
    (renderSuccessorFactors source).Perm
      (renderSuccessorFactors target) := by
  induction permutation with
  | nil =>
      exact List.Perm.nil
  | cons factor _ induction =>
      simpa [renderSuccessorFactors] using
        List.Perm.append
          (List.Perm.refl (renderSuccessorFactor factor)) induction
  | swap left right rest =>
      have swapBlocks :
          (renderSuccessorFactor right ++
              renderSuccessorFactor left).Perm
            (renderSuccessorFactor left ++
              renderSuccessorFactor right) :=
        List.perm_append_comm
      simpa [renderSuccessorFactors, List.append_assoc] using
        swapBlocks.append_right (renderSuccessorFactors rest)
  | trans _ _ first second =>
      exact first.trans second

/-- Permuting whole factors preserves every rendered letter count. -/
theorem renderSuccessorFactors_count_eq
    {source target : List SuccessorFactor}
    (permutation : source.Perm target) (letter : Nat) :
    (renderSuccessorFactors source).count letter =
      (renderSuccessorFactors target).count letter :=
  (List.perm_iff_count.mp
    (renderSuccessorFactors_perm permutation)) letter

/-- Count preservation remains literal in an arbitrary fixed list context. -/
theorem renderedFactorPermutation_count_eq_in_context
    {source target : List SuccessorFactor}
    (permutation : source.Perm target)
    (before after : List Nat) (letter : Nat) :
    (before ++ renderSuccessorFactors source ++ after).count letter =
      (before ++ renderSuccessorFactors target ++ after).count letter := by
  simp only [List.count_append]
  rw [renderSuccessorFactors_count_eq permutation letter]

/-! ## Lemma 23.10 with a fixed final controller -/

/-- Lemma 23.10 specialized to two rendered successor factors in front of
an arbitrary nonempty controller word.  The multiplicity hypotheses refer to
the complete displayed word. -/
theorem derivesAdjacentSuccessorFactorSwap
    (leading controller : Word Nat)
    (left right : SuccessorFactor)
    (leftMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          left.1))
    (rightMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          right.1))
    (controllerMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          controller.head)) :
    Derives B4Basis
      (((leading ++ successorFactorWord left) ++
        successorFactorWord right) ++ controller)
      (((leading ++ successorFactorWord right) ++
        successorFactorWord left) ++ controller) := by
  exact derivesLeeZhang23_10BlockSwap
    leading (successorFactorWord left)
      (successorFactorWord right) controller
      (by simpa using leftMultiple)
      (by simpa using rightMultiple)
      controllerMultiple

/-- Swap two adjacent factors while all later factors and one nonempty final
factor remain fixed.  The final factor makes the Lemma 23.10 controller
nonempty even when `after` is empty. -/
theorem listDerivesAdjacentSuccessorFactorSwapBeforeFinal
    (leading : Word Nat)
    (left right : SuccessorFactor)
    (after : List SuccessorFactor)
    (final : SuccessorFactor)
    (multiples :
      ∀ factor ∈ left :: right :: (after ++ [final]),
        2 ≤
          (leading.toList ++
            renderSuccessorFactors (left :: right :: after) ++
            renderSuccessorFactor final).count factor.1) :
    B4ListDerives
      (leading.toList ++
        renderSuccessorFactors (left :: right :: after) ++
        renderSuccessorFactor final)
      (leading.toList ++
        renderSuccessorFactors (right :: left :: after) ++
        renderSuccessorFactor final) := by
  let controller := controlledSuccessorTail after final
  have leftMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          left.1) := by
    have displayed := multiples left (by simp)
    simpa [controller, Word.toList_append,
      renderSuccessorFactors, List.append_assoc] using displayed
  have rightMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          right.1) := by
    have displayed := multiples right (by simp)
    simpa [controller, Word.toList_append,
      renderSuccessorFactors, List.append_assoc] using displayed
  have controllerMultiple :
      2 ≤
        ((((leading ++ successorFactorWord left) ++
            successorFactorWord right) ++ controller).toList.count
          controller.head) := by
    cases after with
    | nil =>
        have displayed := multiples final (by simp)
        simpa [controller, controlledSuccessorTail,
          Word.toList_append, renderSuccessorFactors,
          List.append_assoc] using displayed
    | cons first rest =>
        have displayed := multiples first (by simp)
        simpa [controller, controlledSuccessorTail,
          Word.toList_append, renderSuccessorFactors,
          List.append_assoc] using displayed
  have swapped :=
    derivesAdjacentSuccessorFactorSwap
      leading controller left right
        leftMultiple rightMultiple controllerMultiple
  simpa [controller, Word.toList_append,
    renderSuccessorFactors, List.append_assoc] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord swapped)

/-- Every permutation of the nonfinal factors is B4-derivable while the
final factor remains literally fixed.  The common multiplicity premise is
transported across transitive permutation steps by rendered count
preservation. -/
theorem listDerivesSuccessorFactorPermutationBeforeFinal
    {source target : List SuccessorFactor}
    (permutation : source.Perm target) :
    ∀ (leading : Word Nat) (final : SuccessorFactor),
      (∀ factor ∈ source ++ [final],
        2 ≤
          (leading.toList ++
            renderSuccessorFactors source ++
            renderSuccessorFactor final).count factor.1) →
      B4ListDerives
        (leading.toList ++
          renderSuccessorFactors source ++
          renderSuccessorFactor final)
        (leading.toList ++
          renderSuccessorFactors target ++
          renderSuccessorFactor final) := by
  induction permutation with
  | nil =>
      intro leading final _
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | @cons first source target permutation induction =>
      intro leading final multiples
      have tailMultiples :
          ∀ factor ∈ source ++ [final],
            2 ≤
              ((leading ++ successorFactorWord first).toList ++
                renderSuccessorFactors source ++
                renderSuccessorFactor final).count factor.1 := by
        intro factor member
        have displayed :=
          multiples factor <| by
            simpa using List.mem_cons_of_mem first member
        simpa [Word.toList_append, renderSuccessorFactors,
          List.append_assoc] using displayed
      have tailStep :=
        induction
          (leading ++ successorFactorWord first) final
          tailMultiples
      simpa [Word.toList_append, renderSuccessorFactors,
        List.append_assoc] using tailStep
  | swap left right rest =>
      intro leading final multiples
      exact
        listDerivesAdjacentSuccessorFactorSwapBeforeFinal
          leading right left rest final multiples
  | @trans source middle target first second
      inductionFirst inductionSecond =>
      intro leading final multiples
      have firstStep := inductionFirst leading final multiples
      have middleMultiples :
          ∀ factor ∈ middle ++ [final],
            2 ≤
              (leading.toList ++
                renderSuccessorFactors middle ++
                renderSuccessorFactor final).count factor.1 := by
        intro factor member
        have sourceMember : factor ∈ source ++ [final] := by
          simp only [List.mem_append, List.mem_singleton] at member ⊢
          rcases member with middleMember | finalEq
          · exact Or.inl (first.mem_iff.mpr middleMember)
          · exact Or.inr finalEq
        have sourceMultiple := multiples factor sourceMember
        have countEquality :=
          renderedFactorPermutation_count_eq_in_context
            first leading.toList
              (renderSuccessorFactor final) factor.1
        rw [← countEquality]
        exact sourceMultiple
      exact firstStep.trans
        (inductionSecond leading final middleMultiples)

/-! ## Selected-factor square exposure -/

/-- Duplicate the selected marker at the head of one rendered factor.  This
is the marker-only expansion used when no residual block is retained. -/
theorem listDerivesSquareSuccessorFactorMarker
    (before block after : List Nat) (marker : Nat)
    (multiple :
      2 ≤
        (before ++ renderSuccessorFactor (marker, block) ++ after).count
          marker) :
    B4ListDerives
      (before ++ renderSuccessorFactor (marker, block) ++ after)
      (before ++ [marker, marker] ++ block ++ after) := by
  have explicitMultiple :
      2 ≤ (before ++ [marker] ++ (block ++ after)).count marker := by
    simpa [renderSuccessorFactor, List.append_assoc] using multiple
  have expanded :=
    listDerivesDuplicateSelectedOccurrence
      marker before (block ++ after) explicitMultiple
  simpa [renderSuccessorFactor, List.append_assoc] using expanded

/-- Render the square exposed before a residual copy of one factor. -/
def renderSquareAndResidualFactor
    (factor : SuccessorFactor) : List Nat :=
  [factor.1, factor.1] ++ renderSuccessorFactor factor

@[simp]
theorem renderSquareAndResidualFactor_mk
    (marker : Nat) (block : List Nat) :
    renderSquareAndResidualFactor (marker, block) =
      [marker, marker, marker] ++ block := by
  simp [renderSquareAndResidualFactor, renderSuccessorFactor]

/-- Split a selected factor `xw` into a displayed square and the residual
factor `xw`.  The first step uses global repeatedness; the second is the
reverse of the B4 power contraction `x^3 = x^2`. -/
theorem listDerivesSplitSuccessorFactor
    (before block after : List Nat) (marker : Nat)
    (multiple :
      2 ≤
        (before ++ renderSuccessorFactor (marker, block) ++ after).count
          marker) :
    B4ListDerives
      (before ++ renderSuccessorFactor (marker, block) ++ after)
      (before ++
        renderSquareAndResidualFactor (marker, block) ++ after) := by
  have firstStep :=
    listDerivesSquareSuccessorFactorMarker
      before block after marker multiple
  have powerRaw :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesPowerContraction (Word.singleton marker)).symm).context
        before (block ++ after)
  have powerStep :
      B4ListDerives
        (before ++ [marker, marker] ++ block ++ after)
        (before ++ [marker, marker, marker] ++ block ++ after) := by
    simpa [Word.singleton, Word.append,
      List.append_assoc] using powerRaw
  have residualStep :
      B4ListDerives
        (before ++ [marker, marker] ++ block ++ after)
        (before ++
          renderSquareAndResidualFactor (marker, block) ++ after) := by
    simpa [renderSquareAndResidualFactor,
      renderSuccessorFactor, List.append_assoc] using powerStep
  exact firstStep.trans residualStep

end SemigroupBasis.CoRoots.Order6LeeZhang23_9FactorMoves
