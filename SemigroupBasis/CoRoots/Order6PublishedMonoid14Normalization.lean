import SemigroupBasis.CoRoots.Order6PublishedMonoid14Syntax
import SemigroupBasis.CoRoots.S5_107Syntax
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons
private abbrev renderSquareBank := S5_107.renderMultipleSquares

/-! ## Squaring every globally repeated occurrence -/

theorem listDerivesExpandLeftOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter, letter] ++ middle ++ [letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord <|
            derivesLeftEndpointExpansion
              (Word.singleton letter)
              (listWordOfCons head tail))

theorem listDerivesExpandRightOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter] ++ middle ++ [letter, letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord <|
            derivesRightEndpointExpansion
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Duplicate one selected occurrence when the same letter occurs elsewhere
in the surrounding word. -/
theorem listDerivesDuplicateSelectedOccurrence
    (letter : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [letter] ++ after).count letter) :
    ListDerives
      (before ++ [letter] ++ after)
      (before ++ [letter, letter] ++ after) := by
  by_cases afterMember : letter ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesExpandLeftOccurrence letter middle).context
        before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : letter ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count letter = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count letter = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [letter] ++ after).count letter = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesExpandRightOccurrence letter middle).context
        beforePrefix after
    simpa [split, List.append_assoc] using expanded

private theorem count_le_count_duplicateSelected
    (tested inserted : Nat) (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted] ++ after).count tested := by
  by_cases equality : tested = inserted
  · subst inserted
    simp [List.count_append]
  · have reverseEquality : inserted ≠ tested := Ne.symm equality
    simp [List.count_append, equality, reverseEquality]

/-- Square every occurrence in a repeated-letter gap. -/
theorem listDerivesSquareSegmentAux
    (after : List Nat) :
    ∀ (segment before : List Nat),
      (∀ letter ∈ segment,
        2 ≤ (before ++ segment ++ after).count letter) →
      ListDerives
        (before ++ segment ++ after)
        (before ++ renderSquareBank segment ++ after)
  | [], before, _ => by
      simpa [S5_107.renderMultipleSquares] using
        (S5_107.ListDerives.refl (basis := basis) (before ++ after))
  | letter :: rest, before, multiples => by
      have selectedMultiple :
          2 ≤
            (before ++ [letter] ++ (rest ++ after)).count letter := by
        simpa [List.append_assoc] using
          multiples letter (by simp)
      have firstRaw :=
        listDerivesDuplicateSelectedOccurrence
          letter before (rest ++ after) selectedMultiple
      have firstStep :
          ListDerives
            (before ++ (letter :: rest) ++ after)
            ((before ++ [letter, letter]) ++ rest ++ after) := by
        simpa [List.append_assoc] using firstRaw
      have restMultiples :
          ∀ tested ∈ rest,
            2 ≤
              ((before ++ [letter, letter]) ++ rest ++ after).count
                tested := by
        intro tested member
        have oldMultiple :
            2 ≤
              (before ++ [letter] ++ (rest ++ after)).count tested := by
          simpa [List.append_assoc] using
            multiples tested (List.Mem.tail letter member)
        have monotone :=
          count_le_count_duplicateSelected
            tested letter before (rest ++ after)
        exact Nat.le_trans oldMultiple <| by
          simpa [List.append_assoc] using monotone
      have restStep :=
        listDerivesSquareSegmentAux after rest
          (before ++ [letter, letter]) restMultiples
      exact firstStep.trans <| by
        simpa [S5_107.renderMultipleSquares,
          List.append_assoc] using restStep

/-! ## The Lee--Li square-return chain -/

@[simp]
theorem renderSquareBank_append (left right : List Nat) :
    renderSquareBank (left ++ right) =
      renderSquareBank left ++ renderSquareBank right := by
  induction left with
  | nil => simp [S5_107.renderMultipleSquares]
  | cons letter rest induction =>
      simp [S5_107.renderMultipleSquares, induction,
        List.append_assoc]

private theorem listDerivesSquareReturnOne
    (anchor label : Nat) :
    ListDerives
      ([anchor, anchor] ++ [label, label] ++ [anchor])
      ([anchor, anchor] ++ [label, label]) := by
  simpa [Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSquareReturnContraction
          (Word.singleton anchor) (Word.singleton label)))

private theorem listDerivesSquarePairReturn
    (anchor label : Nat) :
    ListDerives
      ([anchor, anchor] ++ [label, label] ++ [anchor, anchor])
      ([anchor, anchor] ++ [label, label]) := by
  have first :=
    (listDerivesSquareReturnOne anchor label).append [anchor]
  exact first.trans <| by
    simpa [List.append_assoc] using
      listDerivesSquareReturnOne anchor label

private theorem listDerivesSquareBankReturnRev
    (anchor : Nat) :
    ∀ reverseLabels : List Nat,
      ListDerives
        ([anchor, anchor] ++
          renderSquareBank reverseLabels.reverse ++ [anchor, anchor])
        ([anchor, anchor] ++ renderSquareBank reverseLabels.reverse)
  | [] => by
      simpa [S5_107.renderMultipleSquares, Word.singleton,
        Word.append, Word.append_assoc, List.append_assoc] using
          (S5_107.ListDerives.ofWord (basis := basis)
            (derivesFourToTwo (Word.singleton anchor)))
  | label :: rest => by
      have induction := listDerivesSquareBankReturnRev anchor rest
      let front :=
        [anchor, anchor] ++ renderSquareBank rest.reverse
      have insert :=
        induction.symm.append ([label, label] ++ [anchor, anchor])
      have removeMiddle :=
        (listDerivesSquarePairReturn anchor label).prepend front
      have removeFinal := induction.append [label, label]
      have insertStep :
          ListDerives
            (front ++ [label, label] ++ [anchor, anchor])
            (front ++ [anchor, anchor] ++ [label, label] ++
              [anchor, anchor]) := by
        simpa [front, List.append_assoc] using insert
      have removeMiddleStep :
          ListDerives
            (front ++ [anchor, anchor] ++ [label, label] ++
              [anchor, anchor])
            (front ++ [anchor, anchor] ++ [label, label]) := by
        simpa [List.append_assoc] using removeMiddle
      have removeFinalStep :
          ListDerives
            (front ++ [anchor, anchor] ++ [label, label])
            (front ++ [label, label]) := by
        simpa [front, List.append_assoc] using removeFinal
      have combined :=
        insertStep.trans (removeMiddleStep.trans removeFinalStep)
      simpa [front, S5_107.renderMultipleSquares,
        List.append_assoc] using combined

/-- Lee--Li's consequence
`x² y₁² ... yₙ² x² = x² y₁² ... yₙ²`, including `n = 0`. -/
theorem listDerivesSquareBankReturn
    (anchor : Nat) (labels : List Nat) :
    ListDerives
      ([anchor, anchor] ++ renderSquareBank labels ++ [anchor, anchor])
      ([anchor, anchor] ++ renderSquareBank labels) := by
  simpa using listDerivesSquareBankReturnRev anchor labels.reverse

private theorem filterNe_eq_self
    {anchor : Nat} {letters : List Nat}
    (absent : anchor ∉ letters) :
    letters.filter (fun letter => !decide (letter = anchor)) = letters := by
  apply List.filter_eq_self.mpr
  intro letter member
  have different : letter ≠ anchor := by
    intro equal
    subst letter
    exact absent member
  simp [different]

/-- Delete repeated square labels while preserving the first-occurrence order
of the labels. -/
theorem listDerivesCanonicalSquareBank :
    ∀ labels : List Nat,
      ListDerives
        (renderSquareBank labels)
        (renderSquareBank (S5_107.distinctLetters labels))
  | [] => by
      exact S5_107.ListDerives.refl _
  | anchor :: rest => by
      have normalizeTail :=
        (listDerivesCanonicalSquareBank rest).prepend [anchor, anchor]
      let reduced := S5_107.distinctLetters rest
      by_cases present : anchor ∈ reduced
      · obtain ⟨before, after, split⟩ :=
          List.mem_iff_append.mp present
        have reducedNodup : reduced.Nodup := by
          exact S5_107.distinctLetters_nodup rest
        have splitNodup : (before ++ anchor :: after).Nodup := by
          simpa [split] using reducedNodup
        have appendData := List.nodup_append.mp splitNodup
        have beforeAbsent : anchor ∉ before := by
          intro member
          exact appendData.2.2 anchor member anchor (by simp) rfl
        have afterAbsent : anchor ∉ after :=
          (List.nodup_cons.mp appendData.2.1).1
        have beforeFiltered := filterNe_eq_self beforeAbsent
        have afterFiltered := filterNe_eq_self afterAbsent
        have removeRepeated :=
          (listDerivesSquareBankReturn anchor before).append
            (renderSquareBank after)
        have combined := normalizeTail.trans <| by
          simpa [reduced, split, S5_107.renderMultipleSquares,
            List.append_assoc] using removeRepeated
        simpa [S5_107.distinctLetters, reduced, split,
          List.filter_append, beforeFiltered, afterFiltered,
          S5_107.renderMultipleSquares, List.append_assoc,
          List.flatMap_append] using combined
      · have filtered := filterNe_eq_self present
        simpa [S5_107.distinctLetters, reduced, filtered,
          S5_107.renderMultipleSquares, List.append_assoc,
          List.flatMap_append] using normalizeTail

/-! ## Globally simple separator decomposition -/

def renderSeparatorDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => finalGap
  | (gap, separator) :: rest, finalGap =>
      gap ++ separator :: renderSeparatorDecomposition rest finalGap

def renderSquaredSeparatorDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => renderSquareBank finalGap
  | (gap, separator) :: rest, finalGap =>
      renderSquareBank gap ++ separator ::
        renderSquaredSeparatorDecomposition rest finalGap

def renderCanonicalDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap =>
      renderSquareBank (S5_107.distinctLetters finalGap)
  | (gap, separator) :: rest, finalGap =>
      renderSquareBank (S5_107.distinctLetters gap) ++ separator ::
        renderCanonicalDecomposition rest finalGap

theorem separatorDecomposition_source_eq_render
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole source segments finalGap) :
    source = renderSeparatorDecomposition segments finalGap := by
  induction decomposition with
  | final gap _ => rfl
  | step gap separator remainder segments finalGap
      _ _ tail induction =>
      simp [renderSeparatorDecomposition, induction]

private theorem count_renderSquareBank
    (tested : Nat) :
    ∀ letters : List Nat,
      (renderSquareBank letters).count tested =
        2 * letters.count tested
  | [] => by simp [S5_107.renderMultipleSquares]
  | letter :: rest => by
      have induction := count_renderSquareBank tested rest
      change
        ([letter, letter] ++ renderSquareBank rest).count tested =
          2 * (letter :: rest).count tested
      simp only [List.count_append, List.count_cons, List.count_nil]
      by_cases equal : letter = tested
      · subst letter
        rw [induction]
        omega
      · simp only [beq_iff_eq, equal, if_false]
        rw [induction]
        omega

private theorem count_le_renderSquareBank
    (tested : Nat) (letters : List Nat) :
    letters.count tested ≤ (renderSquareBank letters).count tested := by
  rw [count_renderSquareBank]
  omega

private theorem count_render_le_squared_render
    (tested : Nat) :
    ∀ (segments : List (List Nat × Nat)) (finalGap : List Nat),
      (renderSeparatorDecomposition segments finalGap).count tested ≤
        (renderSquaredSeparatorDecomposition segments finalGap).count
          tested
  | [], finalGap => by
      simpa [renderSeparatorDecomposition,
        renderSquaredSeparatorDecomposition] using
          count_le_renderSquareBank tested finalGap
  | (gap, separator) :: rest, finalGap => by
      simp only [renderSeparatorDecomposition,
        renderSquaredSeparatorDecomposition, List.count_append,
        List.count_cons]
      have gapBound := count_le_renderSquareBank tested gap
      have restBound :=
        count_render_le_squared_render tested rest finalGap
      omega

/-- Square every repeated occurrence in a separator decomposition. -/
theorem listDerivesSquareSeparatorDecompositionAux
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole source segments finalGap) :
    ∀ before : List Nat,
      (∀ tested,
        whole.count tested ≤ (before ++ source).count tested) →
      ListDerives
        (before ++ source)
        (before ++
          renderSquaredSeparatorDecomposition segments finalGap) := by
  induction decomposition with
  | final gap gapRepeated =>
      intro before monotone
      have squared :=
        listDerivesSquareSegmentAux [] gap before (by
          intro letter member
          exact Nat.le_trans (gapRepeated letter member) <| by
            simpa using monotone letter)
      simpa [renderSquaredSeparatorDecomposition] using squared
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail induction =>
      intro before monotone
      have gapMultiples :
          ∀ letter ∈ gap,
            2 ≤
              (before ++ gap ++ (separator :: remainder)).count letter := by
        intro letter member
        exact Nat.le_trans (gapRepeated letter member) <| by
          simpa [List.append_assoc] using monotone letter
      have first :=
        listDerivesSquareSegmentAux
          (separator :: remainder) gap before gapMultiples
      let nextBefore :=
        before ++ renderSquareBank gap ++ [separator]
      have nextMonotone :
          ∀ tested,
            whole.count tested ≤
              (nextBefore ++ remainder).count tested := by
        intro tested
        have old := monotone tested
        have gapBound := count_le_renderSquareBank tested gap
        dsimp [nextBefore]
        simp only [List.count_append, List.count_cons,
          List.count_nil] at *
        omega
      have rest := induction nextBefore nextMonotone
      have combined := first.trans <| by
        simpa [nextBefore, List.append_assoc] using rest
      simpa [renderSquaredSeparatorDecomposition,
        List.append_assoc] using combined

theorem listDerivesSquareSeparatorDecomposition
    (whole : List Nat)
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderSquaredSeparatorDecomposition segments finalGap) := by
  simpa using
    listDerivesSquareSeparatorDecompositionAux decomposition [] (by simp)

theorem listDerivesCanonicalizeSquaredDecomposition
    (segments : List (List Nat × Nat))
    (finalGap before : List Nat) :
    ListDerives
      (before ++ renderSquaredSeparatorDecomposition segments finalGap)
      (before ++ renderCanonicalDecomposition segments finalGap) := by
  induction segments generalizing before with
  | nil =>
      simpa [renderSquaredSeparatorDecomposition,
        renderCanonicalDecomposition] using
          (listDerivesCanonicalSquareBank finalGap).prepend before
  | cons factor rest induction =>
      rcases factor with ⟨gap, separator⟩
      have first :=
        (listDerivesCanonicalSquareBank gap).context before
          (separator ::
            renderSquaredSeparatorDecomposition rest finalGap)
      let nextBefore :=
        before ++ renderSquareBank (S5_107.distinctLetters gap) ++
          [separator]
      have tail := induction nextBefore
      have combined := first.trans <| by
        simpa [nextBefore, renderSquaredSeparatorDecomposition,
          renderCanonicalDecomposition,
          List.append_assoc] using tail
      simpa [renderSquaredSeparatorDecomposition,
        renderCanonicalDecomposition,
        List.append_assoc] using combined

/-- Every word list derives to the Proposition 14.1 canonical rendering:
globally simple separators remain in order and every intervening gap is the
square bank of its distinct letters in first-occurrence order. -/
theorem listDerivesCanonicalDecomposition
    (whole : List Nat)
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderCanonicalDecomposition segments finalGap) :=
  (listDerivesSquareSeparatorDecomposition whole decomposition).trans <| by
    simpa using
      listDerivesCanonicalizeSquaredDecomposition segments finalGap []

end SemigroupBasis.CoRoots.Order6PublishedMonoid14
