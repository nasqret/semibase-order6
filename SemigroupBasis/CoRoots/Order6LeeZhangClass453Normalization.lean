import SemigroupBasis.CoRoots.Order6LeeZhangClass453
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass453

open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop :=
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

/-! ## Canonical square banks -/

theorem listDerivesSquareBlockCommutation
    (left right : Nat) :
    ListDerives
      (renderSquareBank [left, right])
      (renderSquareBank [right, left]) := by
  simpa [S5_107.renderMultipleSquares, List.append_assoc] using
    (S5_107.ListDerives.ofWord <|
      derivesSquareBlockCommutation
        (Word.singleton left) (Word.singleton right))

theorem listDerivesSquareBankPermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives (renderSquareBank source) (renderSquareBank target) := by
  induction permutation with
  | nil => exact .empty
  | cons letter _ induction =>
      simpa [S5_107.renderMultipleSquares] using
        induction.prepend [letter, letter]
  | swap left right rest =>
      have swapped := listDerivesSquareBlockCommutation left right
      simpa [S5_107.renderMultipleSquares] using
        (swapped.append (renderSquareBank rest)).symm
  | trans _ _ first second => exact first.trans second

private theorem listDerivesRemoveRepeatedSquare (anchor : Nat) :
    ∀ labels : List Nat,
      ListDerives
        (renderSquareBank (anchor :: labels))
        (renderSquareBank
          (anchor ::
            labels.filter (fun label => decide (label ≠ anchor))))
  | [] => S5_107.ListDerives.refl _
  | label :: labels => by
      by_cases equal : label = anchor
      · subst label
        have contract :=
          (S5_107.ListDerives.ofWord <|
            derivesFourToTwo (Word.singleton anchor)).append
              (renderSquareBank labels)
        have contractStep :
            ListDerives
              (renderSquareBank (anchor :: anchor :: labels))
              (renderSquareBank (anchor :: labels)) := by
          simpa [S5_107.renderMultipleSquares, Word.toList,
            Word.singleton, Word.append, List.append_assoc] using contract
        simpa [S5_107.renderMultipleSquares] using
          contractStep.trans
            (listDerivesRemoveRepeatedSquare anchor labels)
      · have commuteFront :
            ListDerives
              (renderSquareBank (anchor :: label :: labels))
              (renderSquareBank (label :: anchor :: labels)) := by
          simpa [S5_107.renderMultipleSquares,
            List.append_assoc] using
            (listDerivesSquareBlockCommutation anchor label).append
              (renderSquareBank labels)
        have removeTail :
            ListDerives
              (renderSquareBank (label :: anchor :: labels))
              (renderSquareBank
                (label :: anchor ::
                  labels.filter
                    (fun next => decide (next ≠ anchor)))) := by
          simpa [S5_107.renderMultipleSquares] using
            (listDerivesRemoveRepeatedSquare anchor labels).prepend
              [label, label]
        have commuteBack :
            ListDerives
              (renderSquareBank
                (label :: anchor ::
                  labels.filter
                    (fun next => decide (next ≠ anchor))))
              (renderSquareBank
                (anchor :: label ::
                  labels.filter
                    (fun next => decide (next ≠ anchor)))) := by
          simpa [S5_107.renderMultipleSquares,
            List.append_assoc] using
            (listDerivesSquareBlockCommutation label anchor).append
              (renderSquareBank
                (labels.filter
                  (fun next => decide (next ≠ anchor))))
        simpa [S5_107.renderMultipleSquares, equal] using
          commuteFront.trans (removeTail.trans commuteBack)

theorem listDerivesSquareBankDedup :
    ∀ labels : List Nat,
      ListDerives
        (renderSquareBank labels)
        (renderSquareBank (S5_107.distinctLetters labels))
  | [] => S5_107.ListDerives.empty
  | label :: labels => by
      have dedupTail :
          ListDerives
            (renderSquareBank (label :: labels))
            (renderSquareBank
              (label :: S5_107.distinctLetters labels)) := by
        simpa [S5_107.renderMultipleSquares] using
          (listDerivesSquareBankDedup labels).prepend [label, label]
      exact dedupTail.trans <|
        listDerivesRemoveRepeatedSquare
          label (S5_107.distinctLetters labels)

def sortedDistinctLetters (letters : List Nat) : List Nat :=
  (S5_107.distinctLetters letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

def canonicalGap (gap : List Nat) : List Nat :=
  renderSquareBank (sortedDistinctLetters gap)

theorem sortedDistinctLetters_perm (letters : List Nat) :
    (sortedDistinctLetters letters).Perm
      (S5_107.distinctLetters letters) :=
  List.mergeSort_perm _ _

theorem sortedDistinctLetters_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedDistinctLetters letters ↔ letter ∈ letters := by
  constructor
  · intro member
    have distinctMember : letter ∈ S5_107.distinctLetters letters :=
      (sortedDistinctLetters_perm letters).mem_iff.mp member
    exact (S5_107.distinctLetters_mem_iff letter letters).mp
      distinctMember
  · intro member
    have distinctMember : letter ∈ S5_107.distinctLetters letters :=
      (S5_107.distinctLetters_mem_iff letter letters).mpr member
    exact (sortedDistinctLetters_perm letters).mem_iff.mpr
      distinctMember

theorem sortedDistinctLetters_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    sortedDistinctLetters letters ≠ [] := by
  obtain ⟨letter, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  intro empty
  have listed := (sortedDistinctLetters_mem_iff letter letters).2 member
  rw [empty] at listed
  simp at listed

/-- Sort and deduplicate an already squared bank. -/
theorem listDerivesCanonicalSquareBank (labels : List Nat) :
    ListDerives (renderSquareBank labels) (canonicalGap labels) := by
  exact (listDerivesSquareBankDedup labels).trans <| by
    simpa [canonicalGap] using
      listDerivesSquareBankPermutation
        (sortedDistinctLetters_perm labels).symm

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

def renderOwnCanonicalDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => canonicalGap finalGap
  | (gap, separator) :: rest, finalGap =>
      canonicalGap gap ++ separator ::
        renderOwnCanonicalDecomposition rest finalGap

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

theorem listDerivesOwnCanonicalizeSquaredDecomposition
    (segments : List (List Nat × Nat))
    (finalGap before : List Nat) :
    ListDerives
      (before ++ renderSquaredSeparatorDecomposition segments finalGap)
      (before ++ renderOwnCanonicalDecomposition segments finalGap) := by
  induction segments generalizing before with
  | nil =>
      simpa [renderSquaredSeparatorDecomposition,
        renderOwnCanonicalDecomposition] using
          (listDerivesCanonicalSquareBank finalGap).prepend before
  | cons factor rest induction =>
      rcases factor with ⟨gap, separator⟩
      have first :=
        (listDerivesCanonicalSquareBank gap).context before
          (separator ::
            renderSquaredSeparatorDecomposition rest finalGap)
      let nextBefore := before ++ canonicalGap gap ++ [separator]
      have tail := induction nextBefore
      have combined := first.trans <| by
        simpa [nextBefore, renderSquaredSeparatorDecomposition,
          renderOwnCanonicalDecomposition,
          List.append_assoc] using tail
      simpa [renderSquaredSeparatorDecomposition,
        renderOwnCanonicalDecomposition,
        List.append_assoc] using combined

theorem listDerivesOwnCanonicalDecomposition
    (whole : List Nat)
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderOwnCanonicalDecomposition segments finalGap) :=
  (listDerivesSquareSeparatorDecomposition whole decomposition).trans <| by
    simpa using
      listDerivesOwnCanonicalizeSquaredDecomposition
        segments finalGap []

/-! ## Lee--Zhang cumulative-bank propagation -/

/-- A previous square can be copied across arbitrary intervening material
into a nonempty following square bank. -/
theorem listDerivesPropagateSquare
    (letter carrier : Nat) (middle suffix : List Nat) :
    ListDerives
      ([letter, letter] ++ middle ++ [carrier, carrier] ++ suffix)
      ([letter, letter] ++ middle ++
        [letter, letter, carrier, carrier] ++ suffix) := by
  have expand :=
    (S5_107.ListDerives.ofWord <|
      derivesPowerExpansion (Word.singleton letter)).context []
        (middle ++ [carrier, carrier] ++ suffix)
  have moveCore :=
    S5_107.ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton letter)
        (listWordOfCons letter middle)
        (Word.singleton carrier)
  have move := moveCore.append suffix
  have duplicateCore :=
    S5_107.ListDerives.ofWord <|
      derivesRightEndpointExpansion
        (Word.singleton letter)
        (listWordOfCons letter (middle ++ [carrier, carrier]))
  have duplicate := duplicateCore.append suffix
  have commute :=
    (listDerivesSquareBlockCommutation carrier letter).context
      ([letter, letter] ++ middle) suffix
  have first :
      ListDerives
        ([letter, letter] ++ middle ++ [carrier, carrier] ++ suffix)
        ([letter, letter, letter] ++ middle ++
          [carrier, carrier] ++ suffix) := by
    simpa [List.append_assoc] using expand
  have second :
      ListDerives
        ([letter, letter, letter] ++ middle ++
          [carrier, carrier] ++ suffix)
        ([letter, letter] ++ middle ++
          [carrier, carrier, letter] ++ suffix) := by
    simpa [listWordOfCons, Word.singleton, Word.append,
      List.append_assoc] using move
  have third :
      ListDerives
        ([letter, letter] ++ middle ++
          [carrier, carrier, letter] ++ suffix)
        ([letter, letter] ++ middle ++
          [carrier, carrier, letter, letter] ++ suffix) := by
    simpa [listWordOfCons, S5_107.listWordOfCons, Word.toList,
      Word.singleton, Word.append,
      List.append_assoc] using duplicate
  have fourth :
      ListDerives
        ([letter, letter] ++ middle ++
          [carrier, carrier, letter, letter] ++ suffix)
        ([letter, letter] ++ middle ++
          [letter, letter, carrier, carrier] ++ suffix) := by
    simpa [S5_107.renderMultipleSquares,
      List.append_assoc] using commute
  exact first.trans (second.trans (third.trans fourth))

/-- Copy every label of a preceding bank into a nonempty following bank,
leaving the preceding bank literal. -/
theorem listDerivesPropagateSquareBank
    (middle : List Nat) :
    ∀ (labels current : List Nat), current ≠ [] →
      ListDerives
        (renderSquareBank labels ++ middle ++ renderSquareBank current)
        (renderSquareBank labels ++ middle ++
          renderSquareBank (labels ++ current))
  | [], current, _ => by
      simpa [S5_107.renderMultipleSquares] using
        (S5_107.ListDerives.refl (basis := basis)
          (middle ++ renderSquareBank current))
  | letter :: labels, current, currentNonempty => by
      have tailStep :=
        (listDerivesPropagateSquareBank middle labels current
          currentNonempty).prepend [letter, letter]
      have insertedNonempty : labels ++ current ≠ [] := by
        simp [currentNonempty]
      obtain ⟨carrier, suffix, insertedShape⟩ :=
        List.exists_cons_of_ne_nil insertedNonempty
      have headStep :=
        listDerivesPropagateSquare letter carrier
          (renderSquareBank labels ++ middle)
          (renderSquareBank suffix)
      have combined := tailStep.trans <| by
        rw [insertedShape]
        simpa [S5_107.renderMultipleSquares,
          List.append_assoc] using headStep
      simpa [S5_107.renderMultipleSquares, insertedShape,
        List.append_assoc] using combined

def nextBankLabels (seen gap : List Nat) : List Nat :=
  sortedDistinctLetters (seen ++ sortedDistinctLetters gap)

/-- Propagate the cumulative bank into one nonempty raw gap and then sort
and deduplicate the enlarged bank. -/
theorem listDerivesUpdateBank
    (seen middle gap : List Nat) (gapNonempty : gap ≠ []) :
    ListDerives
      (renderSquareBank seen ++ middle ++ canonicalGap gap)
      (renderSquareBank seen ++ middle ++
        renderSquareBank (nextBankLabels seen gap)) := by
  have ownNonempty : sortedDistinctLetters gap ≠ [] :=
    sortedDistinctLetters_ne_nil gapNonempty
  have propagated :=
    listDerivesPropagateSquareBank middle seen
      (sortedDistinctLetters gap) ownNonempty
  have normalized :=
    (listDerivesCanonicalSquareBank
      (seen ++ sortedDistinctLetters gap)).prepend
        (renderSquareBank seen ++ middle)
  exact propagated.trans <| by
    simpa [canonicalGap, nextBankLabels,
      List.append_assoc] using normalized

/-- Canonical render with nested cumulative square-bank supports. Empty gaps
remain empty, which is precisely the retained simple-adjacency data. -/
def renderCumulativeDecomposition (seen : List Nat) :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap =>
      if finalGap = [] then []
      else renderSquareBank (nextBankLabels seen finalGap)
  | (gap, separator) :: rest, finalGap =>
      if gap = [] then
        separator :: renderCumulativeDecomposition seen rest finalGap
      else
        let next := nextBankLabels seen gap
        renderSquareBank next ++
          separator :: renderCumulativeDecomposition next rest finalGap

private theorem listDerivesCumulativeDecompositionAux
    (finalGap : List Nat) :
    ∀ (segments : List (List Nat × Nat))
      (seen between : List Nat),
      ListDerives
        (renderSquareBank seen ++ between ++
          renderOwnCanonicalDecomposition segments finalGap)
        (renderSquareBank seen ++ between ++
          renderCumulativeDecomposition seen segments finalGap)
  | [], seen, between => by
      by_cases finalEmpty : finalGap = []
      · subst finalGap
        simpa [renderOwnCanonicalDecomposition,
          renderCumulativeDecomposition, canonicalGap,
          sortedDistinctLetters, S5_107.distinctLetters,
          S5_107.renderMultipleSquares] using
            (S5_107.ListDerives.refl (basis := basis)
              (renderSquareBank seen ++ between))
      · simpa [renderOwnCanonicalDecomposition,
          renderCumulativeDecomposition, finalEmpty] using
          listDerivesUpdateBank seen between finalGap finalEmpty
  | (gap, separator) :: rest, seen, between => by
      by_cases gapEmpty : gap = []
      · subst gap
        have tail :=
          listDerivesCumulativeDecompositionAux finalGap rest seen
            (between ++ [separator])
        simpa [renderOwnCanonicalDecomposition,
          renderCumulativeDecomposition, canonicalGap,
          sortedDistinctLetters, S5_107.distinctLetters,
          S5_107.renderMultipleSquares,
          List.append_assoc] using tail
      · let next := nextBankLabels seen gap
        have first :=
          (listDerivesUpdateBank seen between gap gapEmpty).append
            (separator ::
              renderOwnCanonicalDecomposition rest finalGap)
        have tailCore :=
          listDerivesCumulativeDecompositionAux finalGap rest next
            [separator]
        have tail := tailCore.prepend
          (renderSquareBank seen ++ between)
        have combined := first.trans <| by
          simpa [next, List.append_assoc] using tail
        simpa [renderOwnCanonicalDecomposition,
          renderCumulativeDecomposition, gapEmpty, next,
          List.append_assoc] using combined

/-- Every word derives to the unrestricted Lee--Zhang Condition-10 normal
form: ordered globally simple separators and nested sorted square banks. -/
theorem listDerivesCumulativeDecomposition
    (whole : List Nat)
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderCumulativeDecomposition [] segments finalGap) := by
  have own := listDerivesOwnCanonicalDecomposition whole decomposition
  have cumulative :=
    listDerivesCumulativeDecompositionAux finalGap segments [] []
  exact own.trans <| by
    simpa [S5_107.renderMultipleSquares] using cumulative

end SemigroupBasis.CoRoots.Order6LeeZhangClass453
