import SemigroupBasis.CoRoots.S5_254PairExtraction
import SemigroupBasis.CoRoots.S6_3944Core

namespace SemigroupBasis.CoRoots.S6_3944

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons

/-! ## Squaring selected globally repeated occurrences -/

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
            derivesLeftDuplication
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
            derivesRightDuplication
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Duplicate one selected occurrence when the same letter occurs somewhere
else in the surrounding word. -/
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

/-- Square every occurrence of a selected segment while retaining arbitrary
left and right contexts. The multiplicity hypothesis is updated after each
duplication, so the second witness may lie in an already processed segment. -/
theorem listDerivesSquareSegmentAux
    (after : List Nat) :
    ∀ (segment before : List Nat),
      (∀ letter ∈ segment,
        2 ≤ (before ++ segment ++ after).count letter) →
      ListDerives
        (before ++ segment ++ after)
        (before ++ S5_107.renderMultipleSquares segment ++ after)
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

/-! ## Canonical square blocks -/

theorem listDerivesSquareBlockCommutation
    (left right : Nat) :
    ListDerives
      (S5_107.renderMultipleSquares [left, right])
      (S5_107.renderMultipleSquares [right, left]) := by
  simpa [S5_107.renderMultipleSquares, List.append_assoc] using
    (S5_107.ListDerives.ofWord <|
      derivesSquareBlockCommutation
        (Word.singleton left) (Word.singleton right))

theorem listDerivesMultipleSquarePermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives
      (S5_107.renderMultipleSquares source)
      (S5_107.renderMultipleSquares target) := by
  induction permutation with
  | nil => exact .empty
  | cons letter _ induction =>
      simpa [S5_107.renderMultipleSquares] using
        induction.prepend [letter, letter]
  | swap left right rest =>
      have swapped := listDerivesSquareBlockCommutation left right
      simpa [S5_107.renderMultipleSquares] using
        (swapped.append
          (S5_107.renderMultipleSquares rest)).symm
  | trans _ _ first second => exact first.trans second

private theorem listDerivesRemoveRepeatedSquare (anchor : Nat) :
    ∀ labels : List Nat,
      ListDerives
        (S5_107.renderMultipleSquares (anchor :: labels))
        (S5_107.renderMultipleSquares
          (anchor ::
            labels.filter (fun label => decide (label ≠ anchor))))
  | [] => S5_107.ListDerives.refl _
  | label :: labels => by
      by_cases equal : label = anchor
      · subst label
        have contract :=
          (S5_107.ListDerives.ofWord <|
            derivesFourToTwo (Word.singleton anchor)).append
              (S5_107.renderMultipleSquares labels)
        have contractStep :
            ListDerives
              (S5_107.renderMultipleSquares
                (anchor :: anchor :: labels))
              (S5_107.renderMultipleSquares (anchor :: labels)) := by
          simpa [S5_107.renderMultipleSquares, Word.toList,
            Word.singleton, Word.append, List.append_assoc] using
            contract
        simpa [S5_107.renderMultipleSquares] using
          contractStep.trans
            (listDerivesRemoveRepeatedSquare anchor labels)
      · have commuteFront :
            ListDerives
              (S5_107.renderMultipleSquares
                (anchor :: label :: labels))
              (S5_107.renderMultipleSquares
                (label :: anchor :: labels)) := by
          simpa [S5_107.renderMultipleSquares,
            List.append_assoc] using
            (listDerivesSquareBlockCommutation anchor label).append
              (S5_107.renderMultipleSquares labels)
        have removeTail :
            ListDerives
              (S5_107.renderMultipleSquares
                (label :: anchor :: labels))
              (S5_107.renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next => decide (next ≠ anchor)))) := by
          simpa [S5_107.renderMultipleSquares] using
            (listDerivesRemoveRepeatedSquare anchor labels).prepend
              [label, label]
        have commuteBack :
            ListDerives
              (S5_107.renderMultipleSquares
                (label :: anchor ::
                  labels.filter
                    (fun next => decide (next ≠ anchor))))
              (S5_107.renderMultipleSquares
                (anchor :: label ::
                  labels.filter
                    (fun next => decide (next ≠ anchor)))) := by
          simpa [S5_107.renderMultipleSquares,
            List.append_assoc] using
            (listDerivesSquareBlockCommutation label anchor).append
              (S5_107.renderMultipleSquares
                (labels.filter
                  (fun next => decide (next ≠ anchor))))
        simpa [S5_107.renderMultipleSquares, equal] using
          commuteFront.trans (removeTail.trans commuteBack)

theorem listDerivesMultipleSquareDedup :
    ∀ labels : List Nat,
      ListDerives
        (S5_107.renderMultipleSquares labels)
        (S5_107.renderMultipleSquares
          (S5_107.distinctLetters labels))
  | [] => S5_107.ListDerives.empty
  | label :: labels => by
      have dedupTail :
          ListDerives
            (S5_107.renderMultipleSquares (label :: labels))
            (S5_107.renderMultipleSquares
              (label :: S5_107.distinctLetters labels)) := by
        simpa [S5_107.renderMultipleSquares] using
          (listDerivesMultipleSquareDedup labels).prepend
            [label, label]
      exact dedupTail.trans <|
        listDerivesRemoveRepeatedSquare
          label (S5_107.distinctLetters labels)

def sortedDistinctLetters (letters : List Nat) : List Nat :=
  (S5_107.distinctLetters letters).mergeSort
    (fun left right : Nat => decide (left ≤ right))

def canonicalGap (gap : List Nat) : List Nat :=
  S5_107.renderMultipleSquares (sortedDistinctLetters gap)

theorem sortedDistinctLetters_perm (letters : List Nat) :
    (sortedDistinctLetters letters).Perm
      (S5_107.distinctLetters letters) :=
  List.mergeSort_perm _ _

theorem sortedDistinctLetters_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedDistinctLetters letters ↔ letter ∈ letters := by
  constructor
  · intro member
    have distinctMember :
        letter ∈ S5_107.distinctLetters letters :=
      (sortedDistinctLetters_perm letters).mem_iff.mp member
    exact (S5_107.distinctLetters_mem_iff letter letters).mp
      distinctMember
  · intro member
    have distinctMember :
        letter ∈ S5_107.distinctLetters letters :=
      (S5_107.distinctLetters_mem_iff letter letters).mpr member
    exact (sortedDistinctLetters_perm letters).mem_iff.mpr
      distinctMember

/-- Once every occurrence in a gap has been squared, square commutation and
power contraction reduce it to the sorted distinct support. -/
theorem listDerivesCanonicalGap (gap : List Nat) :
    ListDerives (S5_107.renderMultipleSquares gap) (canonicalGap gap) := by
  exact (listDerivesMultipleSquareDedup gap).trans <| by
    simpa [canonicalGap] using
      listDerivesMultipleSquarePermutation
        (sortedDistinctLetters_perm gap).symm

/-! ## Rendering globally simple separator decompositions -/

def renderSeparatorDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => finalGap
  | (gap, separator) :: rest, finalGap =>
      gap ++ separator ::
        renderSeparatorDecomposition rest finalGap

def renderSquaredSeparatorDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => S5_107.renderMultipleSquares finalGap
  | (gap, separator) :: rest, finalGap =>
      S5_107.renderMultipleSquares gap ++ separator ::
        renderSquaredSeparatorDecomposition rest finalGap

def renderCanonicalSeparatorDecomposition :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => canonicalGap finalGap
  | (gap, separator) :: rest, finalGap =>
      canonicalGap gap ++ separator ::
        renderCanonicalSeparatorDecomposition rest finalGap

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

private theorem count_renderMultipleSquares
    (tested : Nat) :
    ∀ letters : List Nat,
      (S5_107.renderMultipleSquares letters).count tested =
        2 * letters.count tested
  | [] => by simp [S5_107.renderMultipleSquares]
  | letter :: rest => by
      have induction := count_renderMultipleSquares tested rest
      change
        ([letter, letter] ++
            S5_107.renderMultipleSquares rest).count tested =
          2 * (letter :: rest).count tested
      simp only [List.count_append, List.count_cons, List.count_nil]
      by_cases equal : letter = tested
      · subst letter
        rw [induction]
        omega
      · simp only [beq_iff_eq, equal, if_false]
        rw [induction]
        omega

private theorem count_le_renderMultipleSquares
    (tested : Nat) (letters : List Nat) :
    letters.count tested ≤
      (S5_107.renderMultipleSquares letters).count tested := by
  rw [count_renderMultipleSquares]
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
          count_le_renderMultipleSquares tested finalGap
  | (gap, separator) :: rest, finalGap => by
      simp only [renderSeparatorDecomposition,
        renderSquaredSeparatorDecomposition, List.count_append,
        List.count_cons]
      have gapBound := count_le_renderMultipleSquares tested gap
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
      have sourceShape :
          gap ++ separator :: remainder =
            renderSeparatorDecomposition
              ((gap, separator) :: segments) finalGap :=
        separatorDecomposition_source_eq_render
          (.step gap separator remainder segments finalGap
            separatorSimple gapRepeated tail)
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
        before ++ S5_107.renderMultipleSquares gap ++ [separator]
      have nextMonotone :
          ∀ tested,
            whole.count tested ≤
              (nextBefore ++ remainder).count tested := by
        intro tested
        have old := monotone tested
        have gapBound := count_le_renderMultipleSquares tested gap
        dsimp [nextBefore]
        simp only [List.count_append, List.count_cons, List.count_nil] at *
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
    (segments : List (List Nat × Nat)) (finalGap before : List Nat) :
    ListDerives
      (before ++ renderSquaredSeparatorDecomposition segments finalGap)
      (before ++ renderCanonicalSeparatorDecomposition segments finalGap) := by
  induction segments generalizing before with
  | nil =>
      simpa [renderSquaredSeparatorDecomposition,
        renderCanonicalSeparatorDecomposition] using
          (listDerivesCanonicalGap finalGap).prepend before
  | cons factor rest induction =>
      rcases factor with ⟨gap, separator⟩
      have first :=
        (listDerivesCanonicalGap gap).context before
          (separator ::
            renderSquaredSeparatorDecomposition rest finalGap)
      let nextBefore := before ++ canonicalGap gap ++ [separator]
      have tail := induction nextBefore
      have combined :
          ListDerives
            (before ++ S5_107.renderMultipleSquares gap ++
              separator ::
                renderSquaredSeparatorDecomposition rest finalGap)
            (before ++ canonicalGap gap ++
              separator ::
                renderCanonicalSeparatorDecomposition rest finalGap) :=
        first.trans <| by
          simpa [nextBefore, renderSquaredSeparatorDecomposition,
            renderCanonicalSeparatorDecomposition,
            List.append_assoc] using tail
      simpa [renderSquaredSeparatorDecomposition,
        renderCanonicalSeparatorDecomposition,
        List.append_assoc] using combined

/-- Every word derives to sorted distinct square blocks in every nonsimple
gap, with every globally simple separator retained literally. -/
theorem listDerivesNormalizeSeparatorDecomposition
    (whole : List Nat)
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderCanonicalSeparatorDecomposition segments finalGap) :=
  (listDerivesSquareSeparatorDecomposition whole decomposition).trans <| by
    simpa using
      listDerivesCanonicalizeSquaredDecomposition segments finalGap []

end SemigroupBasis.CoRoots.S6_3944
