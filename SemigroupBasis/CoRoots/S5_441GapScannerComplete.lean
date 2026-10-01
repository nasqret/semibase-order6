import SemigroupBasis.CoRoots.S5_441GapDecomposition

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- A scanner started before a supplied exact cut eventually emits that cut
at its exact location. The explicit equality records the scanner state
invariant throughout the induction over `left`. -/
private theorem exactCutScanner_complete
    {whole renderedPrefix gap left right : List Nat}
    {separator : Nat}
    (whole_eq :
      whole =
        renderedPrefix ++ gap ++ (left ++ (separator :: right)))
    (cut :
      UniqueSeparatorFourExactCut whole
        (renderedPrefix ++ gap ++ left) separator right) :
    ∃ before segment after,
      exactCutScanner whole renderedPrefix gap
          (left ++ (separator :: right)) =
        before ++ segment :: after ∧
      segment.separator = some separator ∧
      renderedPrefix ++
          renderExactCutSegments before ++ segment.gap =
        renderedPrefix ++ gap ++ left ∧
      renderExactCutSegments after = right := by
  induction left generalizing renderedPrefix gap with
  | nil =>
      rcases cut with ⟨_, countOne, disjoint⟩
      have countTest :
          decide (whole.count separator = 1) = true :=
        decide_eq_true countOne
      have disjointTest :
          exactCutSupportsDisjointBool
              (renderedPrefix ++ gap) right =
            true :=
        exactCutSupportsDisjointBool_eq_true_iff.mpr <| by
          simpa using disjoint
      have cutCondition :
          (decide (whole.count separator = 1) &&
            exactCutSupportsDisjointBool
              (renderedPrefix ++ gap) right) = true := by
        simp [countTest, disjointTest]
      refine
        ⟨[],
          ({ gap := gap, separator := some separator } :
            ExactCutSegment),
          exactCutScanner whole
            (renderedPrefix ++ gap ++ [separator]) [] right,
          ?_, rfl, ?_, ?_⟩
      · simp [exactCutScanner, cutCondition]
      · simp
      · simpa using
          render_exactCutScanner whole
            (renderedPrefix ++ gap ++ [separator]) [] right
  | cons candidate left ih =>
      simp only [List.cons_append, exactCutScanner]
      split
      · have nextWholeEq :
          whole =
            (renderedPrefix ++ gap ++ [candidate]) ++ [] ++
              (left ++ (separator :: right)) := by
          simpa [List.append_assoc] using whole_eq
        have nextCut :
            UniqueSeparatorFourExactCut whole
              ((renderedPrefix ++ gap ++ [candidate]) ++ [] ++
                left)
              separator right := by
          simpa [List.append_assoc] using cut
        obtain
          ⟨before, segment, after, scan_eq, separator_eq,
            left_eq, after_eq⟩ :=
          ih
            (renderedPrefix :=
              renderedPrefix ++ gap ++ [candidate])
            (gap := [])
            nextWholeEq nextCut
        refine
          ⟨({ gap := gap, separator := some candidate } :
              ExactCutSegment) :: before,
            segment, after, ?_, separator_eq, ?_, after_eq⟩
        · simpa [List.cons_append] using
            congrArg
              (fun tail =>
                ({ gap := gap, separator := some candidate } :
                    ExactCutSegment) :: tail)
              scan_eq
        · simpa [ExactCutSegment.render, List.append_assoc] using
            left_eq
      · have nextWholeEq :
          whole =
            renderedPrefix ++ (gap ++ [candidate]) ++
              (left ++ (separator :: right)) := by
          simpa [List.append_assoc] using whole_eq
        have nextCut :
            UniqueSeparatorFourExactCut whole
              (renderedPrefix ++ (gap ++ [candidate]) ++ left)
              separator right := by
          simpa [List.append_assoc] using cut
        obtain
          ⟨before, segment, after, scan_eq, separator_eq,
            left_eq, after_eq⟩ :=
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])
            nextWholeEq nextCut
        refine
          ⟨before, segment, after, ?_, separator_eq, ?_, after_eq⟩
        · simpa using scan_eq
        · simpa [List.append_assoc] using left_eq

/-- The deterministic scanner emits every exact cut, at precisely the
rendered location represented by its segment decomposition. -/
theorem exactCutDecomposition_exactCut_iff
    {letters left right : List Nat} {separator : Nat} :
    UniqueSeparatorFourExactCut letters left separator right ↔
      ∃ before segment after,
        exactCutDecomposition letters =
          before ++ segment :: after ∧
        segment.separator = some separator ∧
        renderExactCutSegments before ++ segment.gap = left ∧
        renderExactCutSegments after = right := by
  constructor
  · intro cut
    have wholeEq :
        letters = [] ++ [] ++ (left ++ (separator :: right)) := by
      simpa [List.append_assoc] using cut.1
    have scannerCut :
        UniqueSeparatorFourExactCut letters
          ([] ++ [] ++ left) separator right := by
      simpa using cut
    obtain
      ⟨before, segment, after, scan_eq, separator_eq,
        left_eq, after_eq⟩ :=
      exactCutScanner_complete wholeEq scannerCut
    refine
      ⟨before, segment, after, ?_, separator_eq, ?_, after_eq⟩
    · simpa [exactCutDecomposition, cut.1] using scan_eq
    · simpa using left_eq
  · rintro
      ⟨before, segment, after, decomposition_eq, separator_eq,
        left_eq, after_eq⟩
    have exactCut :=
      exactCutDecomposition_separator_exactCut
        decomposition_eq separator_eq
    rw [left_eq, after_eq] at exactCut
    exact exactCut

/-- If the original word has no exact cut, every scanner state consists of
one terminal segment containing its current gap and unprocessed suffix. -/
private theorem exactCutScanner_eq_terminal_of_no_exactCut
    {whole renderedPrefix gap remaining : List Nat}
    (whole_eq : whole = renderedPrefix ++ gap ++ remaining)
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut whole left separator right) :
    exactCutScanner whole renderedPrefix gap remaining =
      [({ gap := gap ++ remaining, separator := none } :
        ExactCutSegment)] := by
  induction remaining generalizing renderedPrefix gap with
  | nil =>
      simp [exactCutScanner]
  | cons candidate remaining ih =>
      simp only [exactCutScanner]
      split
      · rename_i cutCondition
        simp only [Bool.and_eq_true] at cutCondition
        rcases cutCondition with ⟨countTest, disjointTest⟩
        have cut :
            UniqueSeparatorFourExactCut whole
              (renderedPrefix ++ gap) candidate remaining := by
          refine
            ⟨?_, of_decide_eq_true countTest,
              exactCutSupportsDisjointBool_eq_true_iff.mp
                disjointTest⟩
          simpa [List.append_assoc] using whole_eq
        exact False.elim <|
          noExactCut
            ⟨renderedPrefix ++ gap, candidate, remaining, cut⟩
      · have nextWholeEq :
          whole =
            renderedPrefix ++ (gap ++ [candidate]) ++ remaining := by
          simpa [List.append_assoc] using whole_eq
        have recurse :=
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])
            nextWholeEq
        simpa [List.append_assoc] using recurse

/-- The decomposition has only its terminal gap exactly when the word has no
exact separator cut. -/
theorem exactCutDecomposition_terminal_iff
    (letters : List Nat) :
    exactCutDecomposition letters =
        [({ gap := letters, separator := none } :
          ExactCutSegment)] ↔
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut letters left separator right := by
  constructor
  · intro decomposition_eq
    rintro ⟨left, separator, right, cut⟩
    obtain
      ⟨before, segment, after, segment_eq, separator_eq, _, _⟩ :=
      exactCutDecomposition_exactCut_iff.mp cut
    have segmentMember :
        segment ∈ exactCutDecomposition letters := by
      rw [segment_eq]
      simp
    rw [decomposition_eq] at segmentMember
    have segment_eq_terminal :
        segment =
          ({ gap := letters, separator := none } :
            ExactCutSegment) := by
      simpa using segmentMember
    subst segment
    simp at separator_eq
  · intro noExactCut
    have scannerTerminal :=
      exactCutScanner_eq_terminal_of_no_exactCut
        (whole := letters)
        (renderedPrefix := [])
        (gap := [])
        (remaining := letters)
        (by simp) noExactCut
    simpa [exactCutDecomposition] using scannerTerminal

end SemigroupBasis.CoRoots.S5_441
