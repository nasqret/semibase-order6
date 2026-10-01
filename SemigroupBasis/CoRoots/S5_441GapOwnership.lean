import SemigroupBasis.CoRoots.S5_441GapDecomposition

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- The separators emitted by an exact-cut decomposition. -/
def exactCutSeparators
    (segments : List ExactCutSegment) : List Nat :=
  segments.filterMap ExactCutSegment.separator

/-- The gaps stored by an exact-cut decomposition. -/
def exactCutGaps
    (segments : List ExactCutSegment) : List (List Nat) :=
  segments.map ExactCutSegment.gap

private theorem exactCutScanner_ne_nil
    (whole renderedPrefix gap remaining : List Nat) :
    exactCutScanner whole renderedPrefix gap remaining ≠ [] := by
  induction remaining generalizing renderedPrefix gap with
  | nil =>
      simp [exactCutScanner]
  | cons candidate remaining ih =>
      simp only [exactCutScanner]
      split
      · simp
      · exact
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])

private theorem exactCutScanner_final_separator_none
    {whole renderedPrefix gap remaining : List Nat}
    {before : List ExactCutSegment} {segment : ExactCutSegment}
    (scan_eq :
      exactCutScanner whole renderedPrefix gap remaining =
        before ++ [segment]) :
    segment.separator = none := by
  induction remaining generalizing
      renderedPrefix gap before segment with
  | nil =>
      simp only [exactCutScanner] at scan_eq
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at scan_eq
          rcases scan_eq with ⟨segment_eq, _⟩
          subst segment
          rfl
      | cons beforeHead beforeTail =>
          simp only [List.cons_append, List.cons.injEq] at scan_eq
          have impossible :
              ([] : List ExactCutSegment) =
                beforeTail ++ [segment] :=
            scan_eq.2
          simp at impossible
  | cons candidate remaining ih =>
      simp only [exactCutScanner] at scan_eq
      split at scan_eq
      · cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at scan_eq
            have recursive_empty :
                exactCutScanner whole
                    (renderedPrefix ++ gap ++ [candidate])
                    [] remaining =
                  [] :=
              scan_eq.2
            exact False.elim <|
              exactCutScanner_ne_nil whole
                (renderedPrefix ++ gap ++ [candidate])
                [] remaining recursive_empty
        | cons beforeHead beforeTail =>
            simp only [List.cons_append, List.cons.injEq] at scan_eq
            exact
              ih
                (renderedPrefix :=
                  renderedPrefix ++ gap ++ [candidate])
                (gap := [])
                (before := beforeTail)
                (segment := segment)
                scan_eq.2
      · exact
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])
            (before := before)
            (segment := segment)
            scan_eq

private theorem exactCutScanner_nonfinal_separator_some
    {whole renderedPrefix gap remaining : List Nat}
    {before : List ExactCutSegment}
    {segment next : ExactCutSegment}
    {after : List ExactCutSegment}
    (scan_eq :
      exactCutScanner whole renderedPrefix gap remaining =
        before ++ segment :: next :: after) :
    ∃ separator, segment.separator = some separator := by
  induction remaining generalizing
      renderedPrefix gap before segment next after with
  | nil =>
      simp only [exactCutScanner] at scan_eq
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at scan_eq
          have impossible :
              ([] : List ExactCutSegment) = next :: after :=
            scan_eq.2
          simp at impossible
      | cons beforeHead beforeTail =>
          simp only [List.cons_append, List.cons.injEq] at scan_eq
          have impossible :
              ([] : List ExactCutSegment) =
                beforeTail ++ segment :: next :: after :=
            scan_eq.2
          simp at impossible
  | cons candidate remaining ih =>
      simp only [exactCutScanner] at scan_eq
      split at scan_eq
      · cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at scan_eq
            rcases scan_eq with ⟨segment_eq, _⟩
            subst segment
            exact ⟨candidate, rfl⟩
        | cons beforeHead beforeTail =>
            simp only [List.cons_append, List.cons.injEq] at scan_eq
            exact
              ih
                (renderedPrefix :=
                  renderedPrefix ++ gap ++ [candidate])
                (gap := [])
                (before := beforeTail)
                (segment := segment)
                (next := next)
                (after := after)
                scan_eq.2
      · exact
          ih
            (renderedPrefix := renderedPrefix)
            (gap := gap ++ [candidate])
            (before := before)
            (segment := segment)
            (next := next)
            (after := after)
            scan_eq

/-- The last segment in the deterministic decomposition has no separator. -/
theorem exactCutDecomposition_final_separator_none
    {letters : List Nat} {before : List ExactCutSegment}
    {segment : ExactCutSegment}
    (decomposition_eq :
      exactCutDecomposition letters = before ++ [segment]) :
    segment.separator = none := by
  apply exactCutScanner_final_separator_none
  simpa [exactCutDecomposition] using decomposition_eq

/-- Every segment followed by another segment has an emitted separator. -/
theorem exactCutDecomposition_nonfinal_separator_some
    {letters : List Nat} {before after : List ExactCutSegment}
    {segment next : ExactCutSegment}
    (decomposition_eq :
      exactCutDecomposition letters =
        before ++ segment :: next :: after) :
    ∃ separator, segment.separator = some separator := by
  apply exactCutScanner_nonfinal_separator_some
  simpa [exactCutDecomposition] using decomposition_eq

/-- In a split at a segment, absence of a separator is equivalent to that
segment being final. -/
theorem exactCutDecomposition_separator_none_iff_after_nil
    {letters : List Nat} {before after : List ExactCutSegment}
    {segment : ExactCutSegment}
    (decomposition_eq :
      exactCutDecomposition letters =
        before ++ segment :: after) :
    segment.separator = none ↔ after = [] := by
  constructor
  · intro separator_none
    cases after with
    | nil => rfl
    | cons next rest =>
        obtain ⟨separator, separator_some⟩ :=
          exactCutDecomposition_nonfinal_separator_some
            (letters := letters)
            (before := before)
            (segment := segment)
            (next := next)
            (after := rest)
            decomposition_eq
        simp [separator_none] at separator_some
  · intro after_nil
    apply exactCutDecomposition_final_separator_none
    simpa [after_nil] using decomposition_eq

theorem exactCutDecomposition_separator_some_of_after_ne_nil
    {letters : List Nat} {before after : List ExactCutSegment}
    {segment : ExactCutSegment}
    (decomposition_eq :
      exactCutDecomposition letters =
        before ++ segment :: after)
    (after_ne_nil : after ≠ []) :
    ∃ separator, segment.separator = some separator := by
  cases separator_eq : segment.separator with
  | none =>
      have after_nil :=
        (exactCutDecomposition_separator_none_iff_after_nil
          decomposition_eq).mp separator_eq
      exact False.elim (after_ne_nil after_nil)
  | some separator =>
      exact ⟨separator, rfl⟩

/-- Earlier and later segment gaps have disjoint supports. -/
theorem exactCutDecomposition_ordered_gaps_disjoint
    {letters : List Nat}
    {before between after : List ExactCutSegment}
    {left right : ExactCutSegment}
    (decomposition_eq :
      exactCutDecomposition letters =
        before ++ left :: (between ++ right :: after)) :
    UniqueSeparatorFourSupportsDisjoint left.gap right.gap := by
  have suffix_ne_nil : between ++ right :: after ≠ [] := by
    simp
  obtain ⟨separator, separator_eq⟩ :=
    exactCutDecomposition_separator_some_of_after_ne_nil
      (letters := letters)
      (before := before)
      (segment := left)
      (after := between ++ right :: after)
      decomposition_eq suffix_ne_nil
  have cut :=
    exactCutDecomposition_separator_exactCut
      (letters := letters)
      (before := before)
      (after := between ++ right :: after)
      (segment := left)
      decomposition_eq separator_eq
  rcases cut with ⟨_, _, disjoint⟩
  intro letter left_member right_member
  have left_rendered :
      letter ∈ renderExactCutSegments before ++ left.gap :=
    List.mem_append_right _ left_member
  have right_rendered :
      letter ∈
        renderExactCutSegments (between ++ right :: after) := by
    change
      letter ∈
        (between ++ right :: after).flatMap ExactCutSegment.render
    rw [List.mem_flatMap]
    refine ⟨right, ?_, ?_⟩
    · simp
    · change letter ∈ right.gap ++ right.separator.toList
      exact List.mem_append_left _ right_member
  exact disjoint letter left_rendered right_rendered

private theorem exactCutDecomposition_suffix_gaps_pairwise_disjoint
    {letters : List Nat} :
    ∀ {scanPrefix suffix : List ExactCutSegment},
      exactCutDecomposition letters = scanPrefix ++ suffix →
        suffix.Pairwise
          (fun left right =>
            UniqueSeparatorFourSupportsDisjoint
              left.gap right.gap) := by
  intro scanPrefix suffix decomposition_eq
  induction suffix generalizing scanPrefix with
  | nil =>
      simp
  | cons left rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro right right_member
        obtain ⟨between, after, rest_eq⟩ :=
          List.mem_iff_append.mp right_member
        apply exactCutDecomposition_ordered_gaps_disjoint
          (letters := letters)
          (before := scanPrefix)
          (between := between)
          (after := after)
          (left := left)
          (right := right)
        rw [decomposition_eq, rest_eq]
      · apply ih (scanPrefix := scanPrefix ++ [left])
        simpa [List.append_assoc] using decomposition_eq

/-- The gaps in the deterministic decomposition have pairwise disjoint
supports in decomposition order. -/
theorem exactCutDecomposition_gaps_pairwise_disjoint
    (letters : List Nat) :
    (exactCutDecomposition letters).Pairwise
      (fun left right =>
        UniqueSeparatorFourSupportsDisjoint
          left.gap right.gap) := by
  apply exactCutDecomposition_suffix_gaps_pairwise_disjoint
    (letters := letters)
    (scanPrefix := [])
  simp

/-- Every non-separator letter of the original list occurs in a segment gap. -/
theorem exists_exactCutDecomposition_gap_of_not_separator
    {letters : List Nat} {letter : Nat}
    (letter_member : letter ∈ letters)
    (not_separator :
      letter ∉
        exactCutSeparators (exactCutDecomposition letters)) :
    ∃ segment,
      segment ∈ exactCutDecomposition letters ∧
        letter ∈ segment.gap := by
  have rendered_member :
      letter ∈
        renderExactCutSegments (exactCutDecomposition letters) := by
    rw [render_exactCutDecomposition]
    exact letter_member
  change
    letter ∈
      (exactCutDecomposition letters).flatMap
        ExactCutSegment.render at rendered_member
  rw [List.mem_flatMap] at rendered_member
  rcases rendered_member with
    ⟨segment, segment_member, segment_render_member⟩
  refine ⟨segment, segment_member, ?_⟩
  change
    (letter ∈ segment.gap ++ segment.separator.toList)
      at segment_render_member
  rw [List.mem_append] at segment_render_member
  rcases segment_render_member with gap_member | separator_member
  · exact gap_member
  · exfalso
    apply not_separator
    unfold exactCutSeparators
    rw [List.mem_filterMap]
    refine ⟨segment, segment_member, ?_⟩
    cases separator_eq : segment.separator with
    | none =>
        simp [separator_eq] at separator_member
    | some separator =>
        have letter_eq : letter = separator := by
          simpa [separator_eq] using separator_member
        subst separator
        simpa [separator_eq]

/-- Every non-separator letter has exactly one owning gap segment. -/
theorem existsUnique_exactCutDecomposition_gap_of_not_separator
    {letters : List Nat} {letter : Nat}
    (letter_member : letter ∈ letters)
    (not_separator :
      letter ∉
        exactCutSeparators (exactCutDecomposition letters)) :
    ∃ owner : ExactCutSegment,
      (owner ∈ exactCutDecomposition letters ∧
        letter ∈ owner.gap) ∧
      ∀ candidate : ExactCutSegment,
        candidate ∈ exactCutDecomposition letters ∧
            letter ∈ candidate.gap →
          candidate = owner := by
  obtain ⟨owner, owner_member, letter_in_owner⟩ :=
    exists_exactCutDecomposition_gap_of_not_separator
      letter_member not_separator
  refine ⟨owner, ⟨⟨owner_member, letter_in_owner⟩, ?_⟩⟩
  intro candidate candidate_data
  rcases candidate_data with
    ⟨candidate_member, letter_in_candidate⟩
  obtain ⟨before, after, decomposition_eq⟩ :=
    List.mem_iff_append.mp owner_member
  rw [decomposition_eq] at candidate_member
  simp only [List.mem_append, List.mem_cons] at candidate_member
  rcases candidate_member with
      candidate_before | candidate_eq | candidate_after
  · obtain ⟨leading, middle, before_eq⟩ :=
      List.mem_iff_append.mp candidate_before
    have ordered_eq :
        exactCutDecomposition letters =
          leading ++ candidate :: (middle ++ owner :: after) := by
      rw [decomposition_eq, before_eq]
      simp [List.append_assoc]
    have disjoint :=
      exactCutDecomposition_ordered_gaps_disjoint
        (letters := letters)
        (before := leading)
        (between := middle)
        (after := after)
        (left := candidate)
        (right := owner)
        ordered_eq
    exact False.elim <|
      disjoint letter letter_in_candidate letter_in_owner
  · exact candidate_eq
  · obtain ⟨middle, trailing, after_eq⟩ :=
      List.mem_iff_append.mp candidate_after
    have ordered_eq :
        exactCutDecomposition letters =
          before ++ owner :: (middle ++ candidate :: trailing) := by
      rw [decomposition_eq, after_eq]
    have disjoint :=
      exactCutDecomposition_ordered_gaps_disjoint
        (letters := letters)
        (before := before)
        (between := middle)
        (after := trailing)
        (left := owner)
        (right := candidate)
        ordered_eq
    exact False.elim <|
      disjoint letter letter_in_owner letter_in_candidate

end SemigroupBasis.CoRoots.S5_441
