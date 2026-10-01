import SemigroupBasis.CoRoots.S5_441GapOwnership

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

private theorem mem_renderExactCutSegments_of_gap
    {segments : List ExactCutSegment}
    {segment : ExactCutSegment} {letter : Nat}
    (segment_member : segment ∈ segments)
    (letter_member : letter ∈ segment.gap) :
    letter ∈ renderExactCutSegments segments := by
  change
    letter ∈ segments.flatMap ExactCutSegment.render
  rw [List.mem_flatMap]
  refine ⟨segment, segment_member, ?_⟩
  change letter ∈ segment.gap ++ segment.separator.toList
  exact List.mem_append_left _ letter_member

private theorem mem_exactCutSeparators_of_separator_toList
    {segments : List ExactCutSegment}
    {segment : ExactCutSegment} {letter : Nat}
    (segment_member : segment ∈ segments)
    (letter_member : letter ∈ segment.separator.toList) :
    letter ∈ exactCutSeparators segments := by
  unfold exactCutSeparators
  rw [List.mem_filterMap]
  refine ⟨segment, segment_member, ?_⟩
  cases separator_eq : segment.separator with
  | none =>
      simp [separator_eq] at letter_member
  | some separator =>
      have letter_eq : letter = separator := by
        simpa [separator_eq] using letter_member
      subst separator
      simpa [separator_eq]

private theorem exactCut_separator_not_left
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  have count_one := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at count_one
  omega

private theorem exactCut_separator_not_right
    {letters left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ right := by
  intro member
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  have count_one := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at count_one
  omega

/-- A letter stored in a decomposition gap cannot also be the value of any
emitted exact-cut separator. -/
theorem exactCutDecomposition_gap_letter_not_separator
    {letters : List Nat} {segment : ExactCutSegment}
    {letter : Nat}
    (segment_member :
      segment ∈ exactCutDecomposition letters)
    (letter_member : letter ∈ segment.gap) :
    letter ∉
      exactCutSeparators (exactCutDecomposition letters) := by
  intro separator_member
  unfold exactCutSeparators at separator_member
  rw [List.mem_filterMap] at separator_member
  rcases separator_member with
    ⟨separator_segment, separator_segment_member, separator_eq⟩
  obtain ⟨before, after, decomposition_eq⟩ :=
    List.mem_iff_append.mp separator_segment_member
  have cut :=
    exactCutDecomposition_separator_exactCut
      (letters := letters)
      (before := before)
      (after := after)
      (segment := separator_segment)
      (separator := letter)
      decomposition_eq separator_eq
  have separator_not_left :=
    exactCut_separator_not_left cut
  have separator_not_right :=
    exactCut_separator_not_right cut
  rw [decomposition_eq] at segment_member
  simp only [List.mem_append, List.mem_cons] at segment_member
  rcases segment_member with
      segment_before | segment_eq | segment_after
  · apply separator_not_left
    exact
      List.mem_append_left _ <|
        mem_renderExactCutSegments_of_gap
          segment_before letter_member
  · apply separator_not_left
    exact
      List.mem_append_right _ <|
        segment_eq ▸ letter_member
  · apply separator_not_right
    exact
      mem_renderExactCutSegments_of_gap
        segment_after letter_member

private theorem pairwise_gap_disjoint_of_mem_before
    {before after : List ExactCutSegment}
    {owner candidate : ExactCutSegment}
    (pairwise :
      (before ++ owner :: after).Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.gap right.gap))
    (candidate_member : candidate ∈ before) :
    UniqueSeparatorFourSupportsDisjoint
      candidate.gap owner.gap := by
  induction before with
  | nil =>
      simp at candidate_member
  | cons head tail ih =>
      simp only [List.cons_append, List.pairwise_cons] at pairwise
      simp only [List.mem_cons] at candidate_member
      rcases candidate_member with candidate_eq | candidate_tail
      · subst candidate
        exact pairwise.1 owner (by simp)
      · exact ih pairwise.2 candidate_tail

private theorem pairwise_gap_disjoint_of_mem_after
    {before after : List ExactCutSegment}
    {owner candidate : ExactCutSegment}
    (pairwise :
      (before ++ owner :: after).Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.gap right.gap))
    (candidate_member : candidate ∈ after) :
    UniqueSeparatorFourSupportsDisjoint
      owner.gap candidate.gap := by
  induction before with
  | nil =>
      simp only [List.nil_append, List.pairwise_cons] at pairwise
      exact pairwise.1 candidate candidate_member
  | cons head tail ih =>
      simp only [List.cons_append, List.pairwise_cons] at pairwise
      exact ih pairwise.2

/-- Every occurrence of a gap-owned letter is localized in its unique gap.
In particular, its count in the original list is exactly its count in that
gap. -/
theorem exactCutDecomposition_count_eq_gap_count
    {letters : List Nat} {segment : ExactCutSegment}
    {letter : Nat}
    (segment_member :
      segment ∈ exactCutDecomposition letters)
    (letter_member : letter ∈ segment.gap) :
    letters.count letter = segment.gap.count letter := by
  have letter_member_letters : letter ∈ letters := by
    rw [← render_exactCutDecomposition letters]
    exact
      mem_renderExactCutSegments_of_gap
        segment_member letter_member
  have not_separator :=
    exactCutDecomposition_gap_letter_not_separator
      segment_member letter_member
  obtain ⟨owner, _owner_data, owner_unique⟩ :=
    existsUnique_exactCutDecomposition_gap_of_not_separator
      letter_member_letters not_separator
  have segment_eq_owner :
      segment = owner :=
    owner_unique segment ⟨segment_member, letter_member⟩
  have gap_owner_unique :
      ∀ candidate : ExactCutSegment,
        candidate ∈ exactCutDecomposition letters ∧
            letter ∈ candidate.gap →
          candidate = segment := by
    intro candidate candidate_data
    exact
      (owner_unique candidate candidate_data).trans
        segment_eq_owner.symm
  obtain ⟨before, after, decomposition_eq⟩ :=
    List.mem_iff_append.mp segment_member
  have pairwise :
      (before ++ segment :: after).Pairwise
        (fun left right =>
          UniqueSeparatorFourSupportsDisjoint
            left.gap right.gap) := by
    rw [← decomposition_eq]
    exact exactCutDecomposition_gaps_pairwise_disjoint letters
  have segment_not_before : segment ∉ before := by
    intro segment_before
    have disjoint :=
      pairwise_gap_disjoint_of_mem_before
        pairwise segment_before
    exact disjoint letter letter_member letter_member
  have segment_not_after : segment ∉ after := by
    intro segment_after
    have disjoint :=
      pairwise_gap_disjoint_of_mem_after
        pairwise segment_after
    exact disjoint letter letter_member letter_member
  have before_not_mem :
      letter ∉ renderExactCutSegments before := by
    intro rendered_member
    change
      letter ∈ before.flatMap ExactCutSegment.render
        at rendered_member
    rw [List.mem_flatMap] at rendered_member
    rcases rendered_member with
      ⟨candidate, candidate_before, candidate_render_member⟩
    have candidate_member :
        candidate ∈ exactCutDecomposition letters := by
      rw [decomposition_eq]
      exact List.mem_append_left _ candidate_before
    change
      letter ∈ candidate.gap ++ candidate.separator.toList
        at candidate_render_member
    rw [List.mem_append] at candidate_render_member
    rcases candidate_render_member with
        candidate_gap_member | candidate_separator_member
    · have candidate_eq :=
        gap_owner_unique candidate
          ⟨candidate_member, candidate_gap_member⟩
      exact
        segment_not_before <|
          candidate_eq ▸ candidate_before
    · exact
        not_separator <|
          mem_exactCutSeparators_of_separator_toList
            candidate_member candidate_separator_member
  have after_not_mem :
      letter ∉ renderExactCutSegments after := by
    intro rendered_member
    change
      letter ∈ after.flatMap ExactCutSegment.render
        at rendered_member
    rw [List.mem_flatMap] at rendered_member
    rcases rendered_member with
      ⟨candidate, candidate_after, candidate_render_member⟩
    have candidate_member :
        candidate ∈ exactCutDecomposition letters := by
      rw [decomposition_eq]
      exact
        List.mem_append_right _ <|
          List.Mem.tail segment candidate_after
    change
      letter ∈ candidate.gap ++ candidate.separator.toList
        at candidate_render_member
    rw [List.mem_append] at candidate_render_member
    rcases candidate_render_member with
        candidate_gap_member | candidate_separator_member
    · have candidate_eq :=
        gap_owner_unique candidate
          ⟨candidate_member, candidate_gap_member⟩
      exact
        segment_not_after <|
          candidate_eq ▸ candidate_after
    · exact
        not_separator <|
          mem_exactCutSeparators_of_separator_toList
            candidate_member candidate_separator_member
  have segment_separator_not_mem :
      letter ∉ segment.separator.toList := by
    intro separator_member
    exact
      not_separator <|
        mem_exactCutSeparators_of_separator_toList
          segment_member separator_member
  have before_count_zero :
      (renderExactCutSegments before).count letter = 0 :=
    List.count_eq_zero.mpr before_not_mem
  have after_count_zero :
      (renderExactCutSegments after).count letter = 0 :=
    List.count_eq_zero.mpr after_not_mem
  have segment_separator_count_zero :
      segment.separator.toList.count letter = 0 :=
    List.count_eq_zero.mpr segment_separator_not_mem
  have render_split :
      renderExactCutSegments (before ++ segment :: after) =
        renderExactCutSegments before ++ segment.gap ++
          segment.separator.toList ++
            renderExactCutSegments after := by
    simp [renderExactCutSegments, ExactCutSegment.render,
      List.append_assoc]
  calc
    letters.count letter =
        (renderExactCutSegments
          (exactCutDecomposition letters)).count letter := by
      rw [render_exactCutDecomposition]
    _ =
        (renderExactCutSegments
          (before ++ segment :: after)).count letter := by
      rw [← decomposition_eq]
    _ =
        (renderExactCutSegments before ++ segment.gap ++
          segment.separator.toList ++
            renderExactCutSegments after).count letter := by
      rw [render_split]
    _ = segment.gap.count letter := by
      simp [List.count_append, before_count_zero,
        after_count_zero, segment_separator_count_zero]

/-- Count localization immediately localizes the parity coordinate as well. -/
theorem exactCutDecomposition_count_mod_two_eq_gap_count_mod_two
    {letters : List Nat} {segment : ExactCutSegment}
    {letter : Nat}
    (segment_member :
      segment ∈ exactCutDecomposition letters)
    (letter_member : letter ∈ segment.gap) :
    letters.count letter % 2 =
      segment.gap.count letter % 2 := by
  rw [exactCutDecomposition_count_eq_gap_count
    segment_member letter_member]

end SemigroupBasis.CoRoots.S5_441
