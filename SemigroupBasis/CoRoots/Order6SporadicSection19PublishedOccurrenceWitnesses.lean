import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedFactorContexts

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses

open FactorContexts CrossFactor CrossSweep CrossLeftSweep AnchorPropagation
  BinaryPowers SquareAlgebra

/-- The first occurrence clause in Section19.1, with its actual adjacency. -/
def C1 (x y : Nat) (letters : List Nat) : Prop :=
  ∃ before middle after : List Nat,
    letters = before ++ x :: (middle ++ y :: x :: after)

/-- The second occurrence clause; the four positions are strictly ordered. -/
def C2 (x y : Nat) (letters : List Nat) : Prop :=
  ([x, y, x, y] : List Nat).Sublist letters

def PairRelated (x y : Nat) (letters : List Nat) : Prop :=
  C1 x y letters ∨ C1 y x letters ∨ C2 x y letters ∨ C2 y x letters

theorem join_contextWords (before after : List Nat) :
    joinGap (contextWord before) (contextWord after) = contextWord (before ++ after) := by
  cases before with
  | nil => rfl
  | cons first rest =>
      cases after with
      | nil =>
          rw [List.append_nil]
          rfl
      | cons next later => rfl

theorem push_contextWord (before : List Nat) (value : Nat) :
    pushGap (contextWord before) (Word.singleton value) = contextWord (before ++ [value]) := by
  cases before <;> rfl

theorem gap_toList (piece : Word Nat) (middle : Option (Word Nat)) :
    (gap piece middle).toList = piece.toList ++ contextLetters middle := by
  cases middle with
  | none => exact (List.append_nil piece.toList).symm
  | some word => exact Word.toList_append piece word

theorem singleton_toList (value : Nat) : (Word.singleton value).toList = [value] := rfl

theorem shortAnchor_toList (x y : Nat) (middle : List Nat) :
    (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)).toList =
      x :: (middle ++ [y, x]) := by
  simp only [shortAnchor, Word.toList_append, gap_toList, contextLetters_contextWord,
    singleton_toList, List.cons_append, List.nil_append, List.append_assoc]

theorem anchor_toList (x y : Nat) (middle : List Nat) :
    (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)).toList =
      x :: (middle ++ [y, y, x]) := by
  simp only [anchor, Word.toList_append, gap_toList, contextLetters_contextWord,
    singleton_toList, List.cons_append, List.nil_append, List.append_assoc]

theorem crossing_toList (x y : Nat) (first second third : List Nat) :
    (crossing (Word.singleton x) (Word.singleton y)
      (contextWord first) (contextWord second) (contextWord third)).toList =
      x :: (first ++ y :: (second ++ x :: (third ++ [y]))) := by
  simp only [crossing, Word.toList_append, gap_toList, contextLetters_contextWord,
    singleton_toList, List.cons_append, List.nil_append, List.append_assoc]

theorem split_letter (value : Nat) (letters : List Nat) (member : value ∈ letters) :
    ∃ before after : List Nat, letters = before ++ value :: after := by
  induction letters with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · cases equal
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, split⟩ := ih later
        refine ⟨first :: before, after, ?_⟩
        exact congrArg (List.cons first) split

/-- The other y really occurs before, inside, or after the selected C1 core. -/
theorem second_occurrence (x y : Nat) (different : x ≠ y)
    (before middle after : List Nat)
    (repeated : 2 ≤ (before ++ x :: (middle ++ y :: x :: after)).count y) :
    y ∈ before ∨ y ∈ middle ∨ y ∈ after := by
  by_cases left : y ∈ before
  · exact Or.inl left
  by_cases inside : y ∈ middle
  · exact Or.inr (Or.inl inside)
  by_cases right : y ∈ after
  · exact Or.inr (Or.inr right)
  have zeroLeft : before.count y = 0 := List.count_eq_zero.mpr left
  have zeroMiddle : middle.count y = 0 := List.count_eq_zero.mpr inside
  have zeroRight : after.count y = 0 := List.count_eq_zero.mpr right
  have one : (before ++ x :: (middle ++ y :: x :: after)).count y = 1 := by
    simp only [List.count_append, List.count_cons_of_ne different, List.count_cons_self,
      zeroLeft, zeroMiddle, zeroRight, Nat.zero_add]
  omega

theorem c1_word_as_frame (x y : Nat) (word : Word Nat)
    (before middle after : List Nat)
    (split : word.toList = before ++ x :: (middle ++ y :: x :: after)) :
    word = Context.frame (contextWord before) (contextWord after)
      (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
  apply Word.toList_injective
  rw [split, frame_of_lists_toList, shortAnchor_toList]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- The actual C1 core gains its repeated-y seed using the proved second
occurrence. Every original context and the complete middle word are retained. -/
theorem c1_seed_from_split (x y : Nat) (different : x ≠ y)
    (before middle after : List Nat)
    (repeated : 2 ≤ (before ++ x :: (middle ++ y :: x :: after)).count y) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle))) := by
  rcases second_occurrence x y different before middle after repeated with left | inside | right
  · obtain ⟨earlier, between, split⟩ := split_letter y before left
    have step := Context.frame_derives
      (c1_seed_left (Word.singleton x) (Word.singleton y)
        (contextWord middle) (contextWord between))
      (contextWord earlier) (contextWord after)
    have sourceEq :
        Context.frame (contextWord earlier) (contextWord after)
          (gap (Word.singleton y) (contextWord between) ++
            shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)) =
        Context.frame (contextWord before) (contextWord after)
          (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
      apply Word.toList_injective
      rw [split]
      simp only [frame_of_lists_toList, Word.toList_append, gap_toList,
        contextLetters_contextWord, singleton_toList,
        List.append_assoc, List.cons_append, List.nil_append]
    have targetEq :
        Context.frame (contextWord earlier) (contextWord after)
          (gap (Word.singleton y) (contextWord between) ++
            anchor (Word.singleton x) (Word.singleton y) (contextWord middle)) =
        Context.frame (contextWord before) (contextWord after)
          (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
      apply Word.toList_injective
      rw [split]
      simp only [frame_of_lists_toList, Word.toList_append, gap_toList,
        contextLetters_contextWord, singleton_toList,
        List.append_assoc, List.cons_append, List.nil_append]
    rw [sourceEq, targetEq] at step
    exact step
  · obtain ⟨earlier, later, split⟩ := split_letter y middle inside
    have middleEq :
        joinGap (pushGap (contextWord earlier) (Word.singleton y)) (contextWord later) =
          contextWord middle := by
      rw [push_contextWord, join_contextWords, split]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have core := c1_seed_middle (Word.singleton x) (Word.singleton y)
      (contextWord earlier) (contextWord later)
    rw [middleEq] at core
    exact Context.frame_derives core (contextWord before) (contextWord after)
  · obtain ⟨between, later, split⟩ := split_letter y after right
    have step := Context.frame_derives
      (c1_seed_right (Word.singleton x) (Word.singleton y)
        (contextWord middle) (contextWord between))
      (contextWord before) (contextWord later)
    have sourceEq :
        Context.frame (contextWord before) (contextWord later)
          (gap (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle))
            (contextWord between) ++ Word.singleton y) =
        Context.frame (contextWord before) (contextWord after)
          (shortAnchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
      apply Word.toList_injective
      rw [split]
      simp only [frame_of_lists_toList, Word.toList_append, gap_toList,
        contextLetters_contextWord, singleton_toList,
        List.append_assoc, List.cons_append, List.nil_append]
    have targetEq :
        Context.frame (contextWord before) (contextWord later)
          (gap (anchor (Word.singleton x) (Word.singleton y) (contextWord middle))
            (contextWord between) ++ Word.singleton y) =
        Context.frame (contextWord before) (contextWord after)
          (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
      apply Word.toList_injective
      rw [split]
      simp only [frame_of_lists_toList, Word.toList_append, gap_toList,
        contextLetters_contextWord, singleton_toList,
        List.append_assoc, List.cons_append, List.nil_append]
    rw [sourceEq, targetEq] at step
    exact step

theorem c1_seed_from_occurrences (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (repeated : 2 ≤ word.toList.count y)
    (occurs : C1 x y word.toList) :
    ∃ before middle after : List Nat,
      word.toList = before ++ x :: (middle ++ y :: x :: after) ∧
      Derives basis word
        (Context.frame (contextWord before) (contextWord after)
          (anchor (Word.singleton x) (Word.singleton y) (contextWord middle))) := by
  obtain ⟨before, middle, after, split⟩ := occurs
  have count : 2 ≤ (before ++ x :: (middle ++ y :: x :: after)).count y := by
    rw [← split]
    exact repeated
  have step := c1_seed_from_split x y different before middle after count
  rw [← c1_word_as_frame x y word before middle after split] at step
  exact ⟨before, middle, after, split, step⟩

theorem sublist_head_split (value : Nat) (rest letters : List Nat)
    (occurs : (value :: rest).Sublist letters) :
    ∃ before after : List Nat,
      letters = before ++ value :: after ∧ rest.Sublist after := by
  induction letters with
  | nil => cases occurs
  | cons first tail ih =>
      cases occurs with
      | cons _ shorter =>
          obtain ⟨before, after, split, remaining⟩ := ih shorter
          exact ⟨first :: before, after, congrArg (List.cons first) split, remaining⟩
      | cons₂ _ shorter => exact ⟨[], tail, rfl, shorter⟩

/-- Extract all five contexts from the real four-position C2 sublist. -/
theorem c2_list_split (x y : Nat) (letters : List Nat) (occurs : C2 x y letters) :
    ∃ before first second third after : List Nat,
      letters = before ++ x :: (first ++ y :: (second ++ x :: (third ++ y :: after))) := by
  obtain ⟨before, tail1, split1, hit1⟩ := sublist_head_split x [y, x, y] letters occurs
  obtain ⟨first, tail2, split2, hit2⟩ := sublist_head_split y [x, y] tail1 hit1
  obtain ⟨second, tail3, split3, hit3⟩ := sublist_head_split x [y] tail2 hit2
  obtain ⟨third, after, split4, _⟩ := sublist_head_split y [] tail3 hit3
  refine ⟨before, first, second, third, after, ?_⟩
  rw [split1, split2, split3, split4]

theorem c2_word_as_frame (x y : Nat) (word : Word Nat)
    (before first second third after : List Nat)
    (split : word.toList = before ++ x :: (first ++ y ::
      (second ++ x :: (third ++ y :: after)))) :
    word = Context.frame (contextWord before) (contextWord after)
      (crossing (Word.singleton x) (Word.singleton y)
        (contextWord first) (contextWord second) (contextWord third)) := by
  apply Word.toList_injective
  rw [split, frame_of_lists_toList, crossing_toList]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- C2 supplies a proved anchor seed. Its three arbitrary gaps are carried
by crossingGap, not discarded by a binary projection. -/
theorem c2_seed_from_occurrences (x y : Nat) (word : Word Nat)
    (occurs : C2 x y word.toList) :
    ∃ before first second third after : List Nat,
      word.toList = before ++ x :: (first ++ y ::
        (second ++ x :: (third ++ y :: after))) ∧
      Derives basis word
        (Context.frame (contextWord before) (contextWord after)
          (anchor (Word.singleton x) (Word.singleton y)
            (crossingGap (Word.singleton x)
              (contextWord first) (contextWord second) (contextWord third)))) := by
  obtain ⟨before, first, second, third, after, split⟩ := c2_list_split x y word.toList occurs
  have step := Context.frame_derives
    (crossing_seed (Word.singleton x) (Word.singleton y)
      (contextWord first) (contextWord second) (contextWord third))
    (contextWord before) (contextWord after)
  rw [← c2_word_as_frame x y word before first second third after split] at step
  exact ⟨before, first, second, third, after, split, step⟩

def HasAnchorSeed (x y : Nat) (word : Word Nat) : Prop :=
  ∃ leftContext rightContext middle : Option (Word Nat),
    Derives basis word
      (Context.frame leftContext rightContext
        (anchor (Word.singleton x) (Word.singleton y) middle))

/-- The complete symmetric occurrence relation yields one of the two
oriented anchor seeds. This is not maximal-factor perfectification. -/
theorem related_has_anchor_seed (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    HasAnchorSeed x y word ∨ HasAnchorSeed y x word := by
  rcases related with c1 | c1 | c2 | c2
  · obtain ⟨before, middle, after, _, step⟩ :=
      c1_seed_from_occurrences x y word different yRepeated c1
    exact Or.inl ⟨contextWord before, contextWord after, contextWord middle, step⟩
  · obtain ⟨before, middle, after, _, step⟩ :=
      c1_seed_from_occurrences y x word (fun equal => different equal.symm) xRepeated c1
    exact Or.inr ⟨contextWord before, contextWord after, contextWord middle, step⟩
  · obtain ⟨before, first, second, third, after, _, step⟩ :=
      c2_seed_from_occurrences x y word c2
    exact Or.inl ⟨contextWord before, contextWord after,
      crossingGap (Word.singleton x) (contextWord first) (contextWord second) (contextWord third), step⟩
  · obtain ⟨before, first, second, third, after, _, step⟩ :=
      c2_seed_from_occurrences y x word c2
    exact Or.inr ⟨contextWord before, contextWord after,
      crossingGap (Word.singleton y) (contextWord first) (contextWord second) (contextWord third), step⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.join_contextWords
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.push_contextWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.gap_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.singleton_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.shortAnchor_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.anchor_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.crossing_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.split_letter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.second_occurrence
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c1_word_as_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c1_seed_from_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c1_seed_from_occurrences
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.sublist_head_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c2_list_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c2_word_as_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.c2_seed_from_occurrences
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OccurrenceWitnesses.related_has_anchor_seed
