import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedOccurrenceWitnesses

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep
  BinaryPowers SquareAlgebra PerfectSweeps FactorContexts OccurrenceWitnesses

abbrev RawSegment := List Nat × Letter

def tagValue (x y : Nat) (tag : Letter) : Nat :=
  if tag.val = 0 then x else y

def segments (items : List RawSegment) : List Segment :=
  items.map (fun item => (contextWord item.1, item.2))

def beforeLetters (x y : Nat) : List RawSegment → List Nat
  | [] => []
  | item :: rest => item.1 ++ tagValue x y item.2 :: beforeLetters x y rest

def afterLetters (x y : Nat) : List RawSegment → List Nat
  | [] => []
  | item :: rest => tagValue x y item.2 :: (item.1 ++ afterLetters x y rest)

/-- The left codec keeps the leading unmarked letters and gaps after marks. -/
def encodeLeft (x y : Nat) : List Nat → List Nat × List RawSegment
  | [] => ([], [])
  | letter :: rest =>
      let encoded := encodeLeft x y rest
      if letter = x then ([], (encoded.1, 0) :: encoded.2)
      else if letter = y then ([], (encoded.1, 1) :: encoded.2)
      else (letter :: encoded.1, encoded.2)

/-- The right/middle codec keeps gaps before marks and the unmarked tail. -/
def encodeRight (x y : Nat) : List Nat → List RawSegment × List Nat
  | [] => ([], [])
  | letter :: rest =>
      let encoded := encodeRight x y rest
      if letter = x then (([], 0) :: encoded.1, encoded.2)
      else if letter = y then (([], 1) :: encoded.1, encoded.2)
      else match encoded.1 with
        | [] => ([], letter :: encoded.2)
        | item :: later => ((letter :: item.1, item.2) :: later, encoded.2)

theorem left_encoding (x y : Nat) (letters : List Nat) :
    (encodeLeft x y letters).1 ++ afterLetters x y (encodeLeft x y letters).2 =
      letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      cases split : encodeLeft x y rest with
      | mk leading marks =>
          simp only [split] at ih
          by_cases hx : letter = x
          · subst letter
            simpa [encodeLeft, split, afterLetters, tagValue] using congrArg (List.cons x) ih
          · by_cases hy : letter = y
            · subst letter
              simpa [encodeLeft, split, hx, afterLetters, tagValue] using congrArg (List.cons y) ih
            · simpa [encodeLeft, split, hx, hy] using congrArg (List.cons letter) ih

theorem right_encoding (x y : Nat) (letters : List Nat) :
    beforeLetters x y (encodeRight x y letters).1 ++ (encodeRight x y letters).2 =
      letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      cases split : encodeRight x y rest with
      | mk marks trailing =>
          simp only [split] at ih
          by_cases hx : letter = x
          · subst letter
            simpa [encodeRight, split, beforeLetters, tagValue] using congrArg (List.cons x) ih
          · by_cases hy : letter = y
            · subst letter
              simpa [encodeRight, split, hx, beforeLetters, tagValue] using congrArg (List.cons y) ih
            · cases marks with
              | nil =>
                  simpa [encodeRight, split, hx, hy, beforeLetters] using congrArg (List.cons letter) ih
              | cons item later =>
                  simpa [encodeRight, split, hx, hy, beforeLetters, List.append_assoc] using
                    congrArg (List.cons letter) ih

def Outside (x y : Nat) (letters : List Nat) : Prop :=
  ∀ letter ∈ letters, letter ≠ x ∧ letter ≠ y

def Clean (x y : Nat) (items : List RawSegment) : Prop :=
  ∀ item ∈ items, Outside x y item.1

theorem outside_nil (x y : Nat) : Outside x y [] := by
  intro letter member
  cases member

theorem outside_cons (x y letter : Nat) (letters : List Nat)
    (hx : letter ≠ x) (hy : letter ≠ y) (tail : Outside x y letters) :
    Outside x y (letter :: letters) := by
  intro value member
  rcases List.mem_cons.mp member with equal | later
  · subst value
    exact ⟨hx, hy⟩
  · exact tail value later

theorem clean_nil (x y : Nat) : Clean x y [] := by
  intro item member
  cases member

theorem clean_cons (x y : Nat) (item : RawSegment) (items : List RawSegment) :
    Clean x y (item :: items) ↔ Outside x y item.1 ∧ Clean x y items := by
  constructor
  · intro clean
    exact ⟨clean item (List.mem_cons.mpr (Or.inl rfl)),
      fun next member => clean next (List.mem_cons.mpr (Or.inr member))⟩
  · rintro ⟨head, tail⟩ next member
    rcases List.mem_cons.mp member with equal | later
    · subst next
      exact head
    · exact tail next later

/-- No occurrence of either marked letter can hide in a left-codec gap. -/
theorem left_clean (x y : Nat) (letters : List Nat) :
    Outside x y (encodeLeft x y letters).1 ∧ Clean x y (encodeLeft x y letters).2 := by
  induction letters with
  | nil => exact ⟨outside_nil x y, clean_nil x y⟩
  | cons letter rest ih =>
      cases split : encodeLeft x y rest with
      | mk leading marks =>
          simp only [split] at ih
          by_cases hx : letter = x
          · simpa only [encodeLeft, split, if_pos hx] using
              And.intro (outside_nil x y) ((clean_cons x y (leading, 0) marks).mpr ih)
          · by_cases hy : letter = y
            · simpa only [encodeLeft, split, if_neg hx, if_pos hy] using
                And.intro (outside_nil x y) ((clean_cons x y (leading, 1) marks).mpr ih)
            · simpa only [encodeLeft, split, if_neg hx, if_neg hy] using
                And.intro (outside_cons x y letter leading hx hy ih.1) ih.2

/-- No occurrence of either marked letter can hide in a right-codec gap. -/
theorem right_clean (x y : Nat) (letters : List Nat) :
    Clean x y (encodeRight x y letters).1 ∧ Outside x y (encodeRight x y letters).2 := by
  induction letters with
  | nil => exact ⟨clean_nil x y, outside_nil x y⟩
  | cons letter rest ih =>
      cases split : encodeRight x y rest with
      | mk marks trailing =>
          simp only [split] at ih
          by_cases hx : letter = x
          · simpa only [encodeRight, split, if_pos hx] using
              And.intro ((clean_cons x y ([], 0) marks).mpr ⟨outside_nil x y, ih.1⟩) ih.2
          · by_cases hy : letter = y
            · simpa only [encodeRight, split, if_neg hx, if_pos hy] using
                And.intro ((clean_cons x y ([], 1) marks).mpr ⟨outside_nil x y, ih.1⟩) ih.2
            · cases marks with
              | nil =>
                  simpa only [encodeRight, split, if_neg hx, if_neg hy] using
                    And.intro (clean_nil x y) (outside_cons x y letter trailing hx hy ih.2)
              | cons item later =>
                  have parts := (clean_cons x y item later).mp ih.1
                  have clean := (clean_cons x y (letter :: item.1, item.2) later).mpr
                    ⟨outside_cons x y letter item.1 hx hy parts.1, parts.2⟩
                  simpa only [encodeRight, split, if_neg hx, if_neg hy] using And.intro clean ih.2

theorem contextWord_contextLetters (piece : Option (Word Nat)) :
    contextWord (contextLetters piece) = piece := by
  cases piece with
  | none => rfl
  | some word => cases word; rfl

theorem join_letters (left right : Option (Word Nat)) :
    contextLetters (joinGap left right) = contextLetters left ++ contextLetters right := by
  cases left <;> cases right <;>
    simp only [joinGap, contextLetters, Word.toList_append, List.nil_append, List.append_nil]

theorem value_letters (x y : Nat) (tag : Letter) :
    (value (Word.singleton x) (Word.singleton y) tag).toList = [tagValue x y tag] := by
  unfold value tagValue
  split <;> rfl

theorem fold_before_letters (x y : Nat) (items : List RawSegment) :
    contextLetters (foldGap (value (Word.singleton x) (Word.singleton y)) (segments items)) =
      beforeLetters x y items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change contextLetters
        (joinGap (pushGap (contextWord item.1) (value (Word.singleton x) (Word.singleton y) item.2))
          (foldGap (value (Word.singleton x) (Word.singleton y)) (segments rest))) = _
      have pushed :
          contextLetters (pushGap (contextWord item.1)
            (value (Word.singleton x) (Word.singleton y) item.2)) =
          item.1 ++ [tagValue x y item.2] := by
        rw [pushGap, join_letters, contextLetters_contextWord]
        change item.1 ++ (value (Word.singleton x) (Word.singleton y) item.2).toList = _
        rw [value_letters]
      rw [join_letters, pushed, ih]
      simp only [beforeLetters, List.append_assoc, List.cons_append, List.nil_append]

theorem render_before_letters (x y : Nat) (initial : Word Nat) (items : List RawSegment) :
    (render (value (Word.singleton x) (Word.singleton y)) initial (segments items)).toList =
      initial.toList ++ beforeLetters x y items := by
  rw [render_foldGap, gap_toList, fold_before_letters]

theorem render_after_letters (x y : Nat) (finalWord : Word Nat) (items : List RawSegment) :
    (renderLeft (value (Word.singleton x) (Word.singleton y)) finalWord (segments items)).toList =
      afterLetters x y items ++ finalWord.toList := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change (gap (value (Word.singleton x) (Word.singleton y) item.2) (contextWord item.1) ++
        renderLeft (value (Word.singleton x) (Word.singleton y)) finalWord (segments rest)).toList = _
      rw [Word.toList_append, gap_toList, contextLetters_contextWord, value_letters, ih]
      simp only [afterLetters, List.append_assoc, List.cons_append, List.nil_append]

theorem middle_encoding (x y : Nat) (letters : List Nat) :
    joinGap (joinGap none
      (foldGap (value (Word.singleton x) (Word.singleton y)) (segments (encodeRight x y letters).1)))
      (contextWord (encodeRight x y letters).2) = contextWord letters := by
  have rendered : contextLetters
      (joinGap (joinGap none
        (foldGap (value (Word.singleton x) (Word.singleton y)) (segments (encodeRight x y letters).1)))
        (contextWord (encodeRight x y letters).2)) = letters := by
    change contextLetters
      (joinGap (foldGap (value (Word.singleton x) (Word.singleton y))
        (segments (encodeRight x y letters).1)) (contextWord (encodeRight x y letters).2)) = letters
    rw [join_letters, fold_before_letters, contextLetters_contextWord]
    exact right_encoding x y letters
  have converted := congrArg contextWord rendered
  simpa only [contextWord_contextLetters] using converted

/-- Actual lists determine both exterior representations; no rendering premise. -/
theorem exterior_rendering (x y : Nat) (before after : List Nat) (core : Word Nat) :
    Context.frame (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
      (render (value (Word.singleton x) (Word.singleton y))
        (renderLeft (value (Word.singleton x) (Word.singleton y)) core
          (segments (encodeLeft x y before).2)) (segments (encodeRight x y after).1)) =
    Context.frame (contextWord before) (contextWord after) core := by
  apply Word.toList_injective
  simp only [frame_of_lists_toList, render_before_letters, render_after_letters]
  have joined :
      ((encodeLeft x y before).1 ++ afterLetters x y (encodeLeft x y before).2) ++
        (core.toList ++ (beforeLetters x y (encodeRight x y after).1 ++ (encodeRight x y after).2)) =
      before ++ (core.toList ++ after) := by
    rw [left_encoding, right_encoding]
  simpa only [List.append_assoc] using joined

def markedSource (x y : Nat) (before middle after : List Nat) : Word Nat :=
  Context.frame (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
    (render (value (Word.singleton x) (Word.singleton y))
      (renderLeft (value (Word.singleton x) (Word.singleton y))
        (anchor (Word.singleton x) (Word.singleton y)
          (joinGap (joinGap none
            (foldGap (value (Word.singleton x) (Word.singleton y)) (segments (encodeRight x y middle).1)))
            (contextWord (encodeRight x y middle).2)))
        (segments (encodeLeft x y before).2)) (segments (encodeRight x y after).1))

def squareBlocks (x y : Nat) (before middle after : List Nat) : Word Nat :=
  Context.frame (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
    (render (fun _ => square (Word.singleton x) (Word.singleton y))
      (renderLeft (fun _ => square (Word.singleton x) (Word.singleton y))
        (gap (square (Word.singleton x) (Word.singleton y))
          (joinGap (joinGap none
            (foldGap (fun _ => square (Word.singleton x) (Word.singleton y)) (segments (encodeRight x y middle).1)))
            (contextWord (encodeRight x y middle).2)) ++ square (Word.singleton x) (Word.singleton y))
        (segments (encodeLeft x y before).2)) (segments (encodeRight x y after).1))

theorem marked_source_eq (x y : Nat) (before middle after : List Nat) :
    markedSource x y before middle after =
      Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)) := by
  unfold markedSource
  rw [middle_encoding]
  exact exterior_rendering x y before after _

/-- Every marked occurrence in the actual three arbitrary lists is swept.
The codecs prove exact rendering and exclude x/y from all residual gaps.
Adjacent square blocks have not yet been coalesced into maximal factors. -/
theorem arbitrary_anchor_square_blocks (x y : Nat) (before middle after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (squareBlocks x y before middle after) := by
  have step := three_zone_square_blocks_context (Word.singleton x) (Word.singleton y)
    none (contextWord (encodeRight x y middle).2)
    (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
    (segments (encodeLeft x y before).2) (segments (encodeRight x y middle).1)
    (segments (encodeRight x y after).1)
  change Derives basis (markedSource x y before middle after) (squareBlocks x y before middle after) at step
  rw [marked_source_eq] at step
  exact step

theorem anchor_seed_square_blocks (x y : Nat) (word : Word Nat)
    (seed : HasAnchorSeed x y word) :
    ∃ before middle after : List Nat, Derives basis word (squareBlocks x y before middle after) := by
  obtain ⟨leftContext, rightContext, middle, step⟩ := seed
  have finish := arbitrary_anchor_square_blocks x y (contextLetters leftContext)
    (contextLetters middle) (contextLetters rightContext)
  simp only [contextWord_contextLetters] at finish
  exact ⟨contextLetters leftContext, contextLetters middle, contextLetters rightContext, step.trans finish⟩

/-- The actual symmetric C1/C2 relation now reaches all marked square blocks,
not merely an assumed marked representation or a bounded projection. -/
theorem related_square_blocks (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    (∃ before middle after : List Nat, Derives basis word (squareBlocks x y before middle after)) ∨
    (∃ before middle after : List Nat, Derives basis word (squareBlocks y x before middle after)) := by
  rcases related_has_anchor_seed x y word different xRepeated yRepeated related with forward | backward
  · exact Or.inl (anchor_seed_square_blocks x y word forward)
  · exact Or.inr (anchor_seed_square_blocks y x word backward)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.left_encoding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.right_encoding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.outside_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.outside_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.clean_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.clean_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.left_clean
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.right_clean
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.contextWord_contextLetters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.join_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.value_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.fold_before_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.render_before_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.render_after_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.middle_encoding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.exterior_rendering
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.marked_source_eq
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.arbitrary_anchor_square_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.anchor_seed_square_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MarkedZones.related_square_blocks
