import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedLayoutAction

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout

open MaximalFactors FactorContexts CrossFactor CrossSweep CrossLeftSweep
  AnchorPropagation MiddleSweep BinaryPowers MarkedZones OccurrenceWitnesses
  SquareCoalescing OrderedSquareForm LayoutAction SeparatorSkeleton

theorem render_layout (first second : Letter → Word Nat) (segments : List Segment)
    (images : ∀ letter, SameWordEffect (first letter) (second letter))
    {left right : Word Nat} (initial : SameWordEffect left right) :
    SameWordEffect (render first left segments) (render second right segments) := by
  induction segments generalizing left right with
  | nil => exact initial
  | cons item rest ih =>
      change SameWordEffect (render first (gap left item.1 ++ first item.2) rest)
        (render second (gap right item.1 ++ second item.2) rest)
      exact ih (word_append (word_gap initial (context_refl item.1)) (images item.2))

theorem renderLeft_layout (first second : Letter → Word Nat) (segments : List Segment)
    (images : ∀ letter, SameWordEffect (first letter) (second letter))
    {left right : Word Nat} (initial : SameWordEffect left right) :
    SameWordEffect (renderLeft first left segments) (renderLeft second right segments) := by
  induction segments with
  | nil => exact initial
  | cons item rest ih =>
      exact word_append (word_gap (images item.2) (context_refl item.1)) ih

theorem foldGap_layout (first second : Letter → Word Nat) (segments : List Segment)
    (images : ∀ letter, SameWordEffect (first letter) (second letter)) :
    SameContextEffect (foldGap first segments) (foldGap second segments) := by
  induction segments with
  | nil => exact context_refl none
  | cons item rest ih =>
      exact context_join (context_push (context_refl item.1) (images item.2)) ih

theorem anchor_square_layout (u v : Word Nat) {before after : Option (Word Nat)}
    (positiveU : Positive u) (positiveV : Positive v)
    (middle : SameContextEffect before after) :
    SameWordEffect (anchor u v before) (gap (square u v) after ++ square u v) := by
  have front : SameWordEffect (gap u before) (gap (square u v) after) :=
    word_gap (positive_words positiveU (positive_square positiveU positiveV)) middle
  have back : SameWordEffect (v ++ (v ++ u)) (square u v) :=
    positive_words (positive_append positiveV (positive_append positiveV positiveU))
      (positive_square positiveU positiveV)
  have step := word_append front back
  simpa only [anchor, Word.append_assoc] using step

theorem three_zone_layout (u v : Word Nat) (hGap kGap : Option (Word Nat))
    (before middle after : List Segment) (positiveU : Positive u) (positiveV : Positive v) :
    SameWordEffect
      (render (value u v)
        (renderLeft (value u v)
          (anchor u v (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)) before) after)
      (render (fun _ => square u v)
        (renderLeft (fun _ => square u v)
          (gap (square u v)
            (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) ++
              square u v) before) after) := by
  have images : ∀ letter, SameWordEffect (value u v letter) (square u v) := by
    intro letter
    exact positive_words (positive_value positiveU positiveV letter)
      (positive_square positiveU positiveV)
  have middleSame : SameContextEffect
      (joinGap (joinGap hGap (foldGap (value u v) middle)) kGap)
      (joinGap (joinGap hGap (foldGap (fun _ => square u v) middle)) kGap) :=
    context_join
      (context_join (context_refl hGap) (foldGap_layout _ _ middle images))
      (context_refl kGap)
  exact render_layout _ _ after images
    (renderLeft_layout _ _ before images
      (anchor_square_layout u v positiveU positiveV middleSame))

theorem arbitrary_anchor_square_layout (x y : Nat) (before middle after : List Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true) :
    SameWordEffect
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (squareBlocks x y before middle after) := by
  have step := word_frame
    (contextWord (encodeLeft x y before).1) (contextWord (encodeRight x y after).2)
    (three_zone_layout (Word.singleton x) (Word.singleton y)
      none (contextWord (encodeRight x y middle).2)
      (segments (encodeLeft x y before).2) (segments (encodeRight x y middle).1)
      (segments (encodeRight x y after).1)
      (positive_singleton x markedX) (positive_singleton y markedY))
  change SameWordEffect (markedSource x y before middle after)
    (squareBlocks x y before middle after) at step
  rw [marked_source_eq] at step
  exact step

theorem chain_layout {left right : Word Nat} (same : SameWordEffect left right)
    (gaps : List (List Nat)) : SameWordEffect (chain left gaps) (chain right gaps) := by
  induction gaps with
  | nil => exact same
  | cons letters rest ih =>
      exact word_append (word_gap same (context_refl (contextWord letters))) ih

theorem prefix_collapse_layout (block : Word Nat) (marked : Positive block)
    (gaps : List (List Nat)) :
    SameWordEffect (block ++ chain block gaps) (chain block gaps) := by
  cases gaps with
  | nil => exact positive_words (positive_append marked marked) marked
  | cons letters rest =>
      have step := word_append
        (word_gap (positive_words (positive_append marked marked) marked)
          (context_refl (contextWord letters))) (word_refl (chain block rest))
      simpa only [chain, prefixChain, gap_append, Word.append_assoc] using step

theorem coalesce_layout (block : Word Nat) (marked : Positive block)
    (gaps : List (List Nat)) :
    SameWordEffect (chain block gaps) (chain block (keepNonempty gaps)) := by
  induction gaps with
  | nil => exact word_refl block
  | cons letters rest ih =>
      cases letters with
      | nil =>
          change SameWordEffect (block ++ chain block rest) (chain block (keepNonempty rest))
          exact word_trans (word_append (word_refl block) ih)
            (prefix_collapse_layout block marked (keepNonempty rest))
      | cons first later =>
          exact word_append (word_refl (gap block (some ⟨first, later⟩))) ih

theorem square_coalesce_layout (x y : Nat) (before middle after : List Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true) :
    SameWordEffect (squareBlocks x y before middle after)
      (coalescedSquareBlocks x y before middle after) := by
  rw [squareBlocks_as_chain]
  unfold coalescedSquareBlocks
  exact word_frame _ _
    (coalesce_layout (square (Word.singleton x) (Word.singleton y))
      (positive_square (positive_singleton x markedX) (positive_singleton y markedY))
      (actualGaps x y before middle after))

theorem arbitrary_anchor_coalesced_layout (x y : Nat) (before middle after : List Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true) :
    SameWordEffect
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton y) (contextWord middle)))
      (coalescedSquareBlocks x y before middle after) :=
  word_trans (arbitrary_anchor_square_layout x y before middle after markedX markedY)
    (square_coalesce_layout x y before middle after markedX markedY)

theorem reorientation_layout (x y : Nat) (before middle after : List Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true) :
    SameWordEffect (coalescedSquareBlocks y x before middle after)
      (reorientedSquareBlocks x y before middle after) := by
  unfold coalescedSquareBlocks reorientedSquareBlocks
  exact word_frame _ _ (chain_layout
    (positive_words
      (positive_square (positive_singleton y markedY) (positive_singleton x markedX))
      (positive_square (positive_singleton x markedX) (positive_singleton y markedY))) _)

theorem c1_anchor_layout (u v : Word Nat) (middle : Option (Word Nat))
    (positiveU : Positive u) (positiveV : Positive v) :
    SameWordEffect (shortAnchor u v middle) (anchor u v middle) := by
  have step := word_append (word_refl (gap u middle))
    (positive_words (positive_append positiveV positiveU)
      (positive_append positiveV (positive_append positiveV positiveU)))
  simpa only [shortAnchor, anchor, Word.append_assoc] using step

theorem crossing_anchor_layout (u v : Word Nat) (hGap kGap tGap : Option (Word Nat))
    (positiveU : Positive u) (positiveV : Positive v) :
    SameWordEffect (crossing u v hGap kGap tGap)
      (anchor u v (crossingGap u hGap kGap tGap)) := by
  have first : SameWordEffect (gap u hGap ++ v) (gap u hGap ++ u) :=
    word_append (word_refl (gap u hGap)) (positive_words positiveV positiveU)
  have second : SameWordEffect
      (gap (gap u hGap ++ v) kGap ++ u) (gap (gap u hGap ++ u) kGap ++ u) :=
    word_append (word_gap first (context_refl kGap)) (word_refl u)
  have third := word_gap second (context_refl tGap)
  have back : SameWordEffect v (v ++ (v ++ u)) :=
    positive_words positiveV (positive_append positiveV (positive_append positiveV positiveU))
  have target : anchor u v (crossingGap u hGap kGap tGap) =
      gap (gap (gap u hGap ++ u) kGap ++ u) tGap ++ (v ++ (v ++ u)) := by
    unfold anchor crossingGap
    rw [gap_join, gap_push, gap_join, gap_push]
    simp only [Word.append_assoc]
  rw [target]
  exact word_append third back

/-- This seed includes the actual input's layout, not just an existential
derivation to an unconnected rendered anchor. -/
def PreservingSeed (x y : Nat) (word : Word Nat) : Prop :=
  ∃ before after middle : Option (Word Nat),
    Derives basis word (Context.frame before after
      (anchor (Word.singleton x) (Word.singleton y) middle)) ∧
    SameWordEffect word (Context.frame before after
      (anchor (Word.singleton x) (Word.singleton y) middle))

theorem c1_preserving_seed (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (repeated : 2 ≤ word.toList.count y)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true)
    (occurs : C1 x y word.toList) : PreservingSeed x y word := by
  obtain ⟨before, middle, after, split, step⟩ :=
    c1_seed_from_occurrences x y word different repeated occurs
  refine ⟨contextWord before, contextWord after, contextWord middle, step, ?_⟩
  rw [c1_word_as_frame x y word before middle after split]
  exact word_frame _ _ (c1_anchor_layout (Word.singleton x) (Word.singleton y)
    (contextWord middle) (positive_singleton x markedX) (positive_singleton y markedY))

theorem c2_preserving_seed (x y : Nat) (word : Word Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true)
    (occurs : C2 x y word.toList) : PreservingSeed x y word := by
  obtain ⟨before, first, second, third, after, split, step⟩ :=
    c2_seed_from_occurrences x y word occurs
  refine ⟨contextWord before, contextWord after,
    crossingGap (Word.singleton x) (contextWord first) (contextWord second) (contextWord third),
    step, ?_⟩
  rw [c2_word_as_frame x y word before first second third after split]
  exact word_frame _ _ (crossing_anchor_layout (Word.singleton x) (Word.singleton y)
    (contextWord first) (contextWord second) (contextWord third)
    (positive_singleton x markedX) (positive_singleton y markedY))

theorem related_preserving_seed (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true)
    (xRepeated : 2 ≤ word.toList.count x) (yRepeated : 2 ≤ word.toList.count y)
    (related : PairRelated x y word.toList) :
    PreservingSeed x y word ∨ PreservingSeed y x word := by
  rcases related with first | second | third | fourth
  · exact Or.inl (c1_preserving_seed x y word different yRepeated markedX markedY first)
  · exact Or.inr (c1_preserving_seed y x word (Ne.symm different) xRepeated markedY markedX second)
  · exact Or.inl (c2_preserving_seed x y word markedX markedY third)
  · exact Or.inr (c2_preserving_seed y x word markedY markedX fourth)

theorem seed_coalesced_layout (x y : Nat) (word : Word Nat)
    (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true)
    (seed : PreservingSeed x y word) :
    ∃ before middle after : List Nat,
      Derives basis word (coalescedSquareBlocks x y before middle after) ∧
      SameWordEffect word (coalescedSquareBlocks x y before middle after) := by
  obtain ⟨before, after, middle, originalStep, originalLayout⟩ := seed
  have step : Derives basis
      (Context.frame before after (anchor (Word.singleton x) (Word.singleton y) middle))
      (coalescedSquareBlocks x y (contextLetters before) (contextLetters middle) (contextLetters after)) := by
    simpa only [contextWord_contextLetters] using
      arbitrary_anchor_coalesced x y (contextLetters before) (contextLetters middle) (contextLetters after)
  have same : SameWordEffect
      (Context.frame before after (anchor (Word.singleton x) (Word.singleton y) middle))
      (coalescedSquareBlocks x y (contextLetters before) (contextLetters middle) (contextLetters after)) := by
    simpa only [contextWord_contextLetters] using
      arbitrary_anchor_coalesced_layout x y (contextLetters before) (contextLetters middle)
        (contextLetters after) markedX markedY
  exact ⟨contextLetters before, contextLetters middle, contextLetters after,
    originalStep.trans step, word_trans originalLayout same⟩

theorem related_perfect_layout (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (markedX : binaryTag 0 1 x = true) (markedY : binaryTag 0 1 y = true)
    (xRepeated : 2 ≤ word.toList.count x) (yRepeated : 2 ≤ word.toList.count y)
    (related : PairRelated x y word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ BinaryPerfect.Perfect x y normal ∧
      SameWordEffect word normal := by
  rcases related_preserving_seed x y word different markedX markedY xRepeated yRepeated related with forward | backward
  · obtain ⟨before, middle, after, step, same⟩ := seed_coalesced_layout x y word markedX markedY forward
    exact ⟨coalescedSquareBlocks x y before middle after, step,
      BinaryPerfect.coalesced_perfect x y before middle after, same⟩
  · obtain ⟨before, middle, after, step, same⟩ := seed_coalesced_layout y x word markedY markedX backward
    exact ⟨reorientedSquareBlocks x y before middle after,
      step.trans (coalesced_reorient x y before middle after),
      BinaryPerfect.reoriented_perfect x y before middle after,
      word_trans same (reorientation_layout x y before middle after markedX markedY)⟩

/-- The actual unrestricted binary-perfect construction now retains every
original complementary factor and every positive factor slot. -/
theorem binary_perfect_skeleton (word : Word Nat)
    (zeroRepeated : 2 ≤ word.toList.count 0) (oneRepeated : 2 ≤ word.toList.count 1)
    (related : PairRelated 0 1 word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ BinaryPerfect.Perfect 0 1 normal ∧
      canonicalSkeleton word.toList = canonicalSkeleton normal.toList := by
  obtain ⟨normal, step, perfect, same⟩ :=
    related_perfect_layout 0 1 word (by decide) (by decide) (by decide)
      zeroRepeated oneRepeated related
  exact ⟨normal, step, perfect, word_skeleton same⟩

theorem expanded_perfect_skeleton (word : Word Nat) (related : PairRelated 0 1 word.toList) :
    ∃ normal : Word Nat, Derives basis (MacroExpansion.expandWord word) normal ∧
      BinaryPerfect.Perfect 0 1 normal ∧
      canonicalSkeleton word.toList = canonicalSkeleton normal.toList := by
  have ready := MacroExpansion.expanded_ready word related
  obtain ⟨normal, step, perfect, same⟩ :=
    binary_perfect_skeleton (MacroExpansion.expandWord word) ready.2.1 ready.2.2 ready.1
  exact ⟨normal, step, perfect, (skeleton_expandWord word).symm.trans same⟩

open BlockAlignment OccurrenceMacro MacroWitnesses

/-- Genuine disjoint-root hypotheses yield a decoded derivation and a binary
perfect macro normal with the ORIGINAL macro separator skeleton preserved. -/
theorem generalized_preserving_macro_perfect (leftRoot rightRoot word : Word Nat)
    (apart : ∀ value ∈ leftRoot.toList, value ∉ rightRoot.toList)
    (leftPerfect : CanonicalPerfect leftRoot word)
    (rightPerfect : CanonicalPerfect rightRoot word)
    (related : GeneralizedRelated leftRoot rightRoot word) :
    ∃ normal : Word Nat,
      Derives basis word (normal.bind (image leftRoot rightRoot)) ∧
      BinaryPerfect.Perfect 0 1 normal ∧
      canonicalSkeleton (macroWord leftRoot rightRoot word apart leftPerfect rightPerfect).toList =
        canonicalSkeleton normal.toList := by
  let codes : Word Nat := macroWord leftRoot rightRoot word apart leftPerfect rightPerfect
  have macroRelated : PairRelated 0 1 codes.toList :=
    generalized_related_macroWord leftRoot rightRoot word apart leftPerfect rightPerfect related
  obtain ⟨normal, step, perfect, same⟩ := expanded_perfect_skeleton codes macroRelated
  have roundtrip : codes.bind (image leftRoot rightRoot) = word :=
    macroWord_bind leftRoot rightRoot word apart leftPerfect rightPerfect
  have first : Derives basis word ((MacroExpansion.expandWord codes).bind (image leftRoot rightRoot)) := by
    have raw := MacroExpansion.expansion_derives leftRoot rightRoot codes
    rw [roundtrip] at raw
    exact raw
  exact ⟨normal, first.trans (Derives.subst step (image leftRoot rightRoot)), perfect, same⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.render_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.renderLeft_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.foldGap_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.anchor_square_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.three_zone_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.arbitrary_anchor_square_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.chain_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.prefix_collapse_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.coalesce_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.square_coalesce_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.arbitrary_anchor_coalesced_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.reorientation_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.c1_anchor_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.crossing_anchor_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.c1_preserving_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.c2_preserving_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.related_preserving_seed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.seed_coalesced_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.related_perfect_layout
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.binary_perfect_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.expanded_perfect_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.NormalizerLayout.generalized_preserving_macro_perfect
