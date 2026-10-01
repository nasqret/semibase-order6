import SemigroupBasis.CoRoots.S5_415AnchoredNormalForm

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- Convert a possibly empty list into an optional nonempty word. -/
def optionalWordOfList : List Nat → Option (Word Nat)
  | [] => none
  | head :: tail => some ⟨head, tail⟩

def optionalWordLetters : Option (Word Nat) → List Nat
  | none => []
  | some word => word.toList

@[simp]
theorem optionalWordLetters_optionalWordOfList (letters : List Nat) :
    optionalWordLetters (optionalWordOfList letters) = letters := by
  cases letters <;> rfl

/-- A nonempty list of segments represented without a dependent type. The
segments are the pieces obtained by splitting a tail at copies of its head
letter. -/
structure HeadSegments where
  first : List Nat
  rest : List (List Nat)
deriving Repr, DecidableEq

def HeadSegments.toList (segments : HeadSegments) : List (List Nat) :=
  segments.first :: segments.rest

/-- Structurally split a list at every occurrence of `anchor`. Processing
from right to left keeps the recursion directly structural. -/
def splitHeadSegments (anchor : Nat) : List Nat → HeadSegments
  | [] => ⟨[], []⟩
  | letter :: letters =>
      let suffix := splitHeadSegments anchor letters
      if letter = anchor then
        ⟨[], suffix.first :: suffix.rest⟩
      else
        ⟨letter :: suffix.first, suffix.rest⟩

def renderHeadSegments (anchor : Nat) (segments : HeadSegments) :
    List Nat :=
  segments.first ++
    segments.rest.flatMap fun segment => anchor :: segment

/-- Splitting at the head letter loses no list data. -/
theorem renderHeadSegments_splitHeadSegments (anchor : Nat) :
    ∀ letters : List Nat,
      renderHeadSegments anchor (splitHeadSegments anchor letters) =
        letters
  | [] => rfl
  | letter :: letters => by
      by_cases same : letter = anchor
      · subst letter
        rw [splitHeadSegments, if_pos rfl]
        change
          anchor ::
              renderHeadSegments anchor
                (splitHeadSegments anchor letters) =
            anchor :: letters
        exact congrArg (fun suffix => anchor :: suffix)
          (renderHeadSegments_splitHeadSegments anchor letters)
      · rw [splitHeadSegments, if_neg same]
        change
          letter ::
              renderHeadSegments anchor
                (splitHeadSegments anchor letters) =
            letter :: letters
        exact congrArg (fun suffix => letter :: suffix)
          (renderHeadSegments_splitHeadSegments anchor letters)

/-- All but the final segment are closed excursions from the head anchor. -/
def closedHeadGaps : List (List Nat) → List (Option (Word Nat))
  | [] => []
  | [_] => []
  | segment :: next :: rest =>
      optionalWordOfList segment :: closedHeadGaps (next :: rest)

def trailingHeadSegment : List (List Nat) → List Nat
  | [] => []
  | [segment] => segment
  | _ :: next :: rest => trailingHeadSegment (next :: rest)

private theorem renderClosedHeadGaps (anchor : Nat) :
    ∀ segments : List (List Nat),
      (closedHeadGaps segments).flatMap
          (fun gap => optionalWordLetters gap ++ [anchor]) ++
          trailingHeadSegment segments =
        match segments with
        | [] => []
        | first :: rest =>
            first ++ rest.flatMap (fun segment => anchor :: segment)
  | [] => rfl
  | [segment] => by
      simp [closedHeadGaps, trailingHeadSegment]
  | segment :: next :: rest => by
      simpa [closedHeadGaps, trailingHeadSegment,
        renderClosedHeadGaps anchor (next :: rest),
        List.append_assoc]

private theorem anchoredGapWalk_singleton_toList (anchor : Nat) :
    ∀ gaps : List (Option (Word Nat)),
      (anchoredGapWalk (Word.singleton anchor) gaps).toList =
        [anchor] ++
          gaps.flatMap
            (fun gap => optionalWordLetters gap ++ [anchor])
  | [] => by simp [anchoredGapWalk]
  | gap :: rest => by
      cases gap with
      | none =>
          simpa only [anchoredGapWalk, Word.toList_append,
            Word.toList_singleton, List.flatMap_cons, optionalWordLetters,
            anchoredGapWalk_singleton_toList anchor rest,
            List.nil_append, List.append_assoc]
      | some excursion =>
          simpa only [anchoredGapWalk, Word.toList_append,
            Word.toList_singleton, List.flatMap_cons, optionalWordLetters,
            anchoredGapWalk_singleton_toList anchor rest,
            List.append_assoc]

/-- Append a possibly empty raw trailing segment to a nonempty prefix. -/
def appendTrailingLetters (baseWord : Word Nat) : List Nat → Word Nat
  | [] => baseWord
  | head :: tail => baseWord ++ ⟨head, tail⟩

@[simp]
theorem appendTrailingLetters_head
    (baseWord : Word Nat) (letters : List Nat) :
    (appendTrailingLetters baseWord letters).head = baseWord.head := by
  cases letters <;> rfl

@[simp]
theorem appendTrailingLetters_toList
    (baseWord : Word Nat) (letters : List Nat) :
    (appendTrailingLetters baseWord letters).toList =
      baseWord.toList ++ letters := by
  cases letters with
  | nil => simp [appendTrailingLetters]
  | cons head tail =>
      simp [appendTrailingLetters, Word.toList_append, Word.toList]

theorem derivesAppendTrailingLetters
    {source target : Word Nat} (derivation : Derives basis source target)
    (letters : List Nat) :
    Derives basis
      (appendTrailingLetters source letters)
      (appendTrailingLetters target letters) := by
  cases letters with
  | nil => simpa [appendTrailingLetters] using derivation
  | cons head tail =>
      simpa [appendTrailingLetters] using
        Derives.appendRight derivation ⟨head, tail⟩

def headSegmentLists (word : Word Nat) : List (List Nat) :=
  (splitHeadSegments word.head word.tail).toList

def headExcursions (word : Word Nat) : List (Option (Word Nat)) :=
  closedHeadGaps (headSegmentLists word)

def headTrailingSegment (word : Word Nat) : List Nat :=
  trailingHeadSegment (headSegmentLists word)

/-- Exact reconstruction of an arbitrary word as optional excursions from
its singleton head anchor followed by a raw trailing segment. -/
def headAnchoredRebuild (word : Word Nat) : Word Nat :=
  appendTrailingLetters
    (anchoredGapWalk (Word.singleton word.head) (headExcursions word))
    (headTrailingSegment word)

theorem headAnchoredRebuild_eq (word : Word Nat) :
    headAnchoredRebuild word = word := by
  apply Word.toList_injective
  rw [headAnchoredRebuild, appendTrailingLetters_toList,
    anchoredGapWalk_singleton_toList]
  have rendered :=
    renderClosedHeadGaps word.head (headSegmentLists word)
  simp only [headExcursions, headTrailingSegment]
  rw [List.append_assoc, rendered]
  simp only [headSegmentLists, HeadSegments.toList,
    List.singleton_append]
  change
    word.head ::
        renderHeadSegments word.head
          (splitHeadSegments word.head word.tail) =
      word.toList
  rw [renderHeadSegments_splitHeadSegments]
  rfl

/-- The one-level structural measure: duplicate closed excursions at the
current head anchor. Recursive descent will use word length as its outer
fuel and this measure as local progress. -/
def headAnchoredDuplicateMeasure (word : Word Nat) : Nat :=
  anchoredGapDuplicateMeasure (headExcursions word)

/-- A total normalization pass on an arbitrary word. It canonicalizes the
closed excursions at the head anchor and leaves the trailing segment intact.
Nested excursion normalization is deliberately a separate recursion layer. -/
def normalizeHeadAnchoredWord (word : Word Nat) : Word Nat :=
  appendTrailingLetters
    (anchoredGapWalk (Word.singleton word.head)
      (normalizeAnchoredGaps (headExcursions word)))
    (headTrailingSegment word)

/-- Every word derives to its total one-level head-anchored normalization. -/
theorem derivesNormalizeHeadAnchoredWord (word : Word Nat) :
    Derives basis word (normalizeHeadAnchoredWord word) := by
  have normalized :
      Derives basis (headAnchoredRebuild word)
        (normalizeHeadAnchoredWord word) := by
    simpa [headAnchoredRebuild, normalizeHeadAnchoredWord] using
      derivesAppendTrailingLetters
        (derivesNormalizeAnchoredGaps
          (Word.singleton word.head) (headExcursions word))
        (headTrailingSegment word)
  simpa only [headAnchoredRebuild_eq] using normalized

/-- Algebraic closure of the one-level decomposition. Once two words have
the same literal head anchor, the same trailing segment, and the same set of
optional closed excursions, the three Brandt laws derive one from the other.
The remaining global problem is therefore the combinatorial alignment of
these data from `SameBrandtSignature`. -/
theorem derivesOfSameHeadExcursionDecomposition
    {left right : Word Nat}
    (sameHead : left.head = right.head)
    (sameTrailing :
      headTrailingSegment left = headTrailingSegment right)
    (sameExcursions :
      ∀ gap, gap ∈ headExcursions left ↔
        gap ∈ headExcursions right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at sameHead
          subst rightHead
          have aligned :=
            derivesAppendTrailingLetters
              (derivesAnchoredGapWalkOfSameSupport
                (Word.singleton leftHead) sameExcursions)
              (headTrailingSegment ⟨leftHead, leftTail⟩)
          have rebuilt :
              Derives basis
                (headAnchoredRebuild ⟨leftHead, leftTail⟩)
                (headAnchoredRebuild ⟨leftHead, rightTail⟩) := by
            simpa [headAnchoredRebuild, sameTrailing] using aligned
          simpa only [headAnchoredRebuild_eq] using rebuilt

/-! ## Fuel-indexed recursive normalization -/

/-- The outer structural measure for recursive normalization. Every genuine
head excursion and trailing subword is shorter than its parent; using the
whole word length as fuel makes the recursion total without hiding a
termination assumption. -/
def recursiveBrandtMeasure (word : Word Nat) : Nat :=
  word.toList.length

/-- Recursively normalize every nonempty closed head excursion and the
trailing subword, then eliminate duplicate optional excursions at the current
anchor. Recursion is structural on `fuel`. -/
def normalizeBrandtFuel : Nat → Word Nat → Word Nat
  | 0, word => word
  | fuel + 1, word =>
      let mappedGaps :=
        (headExcursions word).map
          (Option.map (normalizeBrandtFuel fuel))
      let normalizedPrefix :=
        anchoredGapWalk (Word.singleton word.head)
          (normalizeAnchoredGaps mappedGaps)
      match headTrailingSegment word with
      | [] => normalizedPrefix
      | head :: tail =>
          normalizedPrefix ++
            normalizeBrandtFuel fuel ⟨head, tail⟩

@[simp]
theorem normalizeBrandtFuel_head :
    ∀ (fuel : Nat) (word : Word Nat),
      (normalizeBrandtFuel fuel word).head = word.head
  | 0, word => rfl
  | fuel + 1, word => by
      cases trailing : headTrailingSegment word with
      | nil =>
          simp [normalizeBrandtFuel, trailing]
      | cons head tail =>
          simp [normalizeBrandtFuel, trailing]

/-- Soundness of every finite recursive normalization depth. -/
theorem derivesNormalizeBrandtFuel :
    ∀ (fuel : Nat) (word : Word Nat),
      Derives basis word (normalizeBrandtFuel fuel word)
  | 0, word => Derives.refl word
  | fuel + 1, word => by
      let mappedGaps :=
        (headExcursions word).map
          (Option.map (normalizeBrandtFuel fuel))
      let normalizedPrefix :=
        anchoredGapWalk (Word.singleton word.head)
          (normalizeAnchoredGaps mappedGaps)
      have mapExcursions :
          Derives basis
            (anchoredGapWalk (Word.singleton word.head)
              (headExcursions word))
            (anchoredGapWalk (Word.singleton word.head) mappedGaps) := by
        simpa [mappedGaps] using
          derivesAnchoredGapWalkMap
            (Word.singleton word.head)
            (normalizeBrandtFuel fuel)
            (fun excursion =>
              derivesNormalizeBrandtFuel fuel excursion)
            (headExcursions word)
      have deduplicateExcursions :
          Derives basis
            (anchoredGapWalk (Word.singleton word.head) mappedGaps)
            normalizedPrefix := by
        simpa [normalizedPrefix] using
          derivesNormalizeAnchoredGaps
            (Word.singleton word.head) mappedGaps
      have normalizePrefix :=
        mapExcursions.trans deduplicateExcursions
      have rebuildToPrefix :
          Derives basis word
            (appendTrailingLetters normalizedPrefix
              (headTrailingSegment word)) := by
        have fromRebuild :
            Derives basis (headAnchoredRebuild word)
              (appendTrailingLetters normalizedPrefix
                (headTrailingSegment word)) := by
          simpa [headAnchoredRebuild] using
            derivesAppendTrailingLetters normalizePrefix
              (headTrailingSegment word)
        simpa only [headAnchoredRebuild_eq] using fromRebuild
      cases trailing : headTrailingSegment word with
      | nil =>
          simpa [normalizeBrandtFuel, mappedGaps,
            normalizedPrefix, trailing, appendTrailingLetters] using
            rebuildToPrefix
      | cons head tail =>
          have normalizeTrailing :=
            Derives.prepend normalizedPrefix
              (derivesNormalizeBrandtFuel fuel ⟨head, tail⟩)
          exact rebuildToPrefix.trans <| by
            simpa [normalizeBrandtFuel, mappedGaps,
              normalizedPrefix, trailing, appendTrailingLetters] using
                normalizeTrailing

/-- The total recursive anchored-excursion normalizer, using word length as
its normalization depth. -/
def normalizeBrandtWord (word : Word Nat) : Word Nat :=
  normalizeBrandtFuel (recursiveBrandtMeasure word) word

@[simp]
theorem normalizeBrandtWord_head (word : Word Nat) :
    (normalizeBrandtWord word).head = word.head := by
  simp [normalizeBrandtWord]

theorem derivesNormalizeBrandtWord (word : Word Nat) :
    Derives basis word (normalizeBrandtWord word) := by
  exact derivesNormalizeBrandtFuel (recursiveBrandtMeasure word) word

/-- Once endpoint-component alignment has been realized as a common literal
head decomposition, the anchored permutation and multiplicity lemmas close
the normalized derivation. -/
theorem derivesNormalizedWordsOfAlignedDecomposition
    {left right : Word Nat}
    (sameHead :
      (normalizeBrandtWord left).head =
        (normalizeBrandtWord right).head)
    (sameTrailing :
      headTrailingSegment (normalizeBrandtWord left) =
        headTrailingSegment (normalizeBrandtWord right))
    (sameExcursions :
      ∀ gap,
        gap ∈ headExcursions (normalizeBrandtWord left) ↔
          gap ∈ headExcursions (normalizeBrandtWord right)) :
    Derives basis (normalizeBrandtWord left)
      (normalizeBrandtWord right) :=
  derivesOfSameHeadExcursionDecomposition
    sameHead sameTrailing sameExcursions

end SemigroupBasis.CoRoots.S5_415
