import SemigroupBasis.CoRoots.S5_626FactorBridge

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis

/-- One left-to-right first-occurrence segment.  `marker` is the new first
occurrence and `parity` is the duplicate-free, marker-order-sorted parity
block following it and preceding the next marker. -/
structure FirstParitySegment where
  marker : Nat
  parity : List Nat
deriving Repr, DecidableEq

/-- Toggle `letter` in a parity block and restore the order inherited from
the already-seen marker list. -/
def orderedParityToggle
    (seen : List Nat) (letter : Nat) (parity : List Nat) : List Nat :=
  seen.filter fun tested =>
    decide ((tested = letter) != (tested ∈ parity))

theorem orderedParityToggle_nodup
    {seen : List Nat} (seenNodup : seen.Nodup)
    (letter : Nat) (parity : List Nat) :
    (orderedParityToggle seen letter parity).Nodup := by
  exact seenNodup.filter _

/-- Scan one word from left to right.  A fresh letter closes the current
segment.  An old letter toggles only the current segment, so no rewrite or
combinatorial update crosses the next first-occurrence marker. -/
def segmentedParityScanAux
    (seen : List Nat) (completed : List FirstParitySegment)
    (current : FirstParitySegment) :
    List Nat → List FirstParitySegment
  | [] => completed ++ [current]
  | letter :: rest =>
      if letter ∈ seen then
        segmentedParityScanAux seen completed
          ⟨current.marker,
            orderedParityToggle seen letter current.parity⟩ rest
      else
        segmentedParityScanAux (seen ++ [letter])
          (completed ++ [current]) ⟨letter, []⟩ rest

def segmentedParityScan (word : Word Nat) : List FirstParitySegment :=
  segmentedParityScanAux [word.head] [] ⟨word.head, []⟩ word.tail

private theorem segmentedParityScanAux_ne_nil
    (seen : List Nat) (completed : List FirstParitySegment)
    (current : FirstParitySegment) :
    ∀ letters,
      segmentedParityScanAux seen completed current letters ≠ []
  | [] => by simp [segmentedParityScanAux]
  | letter :: rest => by
      simp only [segmentedParityScanAux]
      split
      · exact segmentedParityScanAux_ne_nil _ _ _ rest
      · exact segmentedParityScanAux_ne_nil _ _ _ rest

theorem segmentedParityScan_ne_nil (word : Word Nat) :
    segmentedParityScan word ≠ [] :=
  segmentedParityScanAux_ne_nil _ _ _ _

private theorem segmentedParityScanAux_completed_prefix
    (seen : List Nat) (completed : List FirstParitySegment)
    (current : FirstParitySegment) :
    ∀ letters,
      ∃ suffix,
        segmentedParityScanAux seen completed current letters =
          completed ++ suffix
  | [] => ⟨[current], by simp [segmentedParityScanAux]⟩
  | letter :: rest => by
      simp only [segmentedParityScanAux]
      split
      · exact segmentedParityScanAux_completed_prefix _ _ _ rest
      · obtain ⟨suffix, shape⟩ :=
          segmentedParityScanAux_completed_prefix
            (seen ++ [letter]) (completed ++ [current])
            ⟨letter, []⟩ rest
        refine ⟨current :: suffix, ?_⟩
        rw [shape]
        simp [List.append_assoc]

private theorem segmentedParityScanAux_first_marker
    (seen : List Nat) (current : FirstParitySegment) :
    ∀ letters,
      ∃ parity rest,
        segmentedParityScanAux seen [] current letters =
          ⟨current.marker, parity⟩ :: rest
  | [] => ⟨current.parity, [], by simp [segmentedParityScanAux]⟩
  | letter :: rest => by
      simp only [segmentedParityScanAux]
      split
      · simpa using
          segmentedParityScanAux_first_marker seen
            ⟨current.marker,
              orderedParityToggle seen letter current.parity⟩ rest
      · obtain ⟨suffix, shape⟩ :=
          segmentedParityScanAux_completed_prefix
            (seen ++ [letter]) [current] ⟨letter, []⟩ rest
        refine ⟨current.parity, suffix, ?_⟩
        simpa using shape

theorem segmentedParityScan_first_marker (word : Word Nat) :
    ∃ parity rest,
      segmentedParityScan word =
        ⟨word.head, parity⟩ :: rest :=
  segmentedParityScanAux_first_marker
    [word.head] ⟨word.head, []⟩ word.tail

def renderFirstParitySegments :
    List FirstParitySegment → List Nat
  | [] => []
  | segment :: rest =>
      segment.marker ::
        (segment.parity ++ renderFirstParitySegments rest)

theorem renderFirstParitySegments_ne_nil
    {segments : List FirstParitySegment}
    (nonempty : segments ≠ []) :
    renderFirstParitySegments segments ≠ [] := by
  cases segments with
  | nil => contradiction
  | cons segment rest =>
      simp [renderFirstParitySegments]

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

private theorem wordOfListOr_toList
    (fallback : Nat) {letters : List Nat}
    (nonempty : letters ≠ []) :
    (wordOfListOr fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

/-- The parity-only segmented representative.  It can accidentally make a
repeated odd initial variable look simple; `needsInitialRepair` detects
exactly that threshold-loss branch. -/
def segmentedParityBaseWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head <|
    renderFirstParitySegments (segmentedParityScan word)

theorem segmentedParityBaseWord_toList (word : Word Nat) :
    (segmentedParityBaseWord word).toList =
      renderFirstParitySegments (segmentedParityScan word) := by
  apply wordOfListOr_toList
  exact renderFirstParitySegments_ne_nil
    (segmentedParityScan_ne_nil word)

theorem segmentedParityBaseWord_head (word : Word Nat) :
    (segmentedParityBaseWord word).head = word.head := by
  obtain ⟨parity, rest, scanShape⟩ :=
    segmentedParityScan_first_marker word
  have rendered := segmentedParityBaseWord_toList word
  rw [scanShape] at rendered
  have heads := congrArg List.head? rendered
  simpa [Word.toList, renderFirstParitySegments] using heads

def needsInitialRepair (word : Word Nat) : Prop :=
  ¬ InitialOccursExactlyOnce word ∧
    InitialOccursExactlyOnce (segmentedParityBaseWord word)

private instance needsInitialRepair_decidable (word : Word Nat) :
    Decidable (needsInitialRepair word) := by
  unfold needsInitialRepair InitialOccursExactlyOnce
  infer_instance

/-- Install the neutral pair immediately after the initial marker.  The
pair is therefore protected before every later first-occurrence marker. -/
def repairInitialList (fallback : Nat) : List Nat → List Nat
  | [] => [fallback, fallback, fallback]
  | marker :: rest => marker :: marker :: marker :: rest

theorem repairInitialList_cons
    (marker : Nat) (rest : List Nat) :
    repairInitialList marker (marker :: rest) =
      marker :: marker :: marker :: rest := rfl

/-- Adding the protected pair does not change any total parity coordinate. -/
theorem repairInitialList_count_mod_two
    (fallback tested marker : Nat) (rest : List Nat) :
    (repairInitialList fallback (marker :: rest)).count tested % 2 =
      (marker :: rest).count tested % 2 := by
  by_cases same : marker = tested
  · subst marker
    simp [repairInitialList]
    omega
  · simp [repairInitialList, same]

/-- The repair pair is syntactically before the entire suffix containing all
later markers.  This is the no-marker-crossing placement invariant. -/
theorem repairInitialList_before_later_markers
    (fallback marker : Nat) (rest : List Nat) :
    ∃ suffix,
      repairInitialList fallback (marker :: rest) =
        marker :: marker :: marker :: suffix ∧
      suffix = rest :=
  ⟨rest, rfl, rfl⟩

def segmentedParityNormalWord (word : Word Nat) : Word Nat :=
  if needsInitialRepair word then
    wordOfListOr word.head <|
      repairInitialList word.head
        (segmentedParityBaseWord word).toList
  else segmentedParityBaseWord word

theorem segmentedParityNormalWord_of_no_repair
    (word : Word Nat) (noRepair : ¬ needsInitialRepair word) :
    segmentedParityNormalWord word =
      segmentedParityBaseWord word := by
  simp [segmentedParityNormalWord, noRepair]

theorem segmentedParityNormalWord_of_repair
    (word : Word Nat) (repair : needsInitialRepair word) :
    segmentedParityNormalWord word =
      wordOfListOr word.head
        (repairInitialList word.head
          (segmentedParityBaseWord word).toList) := by
  simp [segmentedParityNormalWord, repair]

theorem segmentedParityNormalWord_of_repair_target
    (word : Word Nat) (repair : needsInitialRepair word) :
    segmentedParityNormalWord word =
      ((Word.singleton word.head ++ Word.singleton word.head) ++
        segmentedParityBaseWord word) := by
  have baseHead := segmentedParityBaseWord_head word
  cases baseShape : segmentedParityBaseWord word with
  | mk head tail =>
      rw [baseShape] at baseHead
      change head = word.head at baseHead
      subst head
      rw [segmentedParityNormalWord_of_repair word repair]
      apply Word.toList_injective
      simp only [Word.toList_append, Word.toList_singleton]
      simp [baseShape, Word.toList, wordOfListOr, repairInitialList]

def initialTriplePrefix (initial : Nat) : Word Nat :=
  (Word.singleton initial ++ Word.singleton initial) ++
    Word.singleton initial

def initialFivePrefix (initial : Nat) : Word Nat :=
  (((Word.singleton initial ++ Word.singleton initial) ++
      Word.singleton initial) ++ Word.singleton initial) ++
    Word.singleton initial

/-- Once a repeated odd initial is held as a triple, every suffix derivation
can be performed without moving the pair across a later marker. -/
theorem derivesUnderProtectedInitial
    (initial : Nat) {left right : Word Nat}
    (derivation : Derives basis left right) :
    Derives basis
      (initialTriplePrefix initial ++ left)
      (initialTriplePrefix initial ++ right) :=
  Derives.prepend (initialTriplePrefix initial) derivation

/-- The odd initial cap `x^3 = x^5` is available under an arbitrary nonempty
suffix while the neutral pair remains before that suffix. -/
theorem derivesProtectedInitialPairExpansion
    (initial : Nat) (suffix : Word Nat) :
    Derives basis
      (initialTriplePrefix initial ++ suffix)
      (initialFivePrefix initial ++ suffix) := by
  have expanded :=
    Derives.appendRight
      (derivesOddNeutralPairExpansion (Word.singleton initial)) suffix
  simpa [initialTriplePrefix, initialFivePrefix,
    Word.append_assoc] using expanded

theorem derivesProtectedInitialPairContraction
    (initial : Nat) (suffix : Word Nat) :
    Derives basis
      (initialFivePrefix initial ++ suffix)
      (initialTriplePrefix initial ++ suffix) :=
  Derives.symm (derivesProtectedInitialPairExpansion initial suffix)

/-- Normalize a two-marker parity block by swapping its two adjacent old
letters before a fixed suffix.  The suffix can begin with the next marker. -/
theorem derivesTwoMarkerBlockSwap
    (first second suffix : Word Nat) :
    Derives basis
      (((((first ++ second) ++ first) ++ second) ++ suffix))
      (((((first ++ second) ++ second) ++ first) ++ suffix)) := by
  exact Derives.appendRight
    (derivesSystemThreeSwap first second) suffix

/-- Swap the first two guarded letters after a three-block prefix, without
crossing the supplied suffix. -/
theorem derivesThreeMarkerBlockSwapY
    (first second guard suffix : Word Nat) :
    Derives basis
      ((((((first ++ second) ++ guard) ++ first) ++ second) ++ suffix))
      ((((((first ++ second) ++ guard) ++ second) ++ first) ++ suffix)) := by
  exact Derives.appendRight
    (derivesTernarySwapY first second guard) suffix

/-- Swap the first and guard letters after a three-block prefix, without
crossing the supplied suffix. -/
theorem derivesThreeMarkerBlockSwapZ
    (first second guard suffix : Word Nat) :
    Derives basis
      ((((((first ++ second) ++ guard) ++ first) ++ guard) ++ suffix))
      ((((((first ++ second) ++ guard) ++ guard) ++ first) ++ suffix)) := by
  exact Derives.appendRight
    (derivesTernarySwapZ first second guard) suffix

/-- Contract a guarded neutral pair at the end of one segment.  `suffix` is
kept fixed, so this local step cannot cross its next marker. -/
theorem derivesGuardedSegmentPairContraction
    (before letter guard suffix : Word Nat) :
    Derives basis
      ((((((before ++ letter) ++ guard) ++ letter) ++ letter) ++ suffix))
      ((((before ++ letter) ++ guard) ++ suffix)) := by
  exact Derives.appendRight
    (Derives.symm <|
      derivesMarkerSquareLift before letter guard) suffix

/- This module stops at the scan, target shape, and fixed-suffix rewrites.
`S5_626SegmentInduction` supplies the context-uniform affine simulation and
protected-pair extraction; `S5_626AffineBridge` and
`S5_626Completeness` build the later semantic and completeness layers. -/

end SemigroupBasis.CoRoots.S5_626
