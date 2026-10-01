import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank088
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_240
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# An unrestricted first-order / initial-endpoint seed for rank 088

The independently kernel-green `S3_16` detector fixes the COMPLETE
first-occurrence sequence. Independent direct `S5_240` completeness, applied
to reversed words, fixes singleton state, a globally unique initial variable,
and a globally simple ordered first pair even when the initial repeats.

The exact frozen presentation replays the complete two-law left-regular-band
calculus behind TWO arbitrary initial guards. Its genuine initial-return,
second-return, and repeated-initial-gather derivations insert only already-seen
markers and never permute first occurrences. These close every endpoint
stratum without global guard cancellation or an unproved owner premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 9000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank088.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def pairWord
    (initial marker : Nat) (tail : List Nat) : Word Nat :=
  ⟨initial, marker :: tail⟩

/-- Frozen law 00 is unrestricted square expansion. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 returns the repeated initial block. -/
theorem derivesRepeatedReturn
    (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      (((first ++ first) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [0, 1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 04 turns a square followed by a block into its alternation. -/
theorem derivesSquareAlternation
    (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      (((first ++ second) ++ first) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 09 gathers two already-seen initial blocks. -/
theorem derivesRepeatedInitialGather
    (first second rest : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ rest)
      ((((first ++ second) ++ rest) ++ first) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2])
        (Word.mk 0 [1, 2, 0, 1]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second rest)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 12 moves a returned initial block across an arbitrary block. -/
theorem derivesInitialReturnShift
    (first second final : Word Nat) :
    Derives basis
      (((first ++ second) ++ first) ++ final)
      (((first ++ second) ++ final) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2]) (Word.mk 0 [1, 2, 0]) :=
    Derives.fromBasis (e := law12) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 13 duplicates a nonempty block behind two initial guards. -/
theorem derivesSuffixDuplication
    (guard₁ guard₂ block : Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ block)
      (((guard₁ ++ guard₂) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law13) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree guard₁ guard₂ block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The complete LRB regular law has a genuine THREE-step guarded replay. -/
theorem derivesLrbRegularUnderInitialPair
    (guard₁ guard₂ first second : Word Nat) :
    Derives basis
      (((guard₁ ++ guard₂) ++ first) ++ second)
      ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
  have firstStep :
      Derives basis
        (((guard₁ ++ guard₂) ++ first) ++ second)
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication guard₁ guard₂ first) second
  have secondStep :
      Derives basis
        ((((guard₁ ++ guard₂) ++ first) ++ first) ++ second)
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      Derives.prepend (guard₁ ++ guard₂)
        (derivesRepeatedReturn first second)
  have thirdStep :
      Derives basis
        (((((guard₁ ++ guard₂) ++ first) ++ first) ++ second) ++ first)
        ((((guard₁ ++ guard₂) ++ first) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication guard₁ guard₂ first).symm
        (second ++ first)
  exact firstStep.trans (secondStep.trans thirdStep)

/-- A repeated second block moves across ANY nonempty replacement block.
The exact three steps are square alternation, initial-return shift, and
guarded square contraction. -/
theorem derivesSecondReturnShift
    (initial second replacement : Word Nat) :
    Derives basis
      (((initial ++ second) ++ second) ++ replacement)
      (((initial ++ second) ++ replacement) ++ second) := by
  have firstStep :
      Derives basis
        (((initial ++ second) ++ second) ++ replacement)
        ((((initial ++ second) ++ replacement) ++ second) ++ replacement) := by
    simpa [Word.append_assoc] using
      Derives.prepend initial (derivesSquareAlternation second replacement)
  have secondStep :
      Derives basis
        ((((initial ++ second) ++ replacement) ++ second) ++ replacement)
        ((((initial ++ second) ++ replacement) ++ replacement) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend initial
        (derivesInitialReturnShift second replacement replacement)
  have thirdStep :
      Derives basis
        ((((initial ++ second) ++ replacement) ++ replacement) ++ second)
        (((initial ++ second) ++ replacement) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesSuffixDuplication initial second replacement).symm second
  exact firstStep.trans (secondStep.trans thirdStep)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Replay BOTH complete LRB laws behind arbitrary nonempty initial guards,
including every substitution, both contexts, symmetry, and transitivity. -/
theorem liftLeftRegularBandUnderInitialPair
    {left right : Word Nat}
    (derivation : Derives leftRegularBandThreeBasis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((guard₁ ++ guard₂) ++ left.bind substitution)
      ((guard₁ ++ guard₂) ++ right.bind substitution) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [leftRegularBandThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.singleton 0).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesSuffixDuplication guard₁ guard₂ (substitution 0)
      · change Derives basis
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1]).bind substitution)
          ((guard₁ ++ guard₂) ++ (Word.mk 0 [1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesLrbRegularUnderInitialPair
            guard₁ guard₂ (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis guard₁ (guard₂ ++ front.bind substitution)
          substitution
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (hypothesis guard₁ guard₂ substitution)
          (suffix.bind substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- Equal COMPLETE first-occurrence order suffices under both initial guards. -/
theorem derivesSameFirstOrderUnderInitialPair
    (left right guard₁ guard₂ : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis
      ((guard₁ ++ guard₂) ++ left)
      ((guard₁ ++ guard₂) ++ right) := by
  simpa only [bind_singleton] using
    liftLeftRegularBandUnderInitialPair
      (SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbDerives_of_sameFirstOccurrences
        left right order)
      guard₁ guard₂ Word.singleton

/-- Insert an already-seen initial variable immediately after the initial
pair, without changing full first-occurrence order. -/
theorem derivesInsertSeenInitial
    (initial second tail : Word Nat)
    (seen :
      Derives leftRegularBandThreeBasis tail (tail ++ initial)) :
    Derives basis
      ((initial ++ second) ++ tail)
      ((initial ++ second) ++ (initial ++ tail)) := by
  have appended :
      Derives basis
        ((initial ++ second) ++ tail)
        ((initial ++ second) ++ (tail ++ initial)) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderInitialPair seen
        initial second Word.singleton
  have moved :
      Derives basis
        ((initial ++ second) ++ (tail ++ initial))
        ((initial ++ second) ++ (initial ++ tail)) := by
    simpa [Word.append_assoc] using
      (derivesInitialReturnShift initial second tail).symm
  exact appended.trans moved

/-- Insert an already-seen second variable immediately after the initial
pair, using only the genuine three-step second-return shift. -/
theorem derivesInsertSeenSecond
    (initial second tail : Word Nat)
    (seen :
      Derives leftRegularBandThreeBasis tail (tail ++ second)) :
    Derives basis
      ((initial ++ second) ++ tail)
      ((initial ++ second) ++ (second ++ tail)) := by
  have appended :
      Derives basis
        ((initial ++ second) ++ tail)
        ((initial ++ second) ++ (tail ++ second)) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderInitialPair seen
        initial second Word.singleton
  have moved :
      Derives basis
        ((initial ++ second) ++ (tail ++ second))
        ((initial ++ second) ++ (second ++ tail)) := by
    simpa [Word.append_assoc] using
      (derivesSecondReturnShift initial second tail).symm
  exact appended.trans moved

/-- If both initial blocks recur in the genuine suffix, law 09 gathers them
into an honest duplicated-initial prefix. -/
theorem derivesGatherSeenInitialPair
    (initial second tail : Word Nat)
    (initialSeen :
      Derives leftRegularBandThreeBasis tail (tail ++ initial))
    (secondSeen :
      Derives leftRegularBandThreeBasis tail (tail ++ second)) :
    Derives basis
      ((initial ++ second) ++ tail)
      ((initial ++ initial) ++ (second ++ tail)) := by
  have secondAfterInitial :
      Derives leftRegularBandThreeBasis
        (tail ++ initial)
        ((tail ++ initial) ++ second) :=
    initialSeen.symm.trans <|
      secondSeen.trans (Derives.appendRight initialSeen second)
  have combined :
      Derives leftRegularBandThreeBasis
        tail ((tail ++ initial) ++ second) :=
    initialSeen.trans secondAfterInitial
  have appendBoth :
      Derives basis
        ((initial ++ second) ++ tail)
        ((initial ++ second) ++ ((tail ++ initial) ++ second)) := by
    simpa only [bind_singleton] using
      liftLeftRegularBandUnderInitialPair combined
        initial second Word.singleton
  have gather :
      Derives basis
        ((initial ++ second) ++ ((tail ++ initial) ++ second))
        ((initial ++ initial) ++ (second ++ tail)) := by
    simpa [Word.append_assoc] using
      (derivesRepeatedInitialGather initial second tail).symm
  exact appendBoth.trans gather

/-- Behind a genuinely repeated initial, equality of the FULL original
first-occurrence sequence is sufficient: insert one more initial, replay the
complete LRB proof, and contract that independently justified duplicate. -/
theorem derivesUnderRepeatedInitialOfFullOrder
    (initial left right : Word Nat)
    (order :
      firstOccurrenceSequence (initial ++ left).toList =
        firstOccurrenceSequence (initial ++ right).toList) :
    Derives basis
      ((initial ++ initial) ++ left)
      ((initial ++ initial) ++ right) := by
  have expandLeft :
      Derives basis
        ((initial ++ initial) ++ left)
        ((initial ++ initial) ++ (initial ++ left)) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerExpansion initial) left
  have transport :
      Derives basis
        ((initial ++ initial) ++ (initial ++ left))
        ((initial ++ initial) ++ (initial ++ right)) :=
    derivesSameFirstOrderUnderInitialPair
      (initial ++ left) (initial ++ right) initial initial order
  have contractRight :
      Derives basis
        ((initial ++ initial) ++ (initial ++ right))
        ((initial ++ initial) ++ right) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerExpansion initial).symm right
  exact expandLeft.trans (transport.trans contractRight)

private def appendLetters
    (word : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨word.head, word.tail ++ tail⟩

private theorem appendLetters_derives
    {left right : Word Nat}
    (derivation : Derives basis left right)
    (tail : List Nat) :
    Derives basis
      (appendLetters left tail)
      (appendLetters right tail) := by
  cases tail with
  | nil =>
      simpa [appendLetters] using derivation
  | cons first rest =>
      simpa [appendLetters, Word.append] using
        Derives.appendRight derivation (Word.mk first rest)

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat)
    (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬ keep selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

/-- Restricting support commutes with the COMPLETE first-occurrence renderer. -/
theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

private theorem filter_ne_of_not_mem
    (selected : Nat) (letters : List Nat)
    (absent : selected ∉ letters) :
    letters.filter (fun letter => decide (letter ≠ selected)) = letters := by
  apply List.filter_eq_self.mpr
  intro letter present
  simp only [decide_eq_true_eq]
  intro equal
  subst letter
  exact absent present

/-- Deleting the same literal variable from two equal first-order lists
preserves equality without permuting any occurrence. -/
theorem filteredFirstOccurrenceEquality
    (selected : Nat) {left right : List Nat}
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right) :
    firstOccurrenceSequence
        (left.filter (fun letter => decide (letter ≠ selected))) =
      firstOccurrenceSequence
        (right.filter (fun letter => decide (letter ≠ selected))) := by
  rw [firstOccurrenceSequence_filter,
    firstOccurrenceSequence_filter, order]

/-- With the literal initial pair fixed, equal COMPLETE suffix-first-order
lists derive, including the two empty-suffix boundary cases. -/
theorem derivesFixedPairOfTailFirstOrder
    (initial marker : Nat) (left right : List Nat)
    (order :
      firstOccurrenceSequence left =
        firstOccurrenceSequence right) :
    Derives basis
      (pairWord initial marker left)
      (pairWord initial marker right) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact Derives.refl _
      | cons head tail =>
          simp [firstOccurrenceSequence] at order
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp [firstOccurrenceSequence] at order
      | cons rightHead rightTail =>
          have replay :=
            derivesSameFirstOrderUnderInitialPair
              (Word.mk leftHead leftTail)
              (Word.mk rightHead rightTail)
              (Word.singleton initial)
              (Word.singleton marker)
              (by simpa [Word.toList] using order)
          simpa [pairWord, Word.singleton, Word.append] using replay

/-- A literal initial pair reverses to the exact independent S5_240 suffix
signature; the globally simple second marker remains visible even if the
initial variable repeats elsewhere. -/
theorem reversePair_split
    (initial marker : Nat) (tail : List Nat) :
    terminalSplit (pairWord initial marker tail).reverse =
      .pair tail.reverse marker initial := by
  have rendered :
      (pairWord initial marker tail).reverse =
        (TerminalSplit.pair tail.reverse marker initial).renderWord := by
    apply Word.toList_injective
    rw [Word.toList_reverse, TerminalSplit.toList_renderWord]
    simp [pairWord, Word.toList, TerminalSplit.renderList,
      List.reverse_cons, List.append_assoc]
  rw [rendered, terminalSplit_renderWord_inverse]

/-- The first TWO distinct first-occurrence variables are already determined
by the full first-order invariant. -/
theorem secondMarker_of_uniqueInitial_and_firstOrder
    (initial leftMarker rightMarker : Nat)
    (leftTail rightTail : List Nat)
    (leftDistinct : initial ≠ leftMarker)
    (rightDistinct : initial ≠ rightMarker)
    (order :
      firstOccurrenceSequence
          (initial :: leftMarker :: leftTail) =
        firstOccurrenceSequence
          (initial :: rightMarker :: rightTail)) :
    leftMarker = rightMarker := by
  have firstDropped := congrArg List.tail order
  have secondHead := congrArg List.head? firstDropped
  simpa [firstOccurrenceSequence, leftDistinct, rightDistinct,
    Ne.symm leftDistinct, Ne.symm rightDistinct] using secondHead

/-- When neither the second marker nor the initial variable is globally
simple, gather an ACTUALLY recurring pair into a duplicated initial prefix. -/
theorem derivesNonsimpleInitialCanonical
    (initial marker : Nat) (tail : List Nat)
    (notSimple : ¬(marker ≠ initial ∧ marker ∉ tail))
    (notUnique : ¬(initial ≠ marker ∧ initial ∉ tail)) :
    Derives basis
      (pairWord initial marker tail)
      (pairWord initial initial (marker :: tail)) := by
  by_cases equal : marker = initial
  · subst marker
    have power := derivesPowerExpansion (Word.singleton initial)
    simpa [pairWord, appendLetters, Word.append,
      Word.singleton, List.append_assoc] using
      appendLetters_derives power tail
  · have markerPresent : marker ∈ tail := by
      apply Decidable.byContradiction
      intro absent
      exact notSimple ⟨equal, absent⟩
    have initialPresent : initial ∈ tail := by
      apply Decidable.byContradiction
      intro absent
      exact notUnique ⟨Ne.symm equal, absent⟩
    cases tail with
    | nil => simp at markerPresent
    | cons head rest =>
        let tailWord : Word Nat := Word.mk head rest
        have initialSeen :
            Derives leftRegularBandThreeBasis
              tailWord (tailWord ++ Word.singleton initial) :=
          SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
            tailWord initial (by simpa [tailWord, Word.toList] using initialPresent)
        have markerSeen :
            Derives leftRegularBandThreeBasis
              tailWord (tailWord ++ Word.singleton marker) :=
          SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
            tailWord marker (by simpa [tailWord, Word.toList] using markerPresent)
        simpa [pairWord, tailWord, Word.singleton, Word.append,
          List.append_assoc] using
          derivesGatherSeenInitialPair
            (Word.singleton initial)
            (Word.singleton marker)
            tailWord initialSeen markerSeen

/-- Remove a globally absent initial variable from both COMPLETE first-order
lists; the actual second markers remain in their original order. -/
theorem firstOrder_dropAbsentInitial
    (initial leftMarker rightMarker : Nat)
    (leftTail rightTail : List Nat)
    (leftDistinct : initial ≠ leftMarker)
    (rightDistinct : initial ≠ rightMarker)
    (leftAbsent : initial ∉ leftTail)
    (rightAbsent : initial ∉ rightTail)
    (order :
      firstOccurrenceSequence
          (initial :: leftMarker :: leftTail) =
        firstOccurrenceSequence
          (initial :: rightMarker :: rightTail)) :
    firstOccurrenceSequence (leftMarker :: leftTail) =
      firstOccurrenceSequence (rightMarker :: rightTail) := by
  have restricted := filteredFirstOccurrenceEquality initial order
  have leftClean :
      leftTail.filter (fun letter => !decide (letter = initial)) = leftTail := by
    simpa only [decide_not] using
      filter_ne_of_not_mem initial leftTail leftAbsent
  have rightClean :
      rightTail.filter (fun letter => !decide (letter = initial)) = rightTail := by
    simpa only [decide_not] using
      filter_ne_of_not_mem initial rightTail rightAbsent
  simpa [leftDistinct, rightDistinct, Ne.symm leftDistinct,
    Ne.symm rightDistinct, leftClean, rightClean] using restricted

/-- Remove the same globally simple second variable from both full first-order
lists; the initial variable and every later first occurrence are preserved. -/
theorem firstOrder_dropAbsentSecond
    (initial marker : Nat)
    (leftTail rightTail : List Nat)
    (different : marker ≠ initial)
    (leftAbsent : marker ∉ leftTail)
    (rightAbsent : marker ∉ rightTail)
    (order :
      firstOccurrenceSequence
          (initial :: marker :: leftTail) =
        firstOccurrenceSequence
          (initial :: marker :: rightTail)) :
    firstOccurrenceSequence (initial :: leftTail) =
      firstOccurrenceSequence (initial :: rightTail) := by
  have restricted := filteredFirstOccurrenceEquality marker order
  have leftClean :
      leftTail.filter (fun letter => !decide (letter = marker)) = leftTail := by
    simpa only [decide_not] using
      filter_ne_of_not_mem marker leftTail leftAbsent
  have rightClean :
      rightTail.filter (fun letter => !decide (letter = marker)) = rightTail := by
    simpa only [decide_not] using
      filter_ne_of_not_mem marker rightTail rightAbsent
  simpa [different, Ne.symm different, leftClean, rightClean] using restricted

/-- For a fixed globally simple second variable and a genuinely repeated
initial, insert the seen initial in both suffixes and replay full LRB order. -/
theorem derivesFixedPairOfRepeatedInitialOrder
    (initial marker : Nat)
    (leftTail rightTail : List Nat)
    (leftSeen : initial ∈ leftTail)
    (rightSeen : initial ∈ rightTail)
    (order :
      firstOccurrenceSequence (initial :: leftTail) =
        firstOccurrenceSequence (initial :: rightTail)) :
    Derives basis
      (pairWord initial marker leftTail)
      (pairWord initial marker rightTail) := by
  cases leftTail with
  | nil => simp at leftSeen
  | cons leftHead leftRest =>
      cases rightTail with
      | nil => simp at rightSeen
      | cons rightHead rightRest =>
          let leftWord : Word Nat := Word.mk leftHead leftRest
          let rightWord : Word Nat := Word.mk rightHead rightRest
          let initialWord : Word Nat := Word.singleton initial
          let markerWord : Word Nat := Word.singleton marker
          have leftAppend :
              Derives leftRegularBandThreeBasis
                leftWord (leftWord ++ initialWord) :=
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
              leftWord initial
              (by simpa [leftWord, Word.toList] using leftSeen)
          have rightAppend :
              Derives leftRegularBandThreeBasis
                rightWord (rightWord ++ initialWord) :=
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
              rightWord initial
              (by simpa [rightWord, Word.toList] using rightSeen)
          have inside :
              firstOccurrenceSequence (initialWord ++ leftWord).toList =
                firstOccurrenceSequence (initialWord ++ rightWord).toList := by
            simpa [initialWord, leftWord, rightWord,
              Word.singleton, Word.append, Word.toList] using order
          have replay :=
            (derivesInsertSeenInitial
              initialWord markerWord leftWord leftAppend).trans <|
              (derivesSameFirstOrderUnderInitialPair
                (initialWord ++ leftWord)
                (initialWord ++ rightWord)
                initialWord markerWord inside).trans
                (derivesInsertSeenInitial
                  initialWord markerWord rightWord rightAppend).symm
          simpa [pairWord, initialWord, markerWord, leftWord, rightWord,
            Word.singleton, Word.append] using replay

/-- For a fixed genuinely repeated second variable and a globally unique
initial, insert the seen second variable in both suffixes and replay full
LRB first-occurrence order. -/
theorem derivesFixedPairOfRepeatedSecondOrder
    (initial marker : Nat)
    (leftTail rightTail : List Nat)
    (leftSeen : marker ∈ leftTail)
    (rightSeen : marker ∈ rightTail)
    (order :
      firstOccurrenceSequence (marker :: leftTail) =
        firstOccurrenceSequence (marker :: rightTail)) :
    Derives basis
      (pairWord initial marker leftTail)
      (pairWord initial marker rightTail) := by
  cases leftTail with
  | nil => simp at leftSeen
  | cons leftHead leftRest =>
      cases rightTail with
      | nil => simp at rightSeen
      | cons rightHead rightRest =>
          let leftWord : Word Nat := Word.mk leftHead leftRest
          let rightWord : Word Nat := Word.mk rightHead rightRest
          let initialWord : Word Nat := Word.singleton initial
          let markerWord : Word Nat := Word.singleton marker
          have leftAppend :
              Derives leftRegularBandThreeBasis
                leftWord (leftWord ++ markerWord) :=
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
              leftWord marker
              (by simpa [leftWord, Word.toList] using leftSeen)
          have rightAppend :
              Derives leftRegularBandThreeBasis
                rightWord (rightWord ++ markerWord) :=
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbAppendSeen
              rightWord marker
              (by simpa [rightWord, Word.toList] using rightSeen)
          have inside :
              firstOccurrenceSequence (markerWord ++ leftWord).toList =
                firstOccurrenceSequence (markerWord ++ rightWord).toList := by
            simpa [markerWord, leftWord, rightWord,
              Word.singleton, Word.append, Word.toList] using order
          have replay :=
            (derivesInsertSeenSecond
              initialWord markerWord leftWord leftAppend).trans <|
              (derivesSameFirstOrderUnderInitialPair
                (markerWord ++ leftWord)
                (markerWord ++ rightWord)
                initialWord markerWord inside).trans
                (derivesInsertSeenSecond
                  initialWord markerWord rightWord rightAppend).symm
          simpa [pairWord, initialWord, markerWord, leftWord, rightWord,
            Word.singleton, Word.append] using replay

/-- COMPLETE first-occurrence order together with the ACTUAL reversed
S5_240 endpoint signature derives every non-singleton identity. The four
honest branches are unique/simple, repeated-initial/simple,
unique-initial/repeated-second, and nonsimple/repeated-initial. -/
theorem derivesPairOfReversedSignatureAndFirstOrder
    (initial leftMarker rightMarker : Nat)
    (leftTail rightTail : List Nat)
    (order :
      firstOccurrenceSequence
          (pairWord initial leftMarker leftTail).toList =
        firstOccurrenceSequence
          (pairWord initial rightMarker rightTail).toList)
    (same :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature
        (pairWord initial leftMarker leftTail).reverse
        (pairWord initial rightMarker rightTail).reverse) :
    Derives basis
      (pairWord initial leftMarker leftTail)
      (pairWord initial rightMarker rightTail) := by
  have leftSplit := reversePair_split initial leftMarker leftTail
  have rightSplit := reversePair_split initial rightMarker rightTail
  have actualOrder :
      firstOccurrenceSequence (initial :: leftMarker :: leftTail) =
        firstOccurrenceSequence (initial :: rightMarker :: rightTail) := by
    simpa [pairWord, Word.toList] using order
  have uniqueIff :
      (initial ≠ leftMarker ∧ initial ∉ leftTail) ↔
        (initial ≠ rightMarker ∧ initial ∉ rightTail) := by
    simpa [UniqueFinal, leftSplit, rightSplit] using
      same.uniqueFinal initial
  by_cases leftSimple :
      leftMarker ≠ initial ∧ leftMarker ∉ leftTail
  · have leftPair :
        SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
          (pairWord initial leftMarker leftTail).reverse
          leftMarker initial := by
      simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
        leftSplit] using
        ⟨leftSimple.2, Ne.symm leftSimple.1⟩
    have rightPair :=
      (same.simplePenultimatePair leftMarker initial).mp leftPair
    have rightParts :
        rightMarker = leftMarker ∧
          leftMarker ∉ rightTail ∧
          initial ≠ leftMarker := by
      simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
        rightSplit] using rightPair
    have markerEqual := rightParts.1
    subst rightMarker
    by_cases leftUnique :
        initial ≠ leftMarker ∧ initial ∉ leftTail
    · have rightUnique := uniqueIff.mp leftUnique
      have pairOrder :=
        firstOrder_dropAbsentInitial initial leftMarker leftMarker
          leftTail rightTail
          leftUnique.1 rightUnique.1
          leftUnique.2 rightUnique.2 actualOrder
      have restricted :=
        filteredFirstOccurrenceEquality leftMarker pairOrder
      have leftClean :
          leftTail.filter
            (fun letter => !decide (letter = leftMarker)) = leftTail := by
        simpa only [decide_not] using
          filter_ne_of_not_mem leftMarker leftTail leftSimple.2
      have rightClean :
          rightTail.filter
            (fun letter => !decide (letter = leftMarker)) = rightTail := by
        simpa only [decide_not] using
          filter_ne_of_not_mem leftMarker rightTail rightParts.2.1
      have tailOrder :
          firstOccurrenceSequence leftTail =
            firstOccurrenceSequence rightTail := by
        simpa [leftClean, rightClean] using restricted
      exact derivesFixedPairOfTailFirstOrder
        initial leftMarker leftTail rightTail tailOrder
    · have rightNotUnique :
          ¬(initial ≠ leftMarker ∧ initial ∉ rightTail) := by
        intro present
        exact leftUnique (uniqueIff.mpr present)
      have initialLeft : initial ∈ leftTail := by
        apply Decidable.byContradiction
        intro absent
        exact leftUnique ⟨Ne.symm leftSimple.1, absent⟩
      have initialRight : initial ∈ rightTail := by
        apply Decidable.byContradiction
        intro absent
        exact rightNotUnique ⟨Ne.symm leftSimple.1, absent⟩
      have reduced :=
        firstOrder_dropAbsentSecond initial leftMarker
          leftTail rightTail leftSimple.1
          leftSimple.2 rightParts.2.1 actualOrder
      exact derivesFixedPairOfRepeatedInitialOrder
        initial leftMarker leftTail rightTail
        initialLeft initialRight reduced
  · have rightNotSimple :
        ¬(rightMarker ≠ initial ∧ rightMarker ∉ rightTail) := by
      intro rightSimple
      have rightPair :
          SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
            (pairWord initial rightMarker rightTail).reverse
            rightMarker initial := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
          rightSplit] using
          ⟨rightSimple.2, Ne.symm rightSimple.1⟩
      have leftPair :=
        (same.simplePenultimatePair rightMarker initial).mpr rightPair
      have leftParts :
          leftMarker = rightMarker ∧
            rightMarker ∉ leftTail ∧
            initial ≠ rightMarker := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
          leftSplit] using leftPair
      apply leftSimple
      constructor
      · intro equal
        exact leftParts.2.2 (equal.symm.trans leftParts.1)
      · intro present
        exact leftParts.2.1 <| by
          simpa [← leftParts.1] using present
    by_cases leftUnique :
        initial ≠ leftMarker ∧ initial ∉ leftTail
    · have rightUnique := uniqueIff.mp leftUnique
      have markerEqual :=
        secondMarker_of_uniqueInitial_and_firstOrder
          initial leftMarker rightMarker leftTail rightTail
          leftUnique.1 rightUnique.1 actualOrder
      subst rightMarker
      have leftRepeated : leftMarker ∈ leftTail := by
        apply Decidable.byContradiction
        intro absent
        exact leftSimple ⟨Ne.symm leftUnique.1, absent⟩
      have rightRepeated : leftMarker ∈ rightTail := by
        apply Decidable.byContradiction
        intro absent
        exact rightNotSimple ⟨Ne.symm rightUnique.1, absent⟩
      have reduced :=
        firstOrder_dropAbsentInitial initial leftMarker leftMarker
          leftTail rightTail
          leftUnique.1 rightUnique.1
          leftUnique.2 rightUnique.2 actualOrder
      exact derivesFixedPairOfRepeatedSecondOrder
        initial leftMarker leftTail rightTail
        leftRepeated rightRepeated reduced
    · have rightNotUnique :
          ¬(initial ≠ rightMarker ∧ initial ∉ rightTail) := by
        intro present
        exact leftUnique (uniqueIff.mpr present)
      have leftCanonical :=
        derivesNonsimpleInitialCanonical
          initial leftMarker leftTail leftSimple leftUnique
      have rightCanonical :=
        derivesNonsimpleInitialCanonical
          initial rightMarker rightTail rightNotSimple rightNotUnique
      let initialWord : Word Nat := Word.singleton initial
      let leftWord : Word Nat := Word.mk leftMarker leftTail
      let rightWord : Word Nat := Word.mk rightMarker rightTail
      have paddedOrder :
          firstOccurrenceSequence (initialWord ++ leftWord).toList =
            firstOccurrenceSequence (initialWord ++ rightWord).toList := by
        simpa [initialWord, leftWord, rightWord,
          Word.singleton, Word.append, Word.toList] using actualOrder
      have bridge :
          Derives basis
            (pairWord initial initial (leftMarker :: leftTail))
            (pairWord initial initial (rightMarker :: rightTail)) := by
        simpa [pairWord, initialWord, leftWord, rightWord,
          Word.singleton, Word.append, List.append_assoc] using
          derivesUnderRepeatedInitialOfFullOrder
            initialWord leftWord rightWord paddedOrder
      exact leftCanonical.trans (bridge.trans rightCanonical.symm)

/-- COMPLETE first-occurrence order and the COMPLETE reversed direct-factor
signature derive every identity, including singleton boundaries. -/
theorem derives_of_signatures
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature
        left.reverse right.reverse) :
    Derives basis left right := by
  cases left with
  | mk initial leftLetters =>
      cases right with
      | mk rightInitial rightLetters =>
          have heads : initial = rightInitial := by
            have compared := congrArg List.head? order
            simpa [Word.toList, firstOccurrenceSequence] using compared
          subst rightInitial
          cases leftLetters with
          | nil =>
              cases rightLetters with
              | nil => exact Derives.refl _
              | cons rightMarker rightTail =>
                  have leftSingleton :
                      IsSingletonWord (Word.mk initial []).reverse := by
                    change True
                    trivial
                  have rightSingleton :=
                    signature.singleton.mp leftSingleton
                  change
                    IsSingletonWord
                      (pairWord initial rightMarker rightTail).reverse
                    at rightSingleton
                  have rightSplit :=
                    reversePair_split initial rightMarker rightTail
                  simp [IsSingletonWord, rightSplit] at rightSingleton
          | cons leftMarker leftTail =>
              cases rightLetters with
              | nil =>
                  have rightSingleton :
                      IsSingletonWord (Word.mk initial []).reverse := by
                    change True
                    trivial
                  have leftSingleton :=
                    signature.singleton.mpr rightSingleton
                  change
                    IsSingletonWord
                      (pairWord initial leftMarker leftTail).reverse
                    at leftSingleton
                  have leftSplit :=
                    reversePair_split initial leftMarker leftTail
                  simp [IsSingletonWord, leftSplit] at leftSingleton
              | cons rightMarker rightTail =>
                  exact
                    derivesPairOfReversedSignatureAndFirstOrder
                      initial leftMarker rightMarker
                      leftTail rightTail order signature

/-- Validity in the actual opposite factor is equivalent to validity of the
reversed identity in the independently complete direct `S5_240` factor. -/
theorem rightValid_reversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup.opposite
    at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup).mp valid

/-- The two ACTUAL independently certified factors discharge every premise
of the unrestricted initial-endpoint normalizer. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have order :=
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
      identity leftValid
  have directValid := rightValid_reversed identity rightValid
  have signature :=
    SemigroupBasis.CoRoots.S5_240.valid_signature
      identity.reversed directValid
  exact derives_of_signatures
    identity.lhs identity.rhs order signature

/-- Assemble the exact immutable factor intersection ONLY after proving
unrestricted completeness on every alphabet. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-088 family seed, with no conditional premise. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The authenticated rank-088 representative class is unconditional. -/
theorem s6_6512_representative_basis :
    BasisFor S6_6512.table.semigroup basis :=
  S6_6512.representative_basis_of_normalizer normalizer

/-- Its opposite orientation uses the exact reversed displayed presentation. -/
theorem s6_6512_opposite_basis :
    BasisFor S6_6512.table.semigroup.opposite (reversedBasis basis) :=
  S6_6512.opposite_basis_of_normalizer normalizer

/-- Shared reviewed transport preserves explicit displayed-law derivations
and independent unrestricted theory implications for BOTH target factors. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank088.Seed
