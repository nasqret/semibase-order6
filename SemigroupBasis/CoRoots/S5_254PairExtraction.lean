import SemigroupBasis.CoRoots.S5_254PairTransport

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private def instantiateFourWords
    (x y z w : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => w
  | n + 4 => Word.singleton (n + 4)

/-! ## Adjacent swaps with witnesses outside the displayed interval -/

/-- Swap two adjacent letters when both have later witnesses and both
intervening fillers are nonempty. -/
theorem derivesSwapWithFutureWitnesses
    (left right middle beforeRight : Word Nat) :
    Derives basis
      (((((left ++ right) ++ middle) ++ left) ++ beforeRight) ++ right)
      (((((right ++ left) ++ middle) ++ left) ++ beforeRight) ++ right) := by
  have substituted :=
    derivesWyPrefixTransportSubstitution
      (instantiateFourWords left right middle beforeRight)
  change
    Derives basis
      (((((left ++ right) ++ middle) ++ left) ++ beforeRight) ++ right)
      (((((right ++ left) ++ middle) ++ left) ++ beforeRight) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with no filler between the two left witnesses. -/
theorem derivesSwapWithFutureWitnessesNoMiddle
    (left right beforeRight : Word Nat) :
    Derives basis
      ((((left ++ right) ++ left) ++ beforeRight) ++ right)
      ((((right ++ left) ++ left) ++ beforeRight) ++ right) := by
  have substituted :=
    derivesWyRotationSubstitution
      (instantiateFourWords left right right beforeRight)
  change
    Derives basis
      ((((left ++ right) ++ left) ++ beforeRight) ++ right)
      ((((right ++ left) ++ left) ++ beforeRight) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with no filler before the later right witness. -/
theorem derivesSwapWithFutureWitnessesNoBeforeRight
    (left right middle : Word Nat) :
    Derives basis
      ((((left ++ right) ++ middle) ++ left) ++ right)
      ((((right ++ left) ++ middle) ++ left) ++ right) := by
  have substituted :=
    derivesTerminalYTransportSubstitution
      (instantiateFourWords left right middle middle)
  change
    Derives basis
      ((((left ++ right) ++ middle) ++ left) ++ right)
      ((((right ++ left) ++ middle) ++ left) ++ right)
    at substituted
  exact substituted

/-- Future-witness swap with both fillers empty. -/
theorem derivesSwapWithFutureWitnessesShort
    (left right : Word Nat) :
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((right ++ left) ++ left) ++ right) := by
  have substituted :=
    derivesAlternatingPairSubstitution
      (instantiateFourWords left right right right)
  change
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((right ++ left) ++ left) ++ right)
    at substituted
  exact substituted

/-- Swap adjacent `left,right` when `right` has a past witness and `left`
has a future witness. The orientation is the reverse of
`x y x z w z = x y z x w z`. -/
theorem derivesSwapWithPastRightFutureLeft
    (left right afterPast beforeFuture : Word Nat) :
    Derives basis
      (((((right ++ afterPast) ++ left) ++ right) ++ beforeFuture) ++ left)
      (((((right ++ afterPast) ++ right) ++ left) ++ beforeFuture) ++ left) := by
  have substituted :=
    derivesLongZwzTransportSubstitution
      (instantiateFourWords right afterPast left beforeFuture)
  change
    Derives basis
      (((((right ++ afterPast) ++ right) ++ left) ++ beforeFuture) ++ left)
      (((((right ++ afterPast) ++ left) ++ right) ++ beforeFuture) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with no filler after the past witness. -/
theorem derivesSwapWithPastRightFutureLeftNoAfterPast
    (left right beforeFuture : Word Nat) :
    Derives basis
      ((((right ++ left) ++ right) ++ beforeFuture) ++ left)
      ((((right ++ right) ++ left) ++ beforeFuture) ++ left) := by
  have substituted :=
    derivesZwzPrefixSubstitution
      (instantiateFourWords right right left beforeFuture)
  change
    Derives basis
      ((((right ++ right) ++ left) ++ beforeFuture) ++ left)
      ((((right ++ left) ++ right) ++ beforeFuture) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with no filler before the future witness. -/
theorem derivesSwapWithPastRightFutureLeftNoBeforeFuture
    (left right afterPast : Word Nat) :
    Derives basis
      ((((right ++ afterPast) ++ left) ++ right) ++ left)
      ((((right ++ afterPast) ++ right) ++ left) ++ left) := by
  have substituted :=
    derivesDoubleZTransportSubstitution
      (instantiateFourWords right afterPast left left)
  change
    Derives basis
      ((((right ++ afterPast) ++ right) ++ left) ++ left)
      ((((right ++ afterPast) ++ left) ++ right) ++ left)
    at substituted
  exact substituted.symm

/-- Past/future swap with both fillers empty. -/
theorem derivesSwapWithPastRightFutureLeftShort
    (left right : Word Nat) :
    Derives basis
      (((right ++ left) ++ right) ++ left)
      (((right ++ right) ++ left) ++ left) := by
  have substituted :=
    derivesDoubleZPrefixSubstitution
      (instantiateFourWords right right left left)
  change
    Derives basis
      (((right ++ right) ++ left) ++ left)
      (((right ++ left) ++ right) ++ left)
    at substituted
  exact substituted.symm

/-- Swap adjacent letters when both have past witnesses and both fillers are
nonempty. -/
theorem derivesSwapWithPastWitnesses
    (left right betweenWitnesses beforeCurrent : Word Nat) :
    Derives basis
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ left) ++
        right)
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ right) ++
        left) := by
  have substituted :=
    derivesCrossedWZSubstitution
      (instantiateFourWords left betweenWitnesses right beforeCurrent)
  change
    Derives basis
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ left) ++
        right)
      (((((left ++ betweenWitnesses) ++ right) ++ beforeCurrent) ++ right) ++
        left)
    at substituted
  exact substituted

/-- Past-witness swap with no filler between the earlier witnesses. -/
theorem derivesSwapWithPastWitnessesNoBetween
    (left right beforeCurrent : Word Nat) :
    Derives basis
      ((((left ++ right) ++ beforeCurrent) ++ left) ++ right)
      ((((left ++ right) ++ beforeCurrent) ++ right) ++ left) := by
  have substituted :=
    derivesWzCrossingSubstitution
      (instantiateFourWords left left right beforeCurrent)
  change
    Derives basis
      ((((left ++ right) ++ beforeCurrent) ++ left) ++ right)
      ((((left ++ right) ++ beforeCurrent) ++ right) ++ left)
    at substituted
  exact substituted

/-- Past-witness swap with no filler before the current adjacent pair. -/
theorem derivesSwapWithPastWitnessesNoBeforeCurrent
    (left right betweenWitnesses : Word Nat) :
    Derives basis
      ((((left ++ betweenWitnesses) ++ right) ++ left) ++ right)
      ((((left ++ betweenWitnesses) ++ right) ++ right) ++ left) := by
  have substituted :=
    derivesTerminalZTransportSubstitution
      (instantiateFourWords left betweenWitnesses right right)
  change
    Derives basis
      ((((left ++ betweenWitnesses) ++ right) ++ left) ++ right)
      ((((left ++ betweenWitnesses) ++ right) ++ right) ++ left)
    at substituted
  exact substituted

/-- Past-witness swap with both fillers empty. -/
theorem derivesSwapWithPastWitnessesShort
    (left right : Word Nat) :
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((left ++ right) ++ right) ++ left) := by
  have substituted :=
    derivesAlternatingZSubstitution
      (instantiateFourWords left left right right)
  change
    Derives basis
      (((left ++ right) ++ left) ++ right)
      (((left ++ right) ++ right) ++ left)
    at substituted
  exact substituted

/-- List-level future-witness swap. The two fillers may independently be
empty; each empty case uses the corresponding deletion instance already in
the semigroup basis. -/
theorem listDerivesSwapWithFutureWitnesses
    (left right : Nat) (middle beforeRight : List Nat) :
    ListDerives
      ([left, right] ++ middle ++ [left] ++ beforeRight ++ [right])
      ([right, left] ++ middle ++ [left] ++ beforeRight ++ [right]) := by
  cases middle with
  | nil =>
      cases beforeRight with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesNoMiddle
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons middleHead middleTail =>
      cases beforeRight with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnessesNoBeforeRight
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons middleHead middleTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithFutureWitnesses
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons middleHead middleTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- List-level past-right/future-left swap with independently empty
fillers. -/
theorem listDerivesSwapWithPastRightFutureLeft
    (left right : Nat) (afterPast beforeFuture : List Nat) :
    ListDerives
      ([right] ++ afterPast ++ [left, right] ++ beforeFuture ++ [left])
      ([right] ++ afterPast ++ [right, left] ++ beforeFuture ++ [left]) := by
  cases afterPast with
  | nil =>
      cases beforeFuture with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftNoAfterPast
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons afterHead afterTail =>
      cases beforeFuture with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeftNoBeforeFuture
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons afterHead afterTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastRightFutureLeft
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons afterHead afterTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- List-level past-witness swap with independently empty fillers. -/
theorem listDerivesSwapWithPastWitnesses
    (left right : Nat) (betweenWitnesses beforeCurrent : List Nat) :
    ListDerives
      ([left] ++ betweenWitnesses ++ [right] ++ beforeCurrent ++
        [left, right])
      ([left] ++ betweenWitnesses ++ [right] ++ beforeCurrent ++
        [right, left]) := by
  cases betweenWitnesses with
  | nil =>
      cases beforeCurrent with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesShort
                  (Word.singleton left) (Word.singleton right)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesNoBetween
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons beforeHead beforeTail)
  | cons betweenHead betweenTail =>
      cases beforeCurrent with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnessesNoBeforeCurrent
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons betweenHead betweenTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesSwapWithPastWitnesses
                  (Word.singleton left) (Word.singleton right)
                  (S5_107.listWordOfCons betweenHead betweenTail)
                  (S5_107.listWordOfCons beforeHead beforeTail)

/-- Swap any adjacent pair whose two letters each have an occurrence in the
fixed outer contexts. The four past/future placements, and both possible
witness orders within one context, are covered by the three deletion-closed
swap families above. -/
theorem listDerivesSwapExternallyWitnessedAdjacent
    (prefixWords before : List Nat) (left right : Nat)
    (after suffix : List Nat)
    (leftExternal : left ∈ prefixWords ∨ left ∈ suffix)
    (rightExternal : right ∈ prefixWords ∨ right ∈ suffix) :
    ListDerives
      (prefixWords ++ before ++ [left, right] ++ after ++ suffix)
      (prefixWords ++ before ++ [right, left] ++ after ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl (basis := basis)
      (prefixWords ++ before ++ [left, left] ++ after ++ suffix)
  rcases leftExternal with leftPast | leftFuture <;>
    rcases rightExternal with rightPast | rightFuture
  · rcases List.append_of_mem leftPast with
      ⟨beforeLeft, afterLeft, prefixShape⟩
    have rightRelative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
      rw [prefixShape] at rightPast
      simpa [equal, Ne.symm equal] using rightPast
    rcases rightRelative with rightBefore | rightAfter
    · rcases List.append_of_mem rightBefore with
        ⟨beforeRight, between, beforeLeftShape⟩
      rw [prefixShape, beforeLeftShape]
      simpa [List.append_assoc] using
        ((listDerivesSwapWithPastWitnesses
          right left between (afterLeft ++ before)).context
            beforeRight (after ++ suffix)).symm
    · rcases List.append_of_mem rightAfter with
        ⟨between, afterRight, afterLeftShape⟩
      rw [prefixShape, afterLeftShape]
      simpa [List.append_assoc] using
        (listDerivesSwapWithPastWitnesses
          left right between (afterRight ++ before)).context
            beforeLeft (after ++ suffix)
  · rcases List.append_of_mem leftPast with
      ⟨beforeLeft, afterLeft, prefixShape⟩
    rcases List.append_of_mem rightFuture with
      ⟨beforeRight, afterRight, suffixShape⟩
    rw [prefixShape, suffixShape]
    simpa [List.append_assoc] using
      ((listDerivesSwapWithPastRightFutureLeft
        right left (afterLeft ++ before) (after ++ beforeRight)).context
          beforeLeft afterRight).symm
  · rcases List.append_of_mem rightPast with
      ⟨beforeRight, afterRight, prefixShape⟩
    rcases List.append_of_mem leftFuture with
      ⟨beforeLeft, afterLeft, suffixShape⟩
    rw [prefixShape, suffixShape]
    simpa [List.append_assoc] using
      (listDerivesSwapWithPastRightFutureLeft
        left right (afterRight ++ before) (after ++ beforeLeft)).context
          beforeRight afterLeft
  · rcases List.append_of_mem leftFuture with
      ⟨beforeLeft, afterLeft, suffixShape⟩
    have rightRelative : right ∈ beforeLeft ∨ right ∈ afterLeft := by
      rw [suffixShape] at rightFuture
      simpa [equal, Ne.symm equal] using rightFuture
    rcases rightRelative with rightBefore | rightAfter
    · rcases List.append_of_mem rightBefore with
        ⟨beforeRight, between, beforeLeftShape⟩
      rw [suffixShape, beforeLeftShape]
      simpa [List.append_assoc] using
        ((listDerivesSwapWithFutureWitnesses
          right left (after ++ beforeRight) between).context
            (prefixWords ++ before) afterLeft).symm
    · rcases List.append_of_mem rightAfter with
        ⟨between, afterRight, afterLeftShape⟩
      rw [suffixShape, afterLeftShape]
      simpa [List.append_assoc] using
        (listDerivesSwapWithFutureWitnesses
          left right (after ++ beforeLeft) between).context
            (prefixWords ++ before) afterRight

/-! ## Context-uniform pair gathering -/

/-- Move the left displayed occurrence across an arbitrary interleaving and
make the two displayed occurrences adjacent. Every interleaved letter must
have a witness outside the displayed interval, either in the prefix or in
`suffix`. The proof is uniform in both contexts and uses no empty
substitution image. -/
theorem listDerivesGatherExternallyWitnessedPair
    (letter : Nat) :
    ∀ (prefixWords middle suffix : List Nat),
      (∀ other, other ∈ middle →
        other ∈ prefixWords ∨ other ∈ suffix) →
      ListDerives
        (prefixWords ++ [letter] ++ middle ++ [letter] ++ suffix)
        (prefixWords ++ middle ++ [letter, letter] ++ suffix)
  | prefixWords, [], suffix, _ => by
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis)
          (prefixWords ++ [letter, letter] ++ suffix)
  | prefixWords, head :: tail, suffix, external => by
      have headExternal : head ∈ prefixWords ∨ head ∈ suffix :=
        external head (by simp)
      have swapped :
          ListDerives
            (prefixWords ++ [letter] ++ (head :: tail) ++ [letter] ++ suffix)
            ((prefixWords ++ [head]) ++ [letter] ++ tail ++ [letter] ++ suffix) := by
        rcases headExternal with headInPrefix | headInSuffix
        · rcases List.append_of_mem headInPrefix with
            ⟨before, afterPast, rfl⟩
          simpa [List.append_assoc] using
            (listDerivesSwapWithPastRightFutureLeft
              letter head afterPast tail).context before suffix
        · rcases List.append_of_mem headInSuffix with
            ⟨beforeRight, after, rfl⟩
          simpa [List.append_assoc] using
            (listDerivesSwapWithFutureWitnesses
              letter head tail beforeRight).context prefixWords after
      have tailExternal : ∀ other, other ∈ tail →
          other ∈ prefixWords ++ [head] ∨ other ∈ suffix := by
        intro other member
        rcases external other (List.mem_cons_of_mem head member) with
          inPrefix | inSuffix
        · exact Or.inl (List.mem_append_left [head] inPrefix)
        · exact Or.inr inSuffix
      have recurse :=
        listDerivesGatherExternallyWitnessedPair letter
          (prefixWords ++ [head]) tail suffix tailExternal
      exact swapped.trans <| by
        simpa [List.append_assoc] using recurse

/-! ## Refinement-minimal repeated intervals -/

/-- Split at the first occurrence of `letter`. The returned prefix contains
no occurrence of `letter`. -/
private theorem exists_first_occurrence_split
    (letter : Nat) :
    ∀ {letters : List Nat},
      letter ∈ letters →
        ∃ before after,
          letters = before ++ letter :: after ∧
            letter ∉ before
  | [], member => by
      simp at member
  | first :: rest, member => by
      by_cases equal : first = letter
      · subst first
        exact ⟨[], rest, by simp, by simp⟩
      · have letterNeFirst : letter ≠ first := Ne.symm equal
        have restMember : letter ∈ rest := by
          simpa [letterNeFirst] using member
        obtain ⟨before, after, shape, absent⟩ :=
          exists_first_occurrence_split letter restMember
        exact
          ⟨first :: before, after,
            by simp [shape, List.append_assoc],
            by simp [letterNeFirst, absent]⟩

/-- Two occurrences can be selected consecutively with respect to the chosen
letter, so the strict middle contains no further occurrence of it. -/
private theorem exists_consecutive_occurrence_split_of_count_ge_two
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after ∧
            letter ∉ middle
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equal : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, shape, absent⟩ :=
          exists_first_occurrence_split letter
            (List.count_pos_iff.mp restPositive)
        exact
          ⟨[], middle, after,
            by simp [shape, List.append_assoc], absent⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equal] using count
        obtain ⟨before, middle, after, shape, absent⟩ :=
          exists_consecutive_occurrence_split_of_count_ge_two
            letter restCount
        exact
          ⟨first :: before, middle, after,
            by simp [shape, List.append_assoc], absent⟩

/-- Repeatedly narrow a repeated interval whenever its interior still
contains a repeated letter. The strict decrease in interval length yields an
interval whose endpoint letter is absent from the interior and whose every
interior letter occurs exactly once there. -/
private theorem exists_minimal_repeated_interval
    (letters : List Nat)
    (repeated : ∃ letter, 2 ≤ letters.count letter) :
    ∃ before letter middle after,
      letters = before ++ letter :: middle ++ letter :: after ∧
        letter ∉ middle ∧
          ∀ other, other ∈ middle → middle.count other = 1 := by
  obtain ⟨letter, letterRepeated⟩ := repeated
  obtain ⟨before, middle, after, shape, letterAbsent⟩ :=
    exists_consecutive_occurrence_split_of_count_ge_two
      letter letterRepeated
  by_cases interiorRepeated : ∃ other, 2 ≤ middle.count other
  · obtain ⟨innerBefore, innerLetter, innerMiddle, innerAfter,
        innerShape, innerLetterAbsent, innerSimple⟩ :=
      exists_minimal_repeated_interval middle interiorRepeated
    refine
      ⟨before ++ [letter] ++ innerBefore, innerLetter, innerMiddle,
        innerAfter ++ [letter] ++ after, ?_, innerLetterAbsent,
        innerSimple⟩
    rw [shape, innerShape]
    simp [List.append_assoc]
  · refine ⟨before, letter, middle, after, shape, letterAbsent, ?_⟩
    intro other member
    have positive : 0 < middle.count other :=
      List.count_pos_iff.mpr member
    have atMostOne : ¬2 ≤ middle.count other := by
      intro atLeastTwo
      exact interiorRepeated ⟨other, atLeastTwo⟩
    omega
termination_by letters.length
decreasing_by
  rw [shape]
  simp <;> omega

/-- The selector interface chooses a refinement-minimal repeated-letter
interval inside `gap` whose interior is repeat-free. Every letter strictly
inside that interval must then have another occurrence outside it. This does
not assert length optimality among unrelated repeated intervals. -/
def MinimalRepeatedGapIntervalSelectionObligation : Prop :=
  ∀ (prefixWords gap suffix : List Nat),
    (∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) →
    (∃ letter, 2 ≤ gap.count letter) →
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ∀ other, other ∈ middle →
          other ∈ prefixWords ++ gapPrefix ∨
            other ∈ gapSuffix ++ suffix

/-- Construct the required selector by narrowing to a repeated interval with
repeat-free interior. Since every gap letter is globally multiple, an
interior letter's second occurrence must lie outside the selected interval. -/
theorem minimalRepeatedGapIntervalSelection :
    MinimalRepeatedGapIntervalSelectionObligation := by
  intro prefixWords gap suffix globallyRepeated locallyRepeated
  obtain ⟨gapPrefix, letter, middle, gapSuffix,
      gapShape, letterAbsent, interiorSimple⟩ :=
    exists_minimal_repeated_interval gap locallyRepeated
  refine ⟨gapPrefix, letter, middle, gapSuffix, ?_, ?_⟩
  · simpa [List.append_assoc] using gapShape
  intro other member
  by_cases inLeft : other ∈ prefixWords ++ gapPrefix
  · exact Or.inl inLeft
  by_cases inRight : other ∈ gapSuffix ++ suffix
  · exact Or.inr inRight
  exfalso
  have otherInGap : other ∈ gap := by
    rw [gapShape]
    simp [member]
  have totalAtLeastTwo :=
    globallyRepeated other otherInGap
  have otherNeLetter : other ≠ letter := by
    intro equal
    subst other
    exact letterAbsent member
  have leftZero : (prefixWords ++ gapPrefix).count other = 0 :=
    List.count_eq_zero.mpr inLeft
  have rightZero : (gapSuffix ++ suffix).count other = 0 :=
    List.count_eq_zero.mpr inRight
  have middleOne : middle.count other = 1 :=
    interiorSimple other member
  have totalCountOne :
      (prefixWords ++ gap ++ suffix).count other = 1 := by
    rw [gapShape]
    simp only [List.count_append] at leftZero rightZero
    simp [List.count_append, otherNeLetter, Ne.symm otherNeLetter,
      middleOne, List.append_assoc] <;> omega
  rw [totalCountOne] at totalAtLeastTwo
  omega

/-- Once the refinement-minimal, repeat-free-interior selector is supplied,
the derivational part of one pair extraction is complete: a repeated separator
gap derives to a word with one adjacent square, in the original outer
contexts. -/
theorem listDerivesExtractPairFromRepeatedGap_of_selection
    (selection : MinimalRepeatedGapIntervalSelectionObligation)
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ [letter, letter] ++
            gapSuffix ++ suffix) := by
  obtain ⟨gapPrefix, letter, middle, gapSuffix,
      gapShape, external⟩ :=
    selection prefixWords gap suffix globallyRepeated locallyRepeated
  refine ⟨gapPrefix, letter, middle, gapSuffix, gapShape, ?_⟩
  have gathered :=
    listDerivesGatherExternallyWitnessedPair letter
      (prefixWords ++ gapPrefix) middle (gapSuffix ++ suffix) external
  rw [gapShape]
  simpa [List.append_assoc] using gathered

/-- The same conditional extraction with the adjacent square moved to the
right boundary of the selected gap. This is the form consumed by the square
bank normalizer. -/
theorem listDerivesExtractPairToGapBoundary_of_selection
    (selection : MinimalRepeatedGapIntervalSelectionObligation)
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ gapSuffix ++
            [letter, letter] ++ suffix) := by
  obtain ⟨gapPrefix, letter, middle, gapSuffix,
      gapShape, gathered⟩ :=
    listDerivesExtractPairFromRepeatedGap_of_selection
      selection prefixWords gap suffix globallyRepeated locallyRepeated
  refine ⟨gapPrefix, letter, middle, gapSuffix, gapShape, ?_⟩
  have moved :=
    listDerivesPairAcrossContext
      (prefixWords ++ gapPrefix ++ middle) letter gapSuffix suffix
  exact gathered.trans <| by
    simpa [List.append_assoc] using moved

/-- Unconditional one-pair extraction using the constructed
refinement-minimal, repeat-free-interior selector. -/
theorem listDerivesExtractPairFromRepeatedGap
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ [letter, letter] ++
            gapSuffix ++ suffix) :=
  listDerivesExtractPairFromRepeatedGap_of_selection
    minimalRepeatedGapIntervalSelection prefixWords gap suffix
      globallyRepeated locallyRepeated

/-- Unconditional one-pair extraction in square-bank boundary form. -/
theorem listDerivesExtractPairToGapBoundary
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ gapSuffix ++
            [letter, letter] ++ suffix) :=
  listDerivesExtractPairToGapBoundary_of_selection
    minimalRepeatedGapIntervalSelection prefixWords gap suffix
      globallyRepeated locallyRepeated

/-- Extract every local parity pair from one separator gap. The residue is
one-limited, and the exact count equation certifies that the square-bank
labels account for all removed pairs. The outer contexts remain arbitrary,
so previously extracted pairs may be carried in `suffix`. -/
theorem listDerivesExtractAllGapPairs
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ residue labels,
      ListDerives
        (prefixWords ++ gap ++ suffix)
        (prefixWords ++ residue ++ renderSquareBank labels ++ suffix) ∧
        (∀ tested,
          gap.count tested =
            residue.count tested + 2 * labels.count tested) ∧
          ∀ tested, residue.count tested ≤ 1 := by
  by_cases locallyRepeated : ∃ letter, 2 ≤ gap.count letter
  · obtain ⟨gapPrefix, letter, middle, gapSuffix,
        gapShape, extracted⟩ :=
      listDerivesExtractPairToGapBoundary
        prefixWords gap suffix globallyRepeated locallyRepeated
    let reduced := gapPrefix ++ middle ++ gapSuffix
    have reducedShorter : reduced.length < gap.length := by
      rw [gapShape]
      simp [reduced] <;> omega
    have reducedGloballyRepeated :
        ∀ tested, tested ∈ reduced →
          2 ≤
            (prefixWords ++ reduced ++
              ([letter, letter] ++ suffix)).count tested := by
      intro tested memberReduced
      have memberGap : tested ∈ gap := by
        dsimp [reduced] at memberReduced
        rcases List.mem_append.mp memberReduced with
          memberLeft | memberSuffix
        · rcases List.mem_append.mp memberLeft with
            memberPrefix | memberMiddle
          · rw [gapShape]
            simp [memberPrefix]
          · rw [gapShape]
            simp [memberMiddle]
        · rw [gapShape]
          simp [memberSuffix]
      have original := globallyRepeated tested memberGap
      have rearrangedCount :
          (prefixWords ++ reduced ++
            ([letter, letter] ++ suffix)).count tested =
            (prefixWords ++ gap ++ suffix).count tested := by
        rw [gapShape]
        dsimp [reduced]
        simp only [List.count_append, List.count_cons, List.count_nil]
        omega
      rw [rearrangedCount]
      exact original
    obtain ⟨residue, labels, recurse, reducedCounts, residueLimited⟩ :=
      listDerivesExtractAllGapPairs
        prefixWords reduced ([letter, letter] ++ suffix)
          reducedGloballyRepeated
    have combined := extracted.trans <| by
      simpa [reduced, List.append_assoc] using recurse
    refine ⟨residue, labels ++ [letter], ?_, ?_, residueLimited⟩
    · simpa [renderSquareBank, List.flatMap_append,
        List.append_assoc] using combined
    · intro tested
      have reducedCount := reducedCounts tested
      rw [gapShape]
      dsimp [reduced] at reducedCount
      by_cases equal : letter = tested
      · subst tested
        simp [List.count_append] at reducedCount ⊢
        omega
      · simp [List.count_append, equal, Ne.symm equal] at reducedCount
        simp [List.count_append, equal, Ne.symm equal] <;> omega
  · refine ⟨gap, [], ?_, ?_, ?_⟩
    · simpa [renderSquareBank, List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis)
          (prefixWords ++ gap ++ suffix)
    · intro tested
      simp [renderSquareBank]
    · intro tested
      have notTwo : ¬2 ≤ gap.count tested := by
        intro atLeastTwo
        exact locallyRepeated ⟨tested, atLeastTwo⟩
      omega
termination_by gap.length
decreasing_by
  exact reducedShorter

/-- A label occurs in a rendered square bank exactly when it occurs in the
label list. -/
theorem mem_renderSquareBank_iff (letter : Nat) (labels : List Nat) :
    letter ∈ renderSquareBank labels ↔ letter ∈ labels := by
  induction labels with
  | nil => simp [renderSquareBank]
  | cons head tail induction =>
      simp [renderSquareBank, induction]

/-- Deterministic order for the one-limited parity residue of a gap. -/
def canonicalGapResidue (residue : List Nat) : List Nat :=
  residue.mergeSort (fun left right => decide (left ≤ right))

/-- Every residue letter has a witness outside the residue after all local
pairs have been extracted. A witness is either in the original left context,
in the extracted square bank, or in the original right context. -/
theorem residueLetterExternalAfterPairExtraction
    (prefixWords gap suffix residue labels : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (counts : ∀ tested,
      gap.count tested =
        residue.count tested + 2 * labels.count tested)
    (residueLimited : ∀ tested, residue.count tested ≤ 1)
    (letter : Nat) (member : letter ∈ residue) :
    letter ∈ prefixWords ∨
      letter ∈ renderSquareBank labels ++ suffix := by
  by_cases inPrefix : letter ∈ prefixWords
  · exact Or.inl inPrefix
  by_cases inSuffix : letter ∈ suffix
  · exact Or.inr (List.mem_append_right _ inSuffix)
  have residuePositive : 0 < residue.count letter :=
    List.count_pos_iff.mpr member
  have residueOne : residue.count letter = 1 := by
    have bound := residueLimited letter
    omega
  have countEq := counts letter
  have gapPositive : 0 < gap.count letter := by
    omega
  have totalAtLeastTwo :=
    globallyRepeated letter (List.count_pos_iff.mp gapPositive)
  have prefixZero : prefixWords.count letter = 0 :=
    List.count_eq_zero.mpr inPrefix
  have suffixZero : suffix.count letter = 0 :=
    List.count_eq_zero.mpr inSuffix
  have labelsPositive : 0 < labels.count letter := by
    simp [List.count_append, prefixZero, suffixZero, countEq,
      residueOne] at totalAtLeastTwo
    omega
  have labelMember : letter ∈ labels :=
    List.count_pos_iff.mp labelsPositive
  exact Or.inr <|
    List.mem_append_left suffix <|
      (mem_renderSquareBank_iff letter labels).mpr labelMember

/-- Every separator gap derives to a parity residue followed by a canonical
square bank. The residue contains each letter at most once and records exactly
the local occurrence parity. The labels before canonical deduplication retain
the exact pair-count certificate. -/
theorem listDerivesNormalizeSeparatorGapPairBank
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ residue labels,
      ListDerives
        (prefixWords ++ gap ++ suffix)
        (prefixWords ++ residue ++
          renderSquareBank (canonicalSquareBank labels) ++ suffix) ∧
        (∀ tested,
          gap.count tested =
            residue.count tested + 2 * labels.count tested) ∧
        (∀ tested, residue.count tested ≤ 1) ∧
          ∀ tested,
            residue.count tested = gap.count tested % 2 := by
  obtain ⟨residue, labels, extracted, counts, residueLimited⟩ :=
    listDerivesExtractAllGapPairs
      prefixWords gap suffix globallyRepeated
  have canonicalized :=
    S5_107.ListDerives.context
      (basis := basis) (prefixWords ++ residue) suffix
      (listDerivesCanonicalSquareBank labels)
  refine ⟨residue, labels, extracted.trans ?_, counts,
    residueLimited, ?_⟩
  · simpa [List.append_assoc] using canonicalized
  · intro tested
    have countEq := counts tested
    have limited := residueLimited tested
    omega

/-- The residue-permutation interface asks only for permuting a one-limited
residue when every displayed residue letter has a witness in an outer
context. -/
def ExternallyWitnessedResiduePermutationObligation : Prop :=
  ∀ (prefixWords source target suffix : List Nat),
    source.Perm target →
    (∀ letter, letter ∈ source →
      letter ∈ prefixWords ∨ letter ∈ suffix) →
    (∀ letter, source.count letter ≤ 1) →
    ListDerives
      (prefixWords ++ source ++ suffix)
      (prefixWords ++ target ++ suffix)

/-- Adjacent externally witnessed swaps lift to every permutation of a
one-limited residue. -/
theorem externallyWitnessedResiduePermutation :
    ExternallyWitnessedResiduePermutationObligation := by
  intro prefixWords source target suffix permutation external limited
  induction permutation generalizing prefixWords with
  | nil =>
      simpa using
        S5_107.ListDerives.refl (basis := basis) (prefixWords ++ suffix)
  | cons head _ induction =>
      have derivation :=
        induction (prefixWords ++ [head]) (by
          intro letter member
          rcases external letter (List.Mem.tail head member) with
            inPrefix | inSuffix
          · exact Or.inl (List.mem_append_left [head] inPrefix)
          · exact Or.inr inSuffix) (by
          intro letter
          have fullBound := limited letter
          simp only [List.count_cons] at fullBound
          omega)
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have secondExternal : second ∈ prefixWords ∨ second ∈ suffix :=
        external second (by simp)
      have firstExternal : first ∈ prefixWords ∨ first ∈ suffix :=
        external first (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapExternallyWitnessedAdjacent
          prefixWords [] second first rest suffix
            secondExternal firstExternal
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction prefixWords external limited
      have secondDerivation :=
        secondInduction prefixWords (by
          intro letter member
          exact external letter
            ((firstPermutation.mem_iff).mpr member)) (by
          intro letter
          rw [← firstPermutation.count letter]
          exact limited letter)
      exact firstDerivation.trans secondDerivation

/-- Full canonical normalization of an explicitly supplied separator gap:
sort the one-limited parity residue using outer witnesses, then deduplicate
and sort its extracted square bank. -/
theorem listDerivesCanonicalSeparatorGap
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ residue labels,
      ListDerives
        (prefixWords ++ gap ++ suffix)
        (prefixWords ++ canonicalGapResidue residue ++
          renderSquareBank (canonicalSquareBank labels) ++ suffix) ∧
        (∀ tested,
          gap.count tested =
            residue.count tested + 2 * labels.count tested) ∧
        (∀ tested, residue.count tested ≤ 1) ∧
          ∀ tested,
            residue.count tested = gap.count tested % 2 := by
  obtain ⟨residue, labels, extracted, counts, residueLimited⟩ :=
    listDerivesExtractAllGapPairs
      prefixWords gap suffix globallyRepeated
  have residueExternal : ∀ letter, letter ∈ residue →
      letter ∈ prefixWords ∨
        letter ∈ renderSquareBank labels ++ suffix := by
    intro letter member
    exact residueLetterExternalAfterPairExtraction
      prefixWords gap suffix residue labels globallyRepeated counts
        residueLimited letter member
  have residueSorted :=
    externallyWitnessedResiduePermutation
      prefixWords residue (canonicalGapResidue residue)
        (renderSquareBank labels ++ suffix)
        (List.mergeSort_perm _ _).symm residueExternal residueLimited
  have canonicalized :=
    S5_107.ListDerives.context
      (basis := basis)
      (prefixWords ++ canonicalGapResidue residue) suffix
      (listDerivesCanonicalSquareBank labels)
  have normalized := extracted.trans <| by
    simpa [List.append_assoc] using residueSorted
  refine ⟨residue, labels, normalized.trans ?_, counts,
    residueLimited, ?_⟩
  · simpa [List.append_assoc] using canonicalized
  · intro tested
    have countEq := counts tested
    have limited := residueLimited tested
    omega

/-! ## Whole-word simple-separator decomposition -/

/-- A whole word is assembled from repeated-letter gaps separated by letters
that occur exactly once in the whole word. The final gap follows the last
separator. The source word is an index of the relation, so reconstruction is
recorded by the constructors rather than by a separate equality. -/
inductive GloballySimpleSeparatorDecomposition (whole : List Nat) :
    List Nat → List (List Nat × Nat) → List Nat → Prop where
  | final (gap : List Nat)
      (gapRepeated :
        ∀ letter, letter ∈ gap → 2 ≤ whole.count letter) :
      GloballySimpleSeparatorDecomposition whole gap [] gap
  | step (gap : List Nat) (separator : Nat) (remainder : List Nat)
      (segments : List (List Nat × Nat)) (finalGap : List Nat)
      (separatorSimple : whole.count separator = 1)
      (gapRepeated :
        ∀ letter, letter ∈ gap → 2 ≤ whole.count letter)
      (tail :
        GloballySimpleSeparatorDecomposition
          whole remainder segments finalGap) :
      GloballySimpleSeparatorDecomposition
        whole (gap ++ separator :: remainder)
          ((gap, separator) :: segments) finalGap

private theorem prependRepeatedToSeparatorDecomposition
    {whole remaining : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (letter : Nat) (letterRepeated : 2 ≤ whole.count letter)
    (decomposition :
      GloballySimpleSeparatorDecomposition
        whole remaining segments finalGap) :
    ∃ newSegments newFinalGap,
      GloballySimpleSeparatorDecomposition
        whole (letter :: remaining) newSegments newFinalGap := by
  induction decomposition with
  | final gap gapRepeated =>
      refine ⟨[], letter :: gap, .final (letter :: gap) ?_⟩
      intro tested member
      rcases List.mem_cons.mp member with equal | inGap
      · subst tested
        exact letterRepeated
      · exact gapRepeated tested inGap
  | step gap separator remainder restSegments restFinal
      separatorSimple gapRepeated tail _tailInduction =>
      have extendedRepeated :
          ∀ tested, tested ∈ letter :: gap →
            2 ≤ whole.count tested := by
        intro tested member
        rcases List.mem_cons.mp member with equal | inGap
        · subst tested
          exact letterRepeated
        · exact gapRepeated tested inGap
      refine
        ⟨(letter :: gap, separator) :: restSegments, restFinal, ?_⟩
      simpa using
        GloballySimpleSeparatorDecomposition.step
          (whole := whole) (gap := letter :: gap)
          (separator := separator) (remainder := remainder)
          (segments := restSegments) (finalGap := restFinal)
          separatorSimple extendedRepeated tail

private theorem existsGloballySimpleSeparatorDecompositionAux
    (whole : List Nat) :
    ∀ remaining : List Nat,
      (∀ letter, letter ∈ remaining → letter ∈ whole) →
      ∃ segments finalGap,
        GloballySimpleSeparatorDecomposition
          whole remaining segments finalGap
  | [], _ => by
      exact ⟨[], [], .final [] (by simp)⟩
  | head :: tail, contained => by
      have tailContained :
          ∀ letter, letter ∈ tail → letter ∈ whole := by
        intro letter member
        exact contained letter (List.mem_cons_of_mem head member)
      obtain ⟨segments, finalGap, decomposition⟩ :=
        existsGloballySimpleSeparatorDecompositionAux
          whole tail tailContained
      by_cases simple : whole.count head = 1
      · refine ⟨([], head) :: segments, finalGap, ?_⟩
        simpa using
          GloballySimpleSeparatorDecomposition.step
            (whole := whole) (gap := []) (separator := head)
            (remainder := tail) (segments := segments)
            (finalGap := finalGap) simple (by simp) decomposition
      · have headMember : head ∈ whole :=
          contained head (by simp)
        have positive : 0 < whole.count head :=
          List.count_pos_iff.mpr headMember
        have repeated : 2 ≤ whole.count head := by omega
        exact prependRepeatedToSeparatorDecomposition
          head repeated decomposition

/-- Every whole word admits a decomposition at all globally simple letters.
Every intervening gap, including the final gap, contains only letters that
occur at least twice in the original whole word. This is the combinatorial
decomposition needed by later derivational assembly; it does not normalize
the gaps or move their extracted square banks. -/
theorem existsGloballySimpleSeparatorDecomposition (whole : List Nat) :
    ∃ segments finalGap,
      GloballySimpleSeparatorDecomposition
        whole whole segments finalGap := by
  exact existsGloballySimpleSeparatorDecompositionAux
    whole whole (by
      intro letter member
      exact member)

end SemigroupBasis.CoRoots.S5_254
