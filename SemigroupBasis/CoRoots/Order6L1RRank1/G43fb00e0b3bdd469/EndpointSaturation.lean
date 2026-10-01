import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.EndpointConnectivity

/-!
# Exact trim-and-saturate stage for G43 endpoint connectivity

This off-tree module uses only the fresh semantic bridge, the corrected
contextual frozen-path RTC, and the endpoint representation.  It does not
import the retired G43 `Primitives`, `Normalization`, or `Completeness`
modules.

The trim deletes one of three displayed occurrences by one of paths 00000,
00001, 00002, and 00007.  Saturation duplicates a sole nonfinal occurrence
by path 00001 in reverse.  In particular, every output singleton is the
literal final letter; this is proved below rather than added as an input.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Small list and word bridges -/

private def endpointWordOfNonemptyList :
    (letters : List Nat) → letters ≠ [] → Word Nat
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => Word.mk head tail

@[simp]
private theorem endpointWordOfNonemptyList_toList
    (letters : List Nat) (nonempty : letters ≠ []) :
    (endpointWordOfNonemptyList letters nonempty).toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word with
  | mk head tail => simp [Word.toList]

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal,
            reverseEqual, member, List.filter_append]

private theorem firstOccurrenceSequence_duplicate_adjacent
    (before after : List Nat) (letter : Nat) :
    firstOccurrenceSequence
        (before ++ letter :: letter :: after) =
      firstOccurrenceSequence (before ++ letter :: after) := by
  induction before with
  | nil =>
      simp [firstOccurrenceSequence, List.filter_filter]
  | cons head before inductionHypothesis =>
      simp only [List.cons_append, firstOccurrenceSequence]
      rw [inductionHypothesis]

private theorem factorPrefix_eq_prefixFirstOccurrences
    (word : Word Nat) :
    (jointSignature word).factorNormal.dropLast =
      prefixFirstOccurrences word := by
  change (s4_64Normal word).toList.dropLast =
    prefixFirstOccurrences word
  rw [s4_64Normal_toList_eq_s4_64ProofNormal,
    s4_64ProofNormal_dropLast]

/-! ## Exact one-step deletion and duplication macros -/

private def endpointSingletonWord (letter : Nat) : Word Nat :=
  Word.singleton letter

private theorem contextualFrozenTrimThird
    (before firstGap secondGap after : List Nat) (letter : Nat) :
    ContextualFrozenRTC
      (before ++ letter :: firstGap ++ letter ::
        secondGap ++ letter :: after)
      (before ++ letter :: firstGap ++ secondGap ++
        letter :: after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          let rule : FrozenPathInstantiation :=
            { index := .path00000
              V0 := endpointSingletonWord letter
              V1 := endpointSingletonWord letter
              V2 := endpointSingletonWord letter
              V3 := endpointSingletonWord letter }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [letter, letter] ++ after)
          · exact ⟨witness, by
              simp [witness, rule, endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness, rule, endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [letter, letter] ++ after))
      | cons secondHead secondTail =>
          let secondAndFinal : Word Nat :=
            Word.mk secondHead (secondTail ++ [letter])
          let rule : FrozenPathInstantiation :=
            { index := .path00001
              V0 := endpointSingletonWord letter
              V1 := secondAndFinal
              V2 := endpointSingletonWord letter
              V3 := endpointSingletonWord letter }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [letter] ++
              (secondHead :: secondTail) ++ [letter] ++ after)
          · exact ⟨witness, by
              simp [witness, rule, secondAndFinal,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness, rule, secondAndFinal,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [letter] ++ (secondHead :: secondTail) ++
                  [letter] ++ after))
  | cons firstHead firstTail =>
      let firstWord : Word Nat := Word.mk firstHead firstTail
      cases secondGap with
      | nil =>
          let rule : FrozenPathInstantiation :=
            { index := .path00002
              V0 := endpointSingletonWord letter
              V1 := firstWord
              V2 := endpointSingletonWord letter
              V3 := endpointSingletonWord letter }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [letter] ++
              (firstHead :: firstTail) ++ [letter] ++ after)
          · exact ⟨witness, by
              simp [witness, rule, firstWord,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness, rule, firstWord,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [letter] ++ (firstHead :: firstTail) ++
                  [letter] ++ after))
      | cons secondHead secondTail =>
          let secondWord : Word Nat := Word.mk secondHead secondTail
          let rule : FrozenPathInstantiation :=
            { index := .path00007
              V0 := endpointSingletonWord letter
              V1 := firstWord
              V2 := secondWord
              V3 := endpointSingletonWord letter }
          let witness : ContextualFrozenWitness :=
            ⟨rule, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [letter] ++ (firstHead :: firstTail) ++
              (secondHead :: secondTail) ++ [letter] ++ after)
          · exact ⟨witness, by
              simp [witness, rule, firstWord, secondWord,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness, rule, firstWord, secondWord,
                endpointSingletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [letter] ++ (firstHead :: firstTail) ++
                  (secondHead :: secondTail) ++ [letter] ++ after))

private theorem contextualFrozenDuplicateNonfinal
    (before after : List Nat) (letter final : Nat) :
    ContextualFrozenRTC
      (before ++ letter :: after ++ [final])
      (before ++ letter :: letter :: after ++ [final]) := by
  let tailWord : Word Nat :=
    endpointWordOfNonemptyList (after ++ [final]) (by simp)
  have tailWordList : tailWord.toList = after ++ [final] := by
    simp [tailWord]
  let rule : FrozenPathInstantiation :=
    { index := .path00001
      V0 := endpointSingletonWord letter
      V1 := tailWord
      V2 := endpointSingletonWord letter
      V3 := endpointSingletonWord letter }
  let witness : ContextualFrozenWitness :=
    ⟨rule, .reverse, before, []⟩
  apply ContextualFrozenRTC.cons
    (middle := before ++ [letter, letter] ++ after ++ [final])
  · exact ⟨witness, by
      simp [witness, rule, endpointSingletonWord, tailWordList,
        ContextualFrozenWitness.source,
        ContextualFrozenWitness.target,
        ContextualFrozenWitness.coreSource,
        ContextualFrozenWitness.coreTarget,
        FrozenPathInstantiation.source,
        FrozenPathInstantiation.target,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc]
      simpa only [Word.toList] using
        congrArg (List.cons letter) tailWordList.symm, by
      simp [witness, rule, endpointSingletonWord, tailWordList,
        ContextualFrozenWitness.source,
        ContextualFrozenWitness.target,
        ContextualFrozenWitness.coreSource,
        ContextualFrozenWitness.coreTarget,
        FrozenPathInstantiation.source,
        FrozenPathInstantiation.target,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc]
      simpa only [Word.toList] using
        congrArg
          (fun remaining : List Nat => letter :: letter :: remaining)
          tailWordList.symm⟩
  · simpa [List.append_assoc] using
      (ContextualFrozenRTC.refl
        (before ++ [letter, letter] ++ after ++ [final]))

/-! ## Count trimming -/

private theorem exists_two_occurrence_split_of_count_ge_two
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp
            (List.count_pos_iff.mp restPositive)
        exact ⟨[], middle, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem exists_three_occurrence_split_of_count_ge_three
    (letter : Nat) :
    ∀ {letters : List Nat},
      3 ≤ letters.count letter →
        ∃ before firstGap secondGap after,
          letters = before ++ letter :: firstGap ++ letter ::
            secondGap ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter restCount
        exact ⟨[], firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          exists_three_occurrence_split_of_count_ge_three
            letter restCount
        exact ⟨first :: before, firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩

private theorem trimToTwoLimited
    (letters : List Nat) (nonempty : letters ≠ []) :
    ∃ trimmed,
      ContextualFrozenRTC letters trimmed ∧
      trimmed ≠ [] ∧
      (∀ tested, trimmed.count tested ≤ 2) ∧
      (∀ tested, tested ∈ trimmed ↔ tested ∈ letters) := by
  by_cases limited : ∀ tested, letters.count tested ≤ 2
  · exact ⟨letters, ContextualFrozenRTC.refl letters,
      nonempty, limited, fun _ => Iff.rfl⟩
  · have tooMany : ∃ tested, 3 ≤ letters.count tested := by
      apply Classical.byContradiction
      intro absent
      apply limited
      intro tested
      have notTooMany : ¬ 3 ≤ letters.count tested := by
        intro count
        exact absent ⟨tested, count⟩
      omega
    obtain ⟨letter, count⟩ := tooMany
    obtain ⟨before, firstGap, secondGap, after, shape⟩ :=
      exists_three_occurrence_split_of_count_ge_three letter count
    let next :=
      before ++ letter :: firstGap ++ secondGap ++ letter :: after
    have oneStep : ContextualFrozenRTC letters next := by
      rw [shape]
      exact contextualFrozenTrimThird
        before firstGap secondGap after letter
    have nextNonempty : next ≠ [] := by
      have selectedMember : letter ∈ next := by
        simp [next]
      exact List.ne_nil_of_mem selectedMember
    have nextShorter : next.length < letters.length := by
      rw [shape]
      simp only [next, List.length_append, List.length_cons,
        List.length_nil]
      omega
    have nextSupport :
        ∀ tested, tested ∈ next ↔ tested ∈ letters := by
      intro tested
      rw [shape]
      simp [next, or_assoc, or_left_comm, or_comm]
    obtain ⟨trimmed, recurse, trimmedNonempty,
        trimmedLimited, recurseSupport⟩ :=
      trimToTwoLimited next nextNonempty
    exact ⟨trimmed,
      ContextualFrozenRTC.trans oneStep recurse, trimmedNonempty,
      trimmedLimited, fun tested =>
        (recurseSupport tested).trans (nextSupport tested)⟩
termination_by letters.length
decreasing_by exact nextShorter

/-! ## Saturating the selected first-occurrence key -/

private theorem saturateTargets :
    ∀ (targets stem : List Nat) (final : Nat),
      targets.Nodup →
      (∀ tested, (stem ++ [final]).count tested ≤ 2) →
      (∀ tested, tested ∈ targets → tested ∈ stem) →
      ∃ nextStem,
        ContextualFrozenRTC
          (stem ++ [final]) (nextStem ++ [final]) ∧
        (∀ tested, tested ∈ nextStem ↔ tested ∈ stem) ∧
        firstOccurrenceSequence nextStem =
          firstOccurrenceSequence stem ∧
        (∀ tested,
          (nextStem ++ [final]).count tested =
            if tested ∈ targets then
              2
            else
              (stem ++ [final]).count tested)
  | [], stem, final, _, limited, _ => by
      exact ⟨stem, ContextualFrozenRTC.refl _,
        fun _ => Iff.rfl, rfl, by simp⟩
  | selected :: rest, stem, final, nodup, limited, targetInStem => by
      have nodupData := List.nodup_cons.mp nodup
      have selectedNotRest : selected ∉ rest := nodupData.1
      have restNodup : rest.Nodup := nodupData.2
      have restInStem :
          ∀ tested, tested ∈ rest → tested ∈ stem := by
        intro tested member
        exact targetInStem tested (List.Mem.tail selected member)
      have selectedMember : selected ∈ stem :=
        targetInStem selected (List.Mem.head rest)
      have selectedPositive :
          0 < (stem ++ [final]).count selected :=
        List.count_pos_iff.mpr
          (List.mem_append_left [final] selectedMember)
      by_cases alreadyTwo :
          (stem ++ [final]).count selected = 2
      · obtain ⟨nextStem, reachable, sameSupport,
            sameFirsts, counts⟩ :=
          saturateTargets rest stem final restNodup limited restInStem
        refine ⟨nextStem, reachable, sameSupport, sameFirsts, ?_⟩
        intro tested
        rw [counts]
        by_cases equal : tested = selected
        · subst tested
          simp [selectedNotRest, alreadyTwo]
        · simp [equal]
      · have selectedOne :
            (stem ++ [final]).count selected = 1 := by
          have selectedBound := limited selected
          omega
        obtain ⟨before, after, stemShape⟩ :=
          List.mem_iff_append.mp selectedMember
        let enlargedStem :=
          before ++ selected :: selected :: after
        have oneStep :
            ContextualFrozenRTC
              (stem ++ [final]) (enlargedStem ++ [final]) := by
          rw [stemShape]
          exact contextualFrozenDuplicateNonfinal
            before after selected final
        have oneCounts : ∀ tested,
            (enlargedStem ++ [final]).count tested =
              if tested = selected then
                2
              else
                (stem ++ [final]).count tested := by
          intro tested
          by_cases equal : tested = selected
          · subst tested
            rw [stemShape] at selectedOne
            rw [if_pos rfl]
            change
              ((before ++ selected :: selected :: after) ++
                [final]).count selected = 2
            simp only [List.count_append,
              List.count_cons_self, List.count_nil] at selectedOne ⊢
            omega
          · rw [stemShape]
            simp [enlargedStem, List.count_append, equal,
              Ne.symm equal]
        have enlargedLimited :
            ∀ tested, (enlargedStem ++ [final]).count tested ≤ 2 := by
          intro tested
          rw [oneCounts]
          by_cases equal : tested = selected
          · simp [equal]
          · simp [equal]
            simpa only [List.count_append] using limited tested
        have enlargedSupport : ∀ tested,
            tested ∈ enlargedStem ↔ tested ∈ stem := by
          intro tested
          rw [stemShape]
          simp [enlargedStem]
        have restInEnlarged :
            ∀ tested, tested ∈ rest → tested ∈ enlargedStem := by
          intro tested member
          exact (enlargedSupport tested).mpr
            (restInStem tested member)
        obtain ⟨nextStem, recurse, recurseSupport,
            recurseFirsts, recurseCounts⟩ :=
          saturateTargets rest enlargedStem final restNodup
            enlargedLimited restInEnlarged
        refine ⟨nextStem,
          ContextualFrozenRTC.trans oneStep recurse, ?_, ?_, ?_⟩
        · intro tested
          exact (recurseSupport tested).trans
            (enlargedSupport tested)
        · have duplicateFirsts :
              firstOccurrenceSequence enlargedStem =
                firstOccurrenceSequence stem := by
            rw [stemShape]
            exact firstOccurrenceSequence_duplicate_adjacent
              before after selected
          exact recurseFirsts.trans duplicateFirsts
        · intro tested
          rw [recurseCounts, oneCounts]
          by_cases equal : tested = selected
          · subst tested
            simp [selectedNotRest]
          · by_cases member : tested ∈ rest <;>
              simp [equal, member]

/-! ## Endpoint projections of a two-limited saturated list -/

private theorem firstProjection_tagEndpoints_filter
    (letters : List Nat)
    (limited : ∀ tested, letters.count tested ≤ 2) :
    firstProjection (tagEndpoints letters) =
      (firstOccurrenceSequence letters).filter
        (fun tested => decide (letters.count tested = 2)) := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      have restLimited : ∀ tested, rest.count tested ≤ 2 := by
        intro tested
        have bound := limited tested
        simp only [List.count_cons] at bound
        omega
      have induction := inductionHypothesis restLimited
      by_cases later : letter ∈ rest
      · have restPositive : 0 < rest.count letter :=
          List.count_pos_iff.mpr later
        have wholeTwo : (letter :: rest).count letter = 2 := by
          have bound := limited letter
          simp only [List.count_cons_self] at bound ⊢
          omega
        have restOne : rest.count letter = 1 := by
          simp only [List.count_cons_self] at wholeTwo
          omega
        simp only [tagEndpoints, later, if_pos,
          EndpointTag.first, firstProjection, firstOccurrenceSequence,
          List.filter_cons]
        rw [if_pos (by simp [wholeTwo])]
        rw [induction]
        congr 1
        rw [List.filter_filter]
        apply List.filter_congr
        intro tested member
        by_cases equal : tested = letter
        · subst tested
          simp [restOne]
        · simp [equal, Ne.symm equal]
      · have restZero : rest.count letter = 0 :=
          List.count_eq_zero.mpr later
        have wholeOne : (letter :: rest).count letter = 1 := by
          simp [restZero]
        simp only [tagEndpoints, later, if_neg,
          EndpointTag.last, firstProjection, firstOccurrenceSequence,
          List.filter_cons]
        change firstProjection (tagEndpoints rest) = _
        rw [if_neg (by simp [wholeOne])]
        rw [induction]
        rw [List.filter_filter]
        apply List.filter_congr
        intro tested member
        have testedInRest : tested ∈ rest :=
          (mem_firstOccurrenceSequence_iff tested rest).mp member
        have different : tested ≠ letter := by
          intro equal
          subst tested
          exact later testedInRest
        simp [different, Ne.symm different]

private theorem lastProjection_tagEndpoints :
    ∀ letters : List Nat,
      lastProjection (tagEndpoints letters) =
        lastOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      by_cases later : letter ∈ rest <;>
        simp [tagEndpoints, lastProjection,
          EndpointTag.first, EndpointTag.last,
          lastOccurrenceSequence, later,
          lastProjection_tagEndpoints rest]

private theorem firstProjection_saturated_append_final
    (stem : List Nat) (final : Nat)
    (limited : ∀ tested, (stem ++ [final]).count tested ≤ 2)
    (singletonFinal : ∀ tested,
      (stem ++ [final]).count tested = 1 →
        (stem ++ [final]).getLast? = some tested) :
    firstProjection (tagEndpoints (stem ++ [final])) =
      firstOccurrenceSequence stem := by
  have stemDouble : ∀ tested, tested ∈ stem →
      (stem ++ [final]).count tested = 2 := by
    intro tested member
    have positive : 0 < (stem ++ [final]).count tested :=
      List.count_pos_iff.mpr
        (List.mem_append_left [final] member)
    by_cases one : (stem ++ [final]).count tested = 1
    · have lastEq := singletonFinal tested one
      have testedEqFinal : tested = final := by
        simpa using lastEq.symm
      subst final
      have stemPositive : 0 < stem.count tested :=
        List.count_pos_iff.mpr member
      rw [List.count_append] at one
      simp only [List.count_singleton_self] at one
      omega
    · have bound := limited tested
      omega
  rw [firstProjection_tagEndpoints_filter (stem ++ [final]) limited]
  rw [firstOccurrenceSequence_append_singleton]
  by_cases finalMember : final ∈ stem
  · rw [if_pos finalMember]
    apply List.filter_eq_self.mpr
    intro tested member
    have inStem :=
      (mem_firstOccurrenceSequence_iff tested stem).mp member
    simp [stemDouble tested inStem]
  · rw [if_neg finalMember, List.filter_append]
    have keepStem :
        (firstOccurrenceSequence stem).filter
            (fun tested =>
              decide ((stem ++ [final]).count tested = 2)) =
          firstOccurrenceSequence stem := by
      apply List.filter_eq_self.mpr
      intro tested member
      have inStem :=
        (mem_firstOccurrenceSequence_iff tested stem).mp member
      simp [stemDouble tested inStem]
    rw [keepStem]
    have finalZero : stem.count final = 0 :=
      List.count_eq_zero.mpr finalMember
    simp [finalZero]

/-- If every old stem letter is among the saturated targets, a count-one
letter in the enlarged word can only be the unchanged literal final letter.
This is the exact `SaturatedEndpointState.singletonFinal` boundary. -/
private theorem singletonFinal_of_saturatedTargets
    (targets stem nextStem : List Nat) (final : Nat)
    (targetsCoverStem : ∀ tested, tested ∈ stem → tested ∈ targets)
    (sameStemSupport : ∀ tested,
      tested ∈ nextStem ↔ tested ∈ stem)
    (targetsDouble : ∀ tested,
      tested ∈ targets →
        (nextStem ++ [final]).count tested = 2) :
    ∀ tested,
      (nextStem ++ [final]).count tested = 1 →
        (nextStem ++ [final]).getLast? = some tested := by
  intro tested countOne
  have member : tested ∈ nextStem ++ [final] :=
    List.count_pos_iff.mp (by omega)
  have stemOrFinal : tested ∈ nextStem ∨ tested = final := by
    simpa using member
  rcases stemOrFinal with inNextStem | equalFinal
  · have inStem : tested ∈ stem :=
      (sameStemSupport tested).mp inNextStem
    have double := targetsDouble tested (targetsCoverStem tested inStem)
    omega
  · subst tested
    simp

/-! ## Construction of the saturated endpoint state -/

/-- Every nonempty G43 word reaches a two-limited state in which all letters
of the factor key occur twice and every remaining singleton is the literal
final letter. -/
theorem existsSaturatedEndpointState (anchor : Word Nat) :
    ∃ letters,
      ContextualFrozenRTC anchor.toList letters ∧
      SaturatedEndpointState anchor letters := by
  obtain ⟨trimmed, trimRoute, trimmedNonempty,
      trimmedLimited, trimmedSupport⟩ :=
    trimToTwoLimited anchor.toList (word_toList_ne_nil anchor)
  let trimmedWord : Word Nat :=
    endpointWordOfNonemptyList trimmed trimmedNonempty
  have trimRouteWords :
      ContextualFrozenRTC anchor.toList trimmedWord.toList := by
    simpa [trimmedWord] using trimRoute
  have signatureTrimmed :
      jointSignature anchor = jointSignature trimmedWord :=
    jointSignature_eq_of_derives
      (contextualFrozenRTC_derives trimRouteWords)
  let stem := (splitPrefixFinal trimmedWord).1
  let final := (splitPrefixFinal trimmedWord).2
  have trimmedShape : trimmed = stem ++ [final] := by
    calc
      trimmed = trimmedWord.toList := by simp [trimmedWord]
      _ = stem ++ [final] := by
        simpa [stem, final] using toList_eq_splitPrefixFinal trimmedWord
  let targets := (jointSignature anchor).factorNormal.dropLast
  have targetsEq : targets = firstOccurrenceSequence stem := by
    calc
      targets = (jointSignature anchor).factorNormal.dropLast := rfl
      _ = (jointSignature trimmedWord).factorNormal.dropLast :=
        congrArg
          (fun signature : JointSignature =>
            signature.factorNormal.dropLast)
          signatureTrimmed
      _ = prefixFirstOccurrences trimmedWord :=
        factorPrefix_eq_prefixFirstOccurrences trimmedWord
      _ = firstOccurrenceSequence stem := rfl
  have targetsNodup : targets.Nodup := by
    rw [targetsEq]
    exact firstOccurrenceSequence_nodup stem
  have targetsInStem :
      ∀ tested, tested ∈ targets → tested ∈ stem := by
    intro tested member
    rw [targetsEq] at member
    exact (mem_firstOccurrenceSequence_iff tested stem).mp member
  have stemLimited :
      ∀ tested, (stem ++ [final]).count tested ≤ 2 := by
    intro tested
    rw [← trimmedShape]
    exact trimmedLimited tested
  obtain ⟨nextStem, saturationRoute, sameStemSupport,
      sameFirstOccurrences, saturationCounts⟩ :=
    saturateTargets targets stem final targetsNodup
      stemLimited targetsInStem
  let letters := nextStem ++ [final]
  have saturationFromTrimmed :
      ContextualFrozenRTC trimmed letters := by
    rw [trimmedShape]
    exact saturationRoute
  have completeRoute :
      ContextualFrozenRTC anchor.toList letters :=
    ContextualFrozenRTC.trans trimRoute saturationFromTrimmed
  have lettersNonempty : letters ≠ [] := by
    simp [letters]
  let lettersWord : Word Nat :=
    endpointWordOfNonemptyList letters lettersNonempty
  have completeRouteWords :
      ContextualFrozenRTC anchor.toList lettersWord.toList := by
    simpa [lettersWord] using completeRoute
  have signatureLetters :
      jointSignature anchor = jointSignature lettersWord :=
    jointSignature_eq_of_derives
      (contextualFrozenRTC_derives completeRouteWords)
  have lettersLimited : ∀ tested, letters.count tested ≤ 2 := by
    intro tested
    rw [show letters = nextStem ++ [final] by rfl,
      saturationCounts]
    by_cases member : tested ∈ targets
    · simp [member]
    · simp [member]
      simpa only [List.count_append] using stemLimited tested
  have targetsDouble : ∀ tested,
      tested ∈ targets → letters.count tested = 2 := by
    intro tested member
    rw [show letters = nextStem ++ [final] by rfl,
      saturationCounts, if_pos member]
  have lettersSupportStem : ∀ tested,
      tested ∈ letters ↔ tested ∈ stem ++ [final] := by
    intro tested
    change tested ∈ nextStem ++ [final] ↔
      tested ∈ stem ++ [final]
    rw [List.mem_append, List.mem_append,
      sameStemSupport tested]
  have targetsCoverStem : ∀ tested,
      tested ∈ stem → tested ∈ targets := by
    intro tested member
    rw [targetsEq]
    exact (mem_firstOccurrenceSequence_iff tested stem).mpr member
  have targetsDoubleRaw : ∀ tested,
      tested ∈ targets →
        (nextStem ++ [final]).count tested = 2 := by
    simpa [letters] using targetsDouble
  have singletonFinal : ∀ tested,
      letters.count tested = 1 →
        letters.getLast? = some tested := by
    simpa [letters] using
      singletonFinal_of_saturatedTargets
        targets stem nextStem final targetsCoverStem
          sameStemSupport targetsDoubleRaw
  have firstOrder :
      firstProjection (tagEndpoints letters) =
        (jointSignature anchor).factorNormal.dropLast := by
    calc
      firstProjection (tagEndpoints letters) =
          firstOccurrenceSequence nextStem := by
        simpa [letters] using
          firstProjection_saturated_append_final
            nextStem final lettersLimited singletonFinal
      _ = firstOccurrenceSequence stem := sameFirstOccurrences
      _ = targets := targetsEq.symm
      _ = (jointSignature anchor).factorNormal.dropLast := rfl
  have lastOrder :
      lastProjection (tagEndpoints letters) =
        (jointSignature anchor).lastOrder := by
    have projectedSignature :=
      congrArg (fun signature : JointSignature => signature.lastOrder)
        signatureLetters
    calc
      lastProjection (tagEndpoints letters) =
          lastOccurrenceSequence letters :=
        lastProjection_tagEndpoints letters
      _ = lastOccurrenceSequence lettersWord.toList := by
        simp [lettersWord]
      _ = (jointSignature lettersWord).lastOrder := rfl
      _ = (jointSignature anchor).lastOrder :=
        projectedSignature.symm
  have supportAnchor : ∀ tested,
      tested ∈ letters ↔ tested ∈ anchor.toList := by
    intro tested
    exact (lettersSupportStem tested).trans
      ((show tested ∈ stem ++ [final] ↔ tested ∈ trimmed by
          rw [trimmedShape]).trans (trimmedSupport tested))
  refine ⟨letters, completeRoute, ?_⟩
  exact
    { twoLimited := lettersLimited
      prefixSaturated := by
        intro tested member
        exact targetsDouble tested member
      singletonFinal := singletonFinal
      support := supportAnchor
      firstOrder := firstOrder
      lastOrder := lastOrder
      render := tagEndpoints_map_letter letters }

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
