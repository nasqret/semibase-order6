import SemigroupBasis.CoRoots.S5_343
import SemigroupBasis.CoRoots.S5_343Syntax
import SemigroupBasis.CoRoots.S5_345Normalization

namespace SemigroupBasis.CoRoots.S5_343Normalization

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

private theorem listDerivesContractInteriorSquare
    (pre suffix : List Nat) (letter : Nat)
    (prefixNonempty : pre ≠ [])
    (suffixNonempty : suffix ≠ []) :
    S5_107.ListDerives S5_343.basis
      (pre ++ [letter, letter] ++ suffix)
      (pre ++ [letter] ++ suffix) := by
  obtain ⟨prefixHead, prefixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil prefixNonempty
  obtain ⟨suffixHead, suffixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil suffixNonempty
  have core :=
    S5_107.ListDerives.ofWord <|
      (S5_343.derivesInteriorDuplication
        (S5_107.listWordOfCons prefixHead prefixTail)
        (Word.singleton letter)
        (S5_107.listWordOfCons suffixHead suffixTail)).symm
  simpa [S5_107.listWordOfCons, List.append_assoc] using core

private theorem listDerivesDeleteInteriorRepeat
    (pre middle suffix : List Nat) (letter : Nat)
    (prefixNonempty : pre ≠ [])
    (middleNonempty : middle ≠ [])
    (suffixNonempty : suffix ≠ []) :
    S5_107.ListDerives S5_343.basis
      (pre ++ [letter] ++ middle ++ [letter] ++ suffix)
      (pre ++ [letter] ++ middle ++ suffix) := by
  obtain ⟨prefixHead, prefixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil prefixNonempty
  obtain ⟨middleHead, middleTail, rfl⟩ :=
    List.exists_cons_of_ne_nil middleNonempty
  obtain ⟨suffixHead, suffixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil suffixNonempty
  have core :=
    S5_107.ListDerives.ofWord <|
      S5_343.derivesInteriorRepeatDeletion
        (S5_107.listWordOfCons prefixHead prefixTail)
        (Word.singleton letter)
        (S5_107.listWordOfCons middleHead middleTail)
        (S5_107.listWordOfCons suffixHead suffixTail)
  simpa [S5_107.listWordOfCons, List.append_assoc] using core

private theorem listDerivesRepeatedFinalSwitch
    (pre middle : List Nat) (letter : Nat)
    (prefixNonempty : pre ≠ [])
    (middleNonempty : middle ≠ []) :
    S5_107.ListDerives S5_343.basis
      (pre ++ [letter] ++ middle ++ [letter])
      (pre ++ [letter] ++ middle ++ middle) := by
  obtain ⟨prefixHead, prefixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil prefixNonempty
  obtain ⟨middleHead, middleTail, rfl⟩ :=
    List.exists_cons_of_ne_nil middleNonempty
  have core :=
    S5_107.ListDerives.ofWord <|
      S5_343.derivesRepeatedFinalSwitch
        (S5_107.listWordOfCons prefixHead prefixTail)
        (Word.singleton letter)
        (S5_107.listWordOfCons middleHead middleTail)
  simpa [S5_107.listWordOfCons, List.append_assoc] using core

/-- Collapse all saturated blocks between fixed nonempty contexts. -/
private theorem listDerivesCollapseBlocks
    (word : Word Nat) :
    ∀ (pre labels suffix : List Nat),
      pre ≠ [] →
      suffix ≠ [] →
      S5_107.ListDerives S5_343.basis
        (pre ++
          labels.flatMap (S5_345.canonicalBlock word) ++ suffix)
        (pre ++ labels ++ suffix)
  | _, [], _, _, _ =>
      S5_107.ListDerives.refl _
  | pre, label :: labels, suffix,
      prefixNonempty, suffixNonempty => by
      by_cases singleton :
          S5_107.cappedMultiplicity word label = 1 ∨
            S5_345.terminalMarker word = some label
      · have remaining :=
          listDerivesCollapseBlocks word
            (pre ++ [label]) labels suffix
            (by simp) suffixNonempty
        simpa [S5_345.canonicalBlock, singleton,
          List.append_assoc] using remaining
      · have trailingNonempty :
          labels.flatMap (S5_345.canonicalBlock word) ++ suffix ≠ [] := by
          simp [suffixNonempty]
        have first :=
          listDerivesContractInteriorSquare
            pre
            (labels.flatMap (S5_345.canonicalBlock word) ++ suffix)
            label prefixNonempty trailingNonempty
        have remaining :=
          listDerivesCollapseBlocks word
            (pre ++ [label]) labels suffix
            (by simp) suffixNonempty
        exact S5_107.ListDerives.trans
          (by
            simpa [S5_345.canonicalBlock, singleton,
              List.append_assoc] using first)
          (by
            simpa [S5_345.canonicalBlock, singleton,
              List.append_assoc] using remaining)

/-- Reduce `tail ++ tail` to `tail ++ [tail.last]` after a nonempty prefix. -/
private theorem listDerivesDuplicateTailToLast
    (pre : List Nat) (prefixNonempty : pre ≠ []) :
    ∀ (head : Nat) (tail : List Nat),
      S5_107.ListDerives S5_343.basis
        (pre ++ (head :: tail) ++ (head :: tail))
        (pre ++ (head :: tail) ++
          [(head :: tail).getLastD head])
  | head, [] => by
      simpa using
        S5_107.ListDerives.refl
          (basis := S5_343.basis) (pre ++ [head, head])
  | head, next :: rest => by
      have deleteHead :=
        listDerivesDeleteInteriorRepeat
          pre (next :: rest) (next :: rest) head
          prefixNonempty (by simp) (by simp)
      have remaining :=
        listDerivesDuplicateTailToLast
          (pre ++ [head]) (by simp) next rest
      exact S5_107.ListDerives.trans
        (by simpa [List.append_assoc] using deleteHead)
        (by
          simpa [List.getLastD_cons, List.append_assoc] using remaining)

private def removeLetter
    (selected : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ selected))

private theorem firstOccurrenceSequence_cons_eq
    (letter : Nat) (rest : List Nat) :
    firstOccurrenceSequence (letter :: rest) =
      letter :: removeLetter letter
        (firstOccurrenceSequence rest) :=
  rfl

private theorem removeLetter_self_cons
    (selected : Nat) (letters : List Nat) :
    removeLetter selected (selected :: letters) =
      removeLetter selected letters := by
  simp [removeLetter]

private theorem removeLetter_cons_of_ne
    (selected letter : Nat) (letters : List Nat)
    (different : letter ≠ selected) :
    removeLetter selected (letter :: letters) =
      letter :: removeLetter selected letters := by
  simp [removeLetter, different]

private theorem removeLetter_append
    (selected : Nat) (left right : List Nat) :
    removeLetter selected (left ++ right) =
      removeLetter selected left ++
        removeLetter selected right := by
  simp [removeLetter, List.filter_append]

private theorem removeLetter_idempotent
    (selected : Nat) (letters : List Nat) :
    removeLetter selected (removeLetter selected letters) =
      removeLetter selected letters := by
  unfold removeLetter
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  simp

private theorem firstOccurrenceSequence_append_final
    (final : Nat) :
    ∀ before : List Nat,
      firstOccurrenceSequence (before ++ [final]) =
        if final ∈ before then
          firstOccurrenceSequence before
        else
          firstOccurrenceSequence before ++ [final]
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_final final rest
      by_cases equal : letter = final
      · subst letter
        rw [List.cons_append,
          firstOccurrenceSequence_cons_eq,
          induction]
        simp only [List.mem_cons, true_or, if_true]
        by_cases present : final ∈ rest
        · rw [if_pos present]
          exact
            (firstOccurrenceSequence_cons_eq final rest).symm
        · rw [if_neg present, removeLetter_append]
          simpa [removeLetter] using
            (firstOccurrenceSequence_cons_eq final rest).symm
      · have reverse : final ≠ letter := Ne.symm equal
        rw [List.cons_append,
          firstOccurrenceSequence_cons_eq,
          induction]
        by_cases present : final ∈ rest
        · have fullPresent : final ∈ letter :: rest :=
            List.Mem.tail letter present
          rw [if_pos present, if_pos fullPresent]
          exact
            (firstOccurrenceSequence_cons_eq letter rest).symm
        · have fullAbsent : final ∉ letter :: rest := by
            simp [reverse, present]
          rw [if_neg present, if_neg fullAbsent,
            removeLetter_append]
          have keepFinal :
              removeLetter letter [final] = [final] := by
            simp [removeLetter, reverse]
          rw [keepFinal]
          rfl

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔
        selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem word_toList_eq_prefix_final
    (word : Word Nat) :
    ∃ pre, word.toList = pre ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruction :=
        (List.dropLast_concat_getLast
          (l := head :: tail) (by simp)).symm
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa only [Word.toList, Word.final, List.getLastD_cons] using
        reconstruction

private theorem firstOccurrenceSequence_eq_prefix_final
    (word : Word Nat)
    (finalSimple : word.toList.count word.final = 1) :
    ∃ pre,
      firstOccurrenceSequence word.toList =
        firstOccurrenceSequence pre ++ [word.final] := by
  obtain ⟨pre, sourceShape⟩ :=
    word_toList_eq_prefix_final word
  have finalAbsent : word.final ∉ pre := by
    rw [sourceShape, List.count_append] at finalSimple
    have countEquation : pre.count word.final + 1 = 1 := by
      simpa using finalSimple
    have prefixZero : pre.count word.final = 0 := by
      omega
    exact List.count_eq_zero.mp prefixZero
  refine ⟨pre, ?_⟩
  rw [sourceShape, firstOccurrenceSequence_append_final,
    if_neg finalAbsent]

private theorem firstOccurrenceSequence_word_shape
    (word : Word Nat) :
    ∃ rest,
      firstOccurrenceSequence word.toList =
        word.head :: rest := by
  cases word with
  | mk head tail =>
      exact
        ⟨(firstOccurrenceSequence tail).filter
            (fun letter => decide (letter ≠ head)), rfl⟩

private theorem head_mem_word (word : Word Nat) :
    word.head ∈ word.toList := by
  cases word
  simp [Word.toList]

private theorem final_mem_word (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem firstMultiple_split_of_exists
    (multiplicity : Nat → Nat) :
    ∀ (letters : List Nat),
      (∃ letter ∈ letters, multiplicity letter = 2) →
      ∃ marker before after,
        S5_345.firstMultiple multiplicity letters = some marker ∧
        letters = before ++ marker :: after ∧
        (∀ letter ∈ before, multiplicity letter ≠ 2) ∧
        multiplicity marker = 2
  | [], existsMultiple => by
      simp at existsMultiple
  | letter :: rest, existsMultiple => by
      by_cases multiple : multiplicity letter = 2
      · refine ⟨letter, [], rest, ?_, rfl, ?_, multiple⟩
        · simp [S5_345.firstMultiple, multiple]
        · intro selected member
          simp at member
      · have restExists :
          ∃ selected ∈ rest, multiplicity selected = 2 := by
          obtain ⟨selected, member, selectedMultiple⟩ :=
            existsMultiple
          rcases List.mem_cons.mp member with equal | restMember
          · subst selected
            exact False.elim (multiple selectedMultiple)
          · exact ⟨selected, restMember, selectedMultiple⟩
        obtain
          ⟨marker, before, after, firstShape, reconstruction,
            beforeNonmultiple, markerMultiple⟩ :=
          firstMultiple_split_of_exists multiplicity rest restExists
        refine
          ⟨marker, letter :: before, after, ?_, ?_, ?_,
            markerMultiple⟩
        · simp [S5_345.firstMultiple, multiple, firstShape]
        · exact congrArg (List.cons letter) reconstruction
        · intro selected member
          rcases List.mem_cons.mp member with equal | beforeMember
          · subst selected
            exact multiple
          · exact beforeNonmultiple selected beforeMember

private theorem getLastD_append_nonempty
    (left : List Nat) (head fallback : Nat) (tail : List Nat) :
    (left ++ head :: tail).getLastD fallback =
      tail.getLastD head := by
  induction left generalizing fallback with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction letter

/-- Transport the existing saturated normalizer to the exact three-law basis. -/
theorem derivesSaturatedCanonical (word : Word Nat) :
    Derives S5_343.basis word (S5_345.canonicalWord word) :=
  (S5_345.derivesCanonical word).transport
    S5_343.s5_345AxiomDerives

/-- Collapse the saturated `S5_345` normal form to the four endpoint forms. -/
theorem listDerivesSaturatedToEndpoint (word : Word Nat) :
    S5_107.ListDerives S5_343.basis
      (S5_345.canonicalList word)
      (S5_343Syntax.endpointCanonicalList word) := by
  by_cases finalSimple :
      word.toList.count word.final = 1
  · have markerNone : S5_345.terminalMarker word = none := by
      simp [S5_345.terminalMarker, S5_345.simpleFinalVariable,
        finalSimple]
    have finalCapped :
        S5_107.cappedMultiplicity word word.final = 1 :=
      (S5_107.cappedMultiplicity_eq_one_iff word word.final).2
        finalSimple
    have finalBlock :
        S5_345.canonicalBlock word word.final = [word.final] := by
      simp [S5_345.canonicalBlock, finalCapped]
    obtain ⟨pre, sequenceShape⟩ :=
      firstOccurrenceSequence_eq_prefix_final word finalSimple
    cases prefixSequenceShape :
        firstOccurrenceSequence pre with
    | nil =>
        have sequenceSingleton :
            firstOccurrenceSequence word.toList = [word.final] := by
          simpa [prefixSequenceShape] using sequenceShape
        obtain ⟨rest, headShape⟩ :=
          firstOccurrenceSequence_word_shape word
        have headFinal : word.head = word.final := by
          rw [sequenceSingleton] at headShape
          exact (List.cons.inj headShape.symm).1
        have initialSimple :
            word.toList.count word.head = 1 := by
          simpa [headFinal] using finalSimple
        simpa [S5_345.canonicalList,
          S5_343Syntax.endpointCanonicalList, sequenceSingleton,
          markerNone, finalBlock, initialSimple, finalSimple] using
            (S5_107.ListDerives.refl
              (basis := S5_343.basis) [word.final])
    | cons first middle =>
        have sequenceExpanded :
            firstOccurrenceSequence word.toList =
              first :: middle ++ [word.final] := by
          simpa [prefixSequenceShape] using sequenceShape
        obtain ⟨rest, headShape⟩ :=
          firstOccurrenceSequence_word_shape word
        have firstHead : first = word.head := by
          rw [sequenceExpanded] at headShape
          exact (List.cons.inj headShape).1
        have firstBlockNonempty :
            S5_345.canonicalBlock word first ≠ [] :=
          S5_345.canonicalBlock_ne_nil word first
        have collapsed :=
          listDerivesCollapseBlocks word
            (S5_345.canonicalBlock word first)
            middle [word.final]
            firstBlockNonempty (by simp)
        by_cases initialSimple :
            word.toList.count word.head = 1
        · have firstCapped :
              S5_107.cappedMultiplicity word first = 1 := by
            rw [firstHead]
            exact
              (S5_107.cappedMultiplicity_eq_one_iff
                word word.head).2 initialSimple
          have firstBlock :
              S5_345.canonicalBlock word first = [first] := by
            simp [S5_345.canonicalBlock, firstCapped]
          have collapsedEndpoint :
              S5_107.ListDerives S5_343.basis
                (S5_345.canonicalBlock word first ++
                  (middle.flatMap (S5_345.canonicalBlock word) ++
                    [word.final]))
                (first :: (middle ++ [word.final])) := by
            simpa [firstBlock, List.append_assoc] using collapsed
          simpa [S5_345.canonicalList,
            S5_343Syntax.endpointCanonicalList, sequenceExpanded,
            markerNone, finalBlock,
            initialSimple, finalSimple, List.append_assoc] using
              collapsedEndpoint
        · have firstCapped :
              S5_107.cappedMultiplicity word first ≠ 1 := by
            intro capped
            apply initialSimple
            rw [firstHead] at capped
            exact
              (S5_107.cappedMultiplicity_eq_one_iff
                word word.head).1 capped
          have firstBlock :
              S5_345.canonicalBlock word first = [first, first] := by
            simp [S5_345.canonicalBlock, firstCapped, markerNone]
          have collapsedEndpoint :
              S5_107.ListDerives S5_343.basis
                (S5_345.canonicalBlock word first ++
                  (middle.flatMap (S5_345.canonicalBlock word) ++
                    [word.final]))
                (first :: first :: (middle ++ [word.final])) := by
            simpa [firstBlock, List.append_assoc] using collapsed
          simpa [S5_345.canonicalList,
            S5_343Syntax.endpointCanonicalList, sequenceExpanded,
            markerNone, finalBlock, firstHead,
            initialSimple, finalSimple, List.append_assoc] using
              collapsedEndpoint
  · have finalPositive :
        0 < word.toList.count word.final :=
      List.count_pos_iff.mpr (final_mem_word word)
    have finalMultiple :
        S5_107.cappedMultiplicity word word.final = 2 :=
      (S5_345.cappedMultiplicity_eq_two_iff word word.final).2 <| by
        omega
    have finalSequenceMember :
        word.final ∈ firstOccurrenceSequence word.toList :=
      (mem_firstOccurrenceSequence_iff
        word.final word.toList).2 (final_mem_word word)
    obtain
      ⟨marker, before, after, firstShape, sequenceSplit,
        beforeNonmultiple, markerMultiple⟩ :=
      firstMultiple_split_of_exists
        (S5_107.cappedMultiplicity word)
        (firstOccurrenceSequence word.toList)
        ⟨word.final, finalSequenceMember, finalMultiple⟩
    have markerShape :
        S5_345.terminalMarker word = some marker := by
      simp [S5_345.terminalMarker, S5_345.simpleFinalVariable,
        finalSimple, S5_345.earliestMultiple, firstShape]
    obtain ⟨tail, sequenceHead⟩ :=
      firstOccurrenceSequence_word_shape word
    by_cases initialSimple :
        word.toList.count word.head = 1
    · have headCapped :
          S5_107.cappedMultiplicity word word.head = 1 :=
        (S5_107.cappedMultiplicity_eq_one_iff word word.head).2
          initialSimple
      have headBlock :
          S5_345.canonicalBlock word word.head = [word.head] := by
        simp [S5_345.canonicalBlock, headCapped]
      have collapsedTail :=
        listDerivesCollapseBlocks word [word.head] tail [marker]
          (by simp) (by simp)
      have collapsed :
          S5_107.ListDerives S5_343.basis
            (S5_345.canonicalList word)
            (firstOccurrenceSequence word.toList ++ [marker]) := by
        simpa [S5_345.canonicalList, sequenceHead,
          markerShape, headBlock, List.append_assoc] using collapsedTail
      have markerNeHead : marker ≠ word.head := by
        intro equal
        subst marker
        omega
      have beforeNonempty : before ≠ [] := by
        intro beforeEmpty
        rw [beforeEmpty] at sequenceSplit
        simp only [List.nil_append] at sequenceSplit
        rw [sequenceHead] at sequenceSplit
        have markerHead := (List.cons.inj sequenceSplit).1
        exact markerNeHead markerHead.symm
      cases after with
      | nil =>
          have lastMarker :
              (firstOccurrenceSequence word.toList).getLastD
                  word.head = marker := by
            rw [sequenceSplit]
            simpa using
              getLastD_append_nonempty before marker word.head []
          rw [← lastMarker] at collapsed
          simpa [S5_343Syntax.endpointCanonicalList,
            initialSimple, finalSimple] using collapsed
      | cons next rest =>
          have switch :=
            listDerivesRepeatedFinalSwitch
              before (next :: rest) marker
              beforeNonempty (by simp)
          have reduceDuplicate :=
            listDerivesDuplicateTailToLast
              (before ++ [marker]) (by simp) next rest
          rw [List.getLastD_cons] at reduceDuplicate
          have retarget :
              S5_107.ListDerives S5_343.basis
                (firstOccurrenceSequence word.toList ++ [marker])
                (firstOccurrenceSequence word.toList ++
                  [(firstOccurrenceSequence word.toList).getLastD
                    word.head]) := by
            have lastAfter :
                (firstOccurrenceSequence word.toList).getLastD
                    word.head =
                  rest.getLastD next := by
              rw [sequenceSplit]
              simpa [List.append_assoc] using
                getLastD_append_nonempty
                  (before ++ [marker]) next word.head rest
            rw [lastAfter, sequenceSplit]
            exact S5_107.ListDerives.trans
              (by
                simpa [List.append_assoc] using switch)
              (by
                simpa [List.append_assoc] using reduceDuplicate)
          exact collapsed.trans <| by
            simpa [S5_343Syntax.endpointCanonicalList,
              initialSimple, finalSimple] using retarget
    · have headPositive :
          0 < word.toList.count word.head :=
        List.count_pos_iff.mpr (head_mem_word word)
      have headMultiple :
          S5_107.cappedMultiplicity word word.head = 2 :=
        (S5_345.cappedMultiplicity_eq_two_iff word word.head).2 <| by
          omega
      have markerHead : marker = word.head := by
        have firstAtHead :
            S5_345.firstMultiple
                (S5_107.cappedMultiplicity word)
                (firstOccurrenceSequence word.toList) =
              some word.head := by
          rw [sequenceHead]
          simp [S5_345.firstMultiple, headMultiple]
        exact Option.some.inj (firstShape.symm.trans firstAtHead)
      have headBlock :
          S5_345.canonicalBlock word word.head = [word.head] := by
        simp [S5_345.canonicalBlock, markerShape, markerHead]
      have collapsedTail :=
        listDerivesCollapseBlocks word [word.head] tail [marker]
          (by simp) (by simp)
      have collapsed :
          S5_107.ListDerives S5_343.basis
            (S5_345.canonicalList word)
            (firstOccurrenceSequence word.toList ++ [marker]) := by
        simpa [S5_345.canonicalList, sequenceHead,
          markerShape, headBlock, List.append_assoc] using collapsedTail
      simpa [S5_343Syntax.endpointCanonicalList,
        initialSimple, finalSimple, markerHead] using collapsed

/-- Every word derives to its exact first-sequence endpoint normal form. -/
theorem derivesEndpointCanonical (word : Word Nat) :
    Derives S5_343.basis word
      (S5_343Syntax.endpointCanonicalWord word) := by
  have saturated := derivesSaturatedCanonical word
  have collapsed := listDerivesSaturatedToEndpoint word
  have saturatedList := S5_107.ListDerives.ofWord saturated
  have saturatedList' :
      S5_107.ListDerives S5_343.basis word.toList
        (S5_345.canonicalList word) := by
    simpa using saturatedList
  have collapsedWords := saturatedList'.trans collapsed
  cases word with
  | mk head tail =>
      cases canonical :
          S5_343Syntax.endpointCanonicalList (Word.mk head tail) with
      | nil =>
          exact False.elim <|
            S5_343Syntax.endpointCanonicalList_ne_nil
              (Word.mk head tail) canonical
      | cons canonicalHead canonicalTail =>
          have nonemptyCollapsed :
              S5_107.ListDerives S5_343.basis
                (head :: tail)
                (canonicalHead :: canonicalTail) := by
            simpa [S5_345.toList_canonicalWord, canonical] using
              collapsedWords
          have wordDerivation :=
            S5_107.ListDerives.toWord nonemptyCollapsed
          have targetEq :
              (⟨canonicalHead, canonicalTail⟩ : Word Nat) =
                S5_343Syntax.endpointCanonicalWord
                  (Word.mk head tail) := by
            apply Word.toList_injective
            rw [S5_343Syntax.toList_endpointCanonicalWord]
            exact canonical.symm
          rw [← targetEq]
          exact wordDerivation

end SemigroupBasis.CoRoots.S5_343Normalization
