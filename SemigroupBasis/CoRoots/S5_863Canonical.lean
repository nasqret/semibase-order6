import SemigroupBasis.CoRoots.S5_863Invariant
import SemigroupBasis.CoRoots.S5_863Normalization

namespace SemigroupBasis.CoRoots.S5_863

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

private def saturatedBlock
    (letters : List Nat) (letter : Nat) : List Nat :=
  if letters.count letter = 1 then [letter] else [letter, letter]

private def saturatedCanonicalList (letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).flatMap
    (saturatedBlock letters)

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

private theorem filter_ne_eq_self
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∉ letters →
      letters.filter (fun letter => decide (letter ≠ selected)) =
        letters
  | letters, absent => by
      apply List.filter_eq_self.mpr
      intro letter member
      simp only [decide_eq_true_eq]
      intro equal
      subst letter
      exact absent member

private theorem mem_saturatedBlock_iff
    (letters : List Nat) (selected label : Nat) :
    selected ∈ saturatedBlock letters label ↔ selected = label := by
  unfold saturatedBlock
  split <;> simp

private theorem mem_saturatedCanonicalList_iff
    (selected : Nat) (letters : List Nat) :
    selected ∈ saturatedCanonicalList letters ↔ selected ∈ letters := by
  unfold saturatedCanonicalList
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with
      ⟨label, labelMember, selectedMember⟩
    have equal :=
      (mem_saturatedBlock_iff letters selected label).1
        selectedMember
    subst label
    exact
      (mem_firstOccurrenceSequence_iff selected letters).1
        labelMember
  · intro member
    have labelMember :
        selected ∈ firstOccurrenceSequence letters :=
      (mem_firstOccurrenceSequence_iff selected letters).2 member
    apply List.mem_flatMap.mpr
    refine ⟨selected, labelMember, ?_⟩
    exact
      (mem_saturatedBlock_iff letters selected selected).2 rfl

private theorem filter_saturated_blocks
    (source target : List Nat) (selected : Nat)
    (sameCounts :
      ∀ letter, letter ≠ selected →
        source.count letter = target.count letter) :
    ∀ labels : List Nat,
      (labels.flatMap (saturatedBlock source)).filter
          (fun letter => decide (letter ≠ selected)) =
        (labels.filter
            (fun letter => decide (letter ≠ selected))).flatMap
          (saturatedBlock target)
  | [] => rfl
  | letter :: rest => by
      have recursive :=
        filter_saturated_blocks
          source target selected sameCounts rest
      rw [List.flatMap_cons, List.filter_append]
      by_cases equal : letter = selected
      · subst letter
        have blockFilter :
            (saturatedBlock source selected).filter
                (fun letter => decide (letter ≠ selected)) = [] := by
          unfold saturatedBlock
          split <;> simp
        rw [blockFilter, List.nil_append, recursive]
        simp
      · have countEq := sameCounts letter equal
        have blockEq :
            saturatedBlock source letter =
              saturatedBlock target letter := by
          unfold saturatedBlock
          rw [countEq]
        have blockFilter :
            (saturatedBlock target letter).filter
                (fun next => decide (next ≠ selected)) =
              saturatedBlock target letter := by
          unfold saturatedBlock
          split <;> simp [equal]
        rw [blockEq, blockFilter, recursive]
        simp [equal]

private theorem doubleCanonicalList_eq_saturatedCanonicalList :
    ∀ letters : List Nat,
      S5_345.doubleCanonicalList letters =
        saturatedCanonicalList letters
  | [] => rfl
  | letter :: rest => by
      have induction :=
        doubleCanonicalList_eq_saturatedCanonicalList rest
      have filtered :=
        filter_saturated_blocks rest (letter :: rest) letter
          (fun next different => by
            simp [List.count_cons_of_ne (Ne.symm different)])
          (firstOccurrenceSequence rest)
      by_cases repeated : letter ∈ rest
      · have repeatedReduced :
            letter ∈ S5_345.doubleCanonicalList rest := by
          rw [induction]
          exact
            (mem_saturatedCanonicalList_iff letter rest).2 repeated
        have positive : 0 < rest.count letter :=
          List.count_pos_iff.mpr repeated
        have restCountNeZero : rest.count letter ≠ 0 :=
          Nat.ne_of_gt positive
        have tailEq :
            (S5_345.doubleCanonicalList rest).filter
                (fun next => decide (next ≠ letter)) =
              ((firstOccurrenceSequence rest).filter
                  (fun next => decide (next ≠ letter))).flatMap
                (saturatedBlock (letter :: rest)) := by
          rw [induction]
          simpa [saturatedCanonicalList] using filtered
        unfold saturatedCanonicalList
        rw [firstOccurrenceSequence, List.flatMap_cons]
        have firstBlock :
            saturatedBlock (letter :: rest) letter =
              [letter, letter] := by
          simp [saturatedBlock, restCountNeZero]
        rw [firstBlock]
        simp only [S5_345.doubleCanonicalList, repeatedReduced, if_pos]
        exact congrArg (List.append [letter, letter]) tailEq
      · have repeatedReduced :
            letter ∉ S5_345.doubleCanonicalList rest := by
          intro member
          rw [induction] at member
          exact repeated <|
            (mem_saturatedCanonicalList_iff letter rest).1 member
        have repeatedSequence :
            letter ∉ firstOccurrenceSequence rest := by
          simpa [mem_firstOccurrenceSequence_iff] using repeated
        have countOne :
            (letter :: rest).count letter = 1 := by
          have countZero : rest.count letter = 0 :=
            List.count_eq_zero.mpr repeated
          simp [countZero]
        have sourceAbsent :
            letter ∉ saturatedCanonicalList rest := by
          simpa [mem_saturatedCanonicalList_iff] using repeated
        have sourceAbsent' :
            letter ∉
              (firstOccurrenceSequence rest).flatMap
                (saturatedBlock rest) := by
          simpa [saturatedCanonicalList] using sourceAbsent
        have tailEq :
            S5_345.doubleCanonicalList rest =
              (firstOccurrenceSequence rest).flatMap
                (saturatedBlock (letter :: rest)) := by
          rw [induction]
          have filtered' := filtered
          rw [filter_ne_eq_self letter sourceAbsent',
            filter_ne_eq_self letter repeatedSequence] at filtered'
          exact filtered'
        unfold saturatedCanonicalList
        rw [firstOccurrenceSequence, List.flatMap_cons]
        have firstBlock :
            saturatedBlock (letter :: rest) letter = [letter] := by
          simp [saturatedBlock, countOne]
        rw [firstBlock,
          filter_ne_eq_self letter repeatedSequence]
        simp only [S5_345.doubleCanonicalList, repeatedReduced, if_neg]
        exact congrArg (List.cons letter) tailEq

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

private theorem removeLetter_comm
    (first second : Nat) (letters : List Nat) :
    removeLetter second (removeLetter first letters) =
      removeLetter first (removeLetter second letters) := by
  unfold removeLetter
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem firstOccurrenceSequence_removeLetter
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence
          (removeLetter selected letters) =
        removeLetter selected
          (firstOccurrenceSequence letters)
  | [] => rfl
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_removeLetter selected rest
      by_cases equal : letter = selected
      · subst letter
        rw [removeLetter_self_cons, induction,
          firstOccurrenceSequence_cons_eq,
          removeLetter_self_cons,
          removeLetter_idempotent]
      · rw [removeLetter_cons_of_ne
          selected letter rest equal,
        firstOccurrenceSequence_cons_eq,
        induction,
        firstOccurrenceSequence_cons_eq,
        removeLetter_cons_of_ne
          selected letter
            (removeLetter letter
              (firstOccurrenceSequence rest)) equal]
        exact congrArg (List.cons letter) <|
          removeLetter_comm selected letter
            (firstOccurrenceSequence rest)

private theorem firstOccurrenceSequence_retainFirst
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence
          (S5_345.retainFirst selected letters) =
        firstOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_retainFirst selected rest
      by_cases equal : letter = selected
      · subst letter
        simp only [S5_345.retainFirst, if_pos rfl,
          firstOccurrenceSequence_cons_eq]
        change
          selected ::
              removeLetter selected
                (firstOccurrenceSequence
                  (removeLetter selected rest)) =
            selected ::
              removeLetter selected
                (firstOccurrenceSequence rest)
        rw [firstOccurrenceSequence_removeLetter,
          removeLetter_idempotent]
      · simp only [S5_345.retainFirst, if_neg equal,
          firstOccurrenceSequence_cons_eq]
        exact congrArg (List.cons letter) <|
          congrArg (removeLetter letter) induction

private theorem count_removeLetter_of_ne
    (selected tested : Nat) (different : tested ≠ selected)
    (letters : List Nat) :
    (removeLetter selected letters).count tested =
      letters.count tested := by
  unfold removeLetter
  exact List.count_filter (p :=
    fun letter => decide (letter ≠ selected))
      (by simp [different])

private theorem count_removeLetter_self
    (selected : Nat) (letters : List Nat) :
    (removeLetter selected letters).count selected = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have impossible : selected ≠ selected := by
    simpa using (List.mem_filter.mp member).2
  exact impossible rfl

private theorem count_retainFirst_of_ne
    (selected tested : Nat) (different : tested ≠ selected) :
    ∀ letters : List Nat,
      (S5_345.retainFirst selected letters).count tested =
        letters.count tested
  | [] => rfl
  | letter :: rest => by
      have induction :=
        count_retainFirst_of_ne
          selected tested different rest
      by_cases equal : letter = selected
      · subst letter
        simpa only [S5_345.retainFirst, if_pos,
          List.count_cons_of_ne (Ne.symm different)] using
          count_removeLetter_of_ne
            selected tested different rest
      · rw [S5_345.retainFirst, if_neg equal,
          List.count_cons, List.count_cons, induction]

private theorem count_retainFirst_self_of_mem
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      (S5_345.retainFirst selected letters).count selected = 1
  | [], member => by
      simp at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · subst letter
        rw [S5_345.retainFirst, if_pos rfl,
          List.count_cons_self]
        have tailZero :
            (List.filter
                (fun next => decide (next ≠ selected)) rest).count
                selected = 0 := by
          simpa only [removeLetter] using
            count_removeLetter_self selected rest
        omega
      · have restMember : selected ∈ rest := by
          simpa [equal, Ne.symm equal] using member
        rw [S5_345.retainFirst, if_neg equal,
          List.count_cons_of_ne equal]
        exact
          count_retainFirst_self_of_mem selected restMember

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
        · rw [if_neg present,
            removeLetter_append]
          simpa [removeLetter] using
            (firstOccurrenceSequence_cons_eq final rest).symm
      · have reverse : final ≠ letter :=
          Ne.symm equal
        rw [List.cons_append,
          firstOccurrenceSequence_cons_eq,
          induction]
        by_cases present : final ∈ rest
        · have fullPresent : final ∈ letter :: rest := by
            exact List.Mem.tail letter present
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
          change
            letter ::
                (removeLetter letter
                    (firstOccurrenceSequence rest) ++ [final]) =
              (letter ::
                removeLetter letter
                  (firstOccurrenceSequence rest)) ++ [final]
          rfl

private def subsystemBlock
    (letters : List Nat) (final letter : Nat) : List Nat :=
  if letter = final ∨ letters.count letter = 1 then
    [letter]
  else
    [letter, letter]

private def subsystemCanonicalList (word : Word Nat) : List Nat :=
  (firstOccurrenceSequence word.toList).flatMap
      (subsystemBlock word.toList word.final) ++
    if word.toList.count word.final = 1 then
      []
    else
      [word.final]

private theorem saturatedBlock_retainFirst_eq_subsystemBlock
    (before : List Nat) (final letter : Nat)
    (member : letter ∈ before) :
    saturatedBlock (S5_345.retainFirst final before) letter =
      subsystemBlock (before ++ [final]) final letter := by
  by_cases equal : letter = final
  · subst letter
    have retainedCount :=
      count_retainFirst_self_of_mem final member
    simp [saturatedBlock, subsystemBlock, retainedCount]
  · have retainedCount :=
      count_retainFirst_of_ne final letter equal before
    have fullCount :
        (before ++ [final]).count letter =
          before.count letter := by
      simp [List.count_append, equal, Ne.symm equal]
    unfold saturatedBlock subsystemBlock
    rw [retainedCount, fullCount]
    simp [equal]

private theorem flatMap_saturated_retainFirst_eq_subsystemBlock
    (before : List Nat) (final : Nat) :
    ∀ labels : List Nat,
      (∀ letter, letter ∈ labels → letter ∈ before) →
      labels.flatMap
          (saturatedBlock (S5_345.retainFirst final before)) =
        labels.flatMap
          (subsystemBlock (before ++ [final]) final)
  | [], _ => rfl
  | letter :: rest, supported => by
      have letterMember : letter ∈ before :=
        supported letter (by simp)
      have restSupported :
          ∀ next, next ∈ rest → next ∈ before := by
        intro next member
        exact supported next (by simp [member])
      rw [List.flatMap_cons, List.flatMap_cons,
        saturatedBlock_retainFirst_eq_subsystemBlock
          before final letter letterMember,
        flatMap_saturated_retainFirst_eq_subsystemBlock
          before final rest restSupported]

private theorem doubleCanonicalList_retainFirst_eq_subsystemBlocks
    (before : List Nat) (final : Nat) :
    S5_345.doubleCanonicalList
        (S5_345.retainFirst final before) =
      (firstOccurrenceSequence before).flatMap
        (subsystemBlock (before ++ [final]) final) := by
  rw [doubleCanonicalList_eq_saturatedCanonicalList]
  unfold saturatedCanonicalList
  rw [firstOccurrenceSequence_retainFirst]
  apply
    flatMap_saturated_retainFirst_eq_subsystemBlock
      before final
  intro letter member
  exact
    (mem_firstOccurrenceSequence_iff letter before).1 member

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

private theorem coreCanonicalList_eq_subsystemCanonicalList
    (word : Word Nat) :
    S5_345.coreCanonicalList word.toList =
      subsystemCanonicalList word := by
  cases word with
  | mk head tail =>
      unfold subsystemCanonicalList
      simp only [Word.toList, Word.final]
      let letters := head :: tail
      let final := tail.getLastD head
      let before := letters.dropLast
      change
        S5_345.doubleCanonicalList
              (S5_345.retainFirst final before) ++ [final] =
          (firstOccurrenceSequence letters).flatMap
              (subsystemBlock letters final) ++
            (if letters.count final = 1 then
              []
            else
              [final])
      have reconstruction :
          before ++ [final] = letters := by
        simpa [before, final, letters] using
          dropLast_append_final head tail
      have blockShape :=
        doubleCanonicalList_retainFirst_eq_subsystemBlocks
          before final
      have sequenceShape :=
        firstOccurrenceSequence_append_final final before
      rw [← reconstruction]
      by_cases finalBefore : final ∈ before
      · have finalCountPositive :
            0 < before.count final :=
          List.count_pos_iff.mpr finalBefore
        have finalNotSimple :
            (before ++ [final]).count final ≠ 1 := by
          simp only [List.count_append,
            List.count_cons_self, List.count_nil, Nat.add_zero]
          omega
        rw [if_pos finalBefore] at sequenceShape
        rw [blockShape, sequenceShape,
          if_neg finalNotSimple]
      · have finalSimple :
            (before ++ [final]).count final = 1 := by
          have countZero : before.count final = 0 :=
            List.count_eq_zero.mpr finalBefore
          simp [List.count_append, countZero]
        rw [if_neg finalBefore] at sequenceShape
        rw [blockShape, sequenceShape,
          if_pos finalSimple, List.append_nil,
          List.flatMap_append, List.flatMap_singleton]
        simp [subsystemBlock]

private theorem subsystemBlock_eq
    {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right)
    (letter : Nat) :
    subsystemBlock left.toList left.final letter =
      subsystemBlock right.toList right.final letter := by
  by_cases leftFinal : letter = left.final
  · have rightFinal : letter = right.final :=
      leftFinal.trans same.finalLetter
    simp only [subsystemBlock, if_pos (Or.inl leftFinal),
      if_pos (Or.inl rightFinal)]
  · have rightFinal : letter ≠ right.final := by
      intro equal
      exact leftFinal (equal.trans same.finalLetter.symm)
    have simpleEq :
        left.toList.count letter = 1 ↔
          right.toList.count letter = 1 := by
      simpa [SimpleIn] using same.simple letter
    by_cases leftSimple : left.toList.count letter = 1
    · have rightSimple := simpleEq.mp leftSimple
      simp only [subsystemBlock, if_pos (Or.inr leftSimple),
        if_pos (Or.inr rightSimple)]
    · have rightSimple : right.toList.count letter ≠ 1 := by
        intro simple
        exact leftSimple (simpleEq.mpr simple)
      have leftCondition :
          ¬(letter = left.final ∨ left.toList.count letter = 1) := by
        rintro (final | simple)
        · exact leftFinal final
        · exact leftSimple simple
      have rightCondition :
          ¬(letter = right.final ∨ right.toList.count letter = 1) := by
        rintro (final | simple)
        · exact rightFinal final
        · exact rightSimple simple
      simp only [subsystemBlock, if_neg leftCondition,
        if_neg rightCondition]

private theorem subsystemCanonicalList_eq
    {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    subsystemCanonicalList left =
      subsystemCanonicalList right := by
  have blockEq :
      subsystemBlock left.toList left.final =
        subsystemBlock right.toList right.final := by
    funext letter
    exact subsystemBlock_eq same letter
  have finalSimpleEq :
      left.toList.count left.final = 1 ↔
        right.toList.count right.final = 1 := by
    rw [same.finalLetter]
    simpa [SimpleIn] using same.simple right.final
  unfold subsystemCanonicalList
  by_cases leftSimple : left.toList.count left.final = 1
  · have rightSimple := finalSimpleEq.mp leftSimple
    rw [same.firstOccurrences, blockEq,
      if_pos leftSimple, if_pos rightSimple]
  · have rightSimple : right.toList.count right.final ≠ 1 := by
      intro simple
      exact leftSimple (finalSimpleEq.mpr simple)
    rw [same.firstOccurrences, blockEq,
      if_neg leftSimple, if_neg rightSimple, same.finalLetter]

private theorem coreCanonicalList_ne_nil (word : Word Nat) :
    S5_345.coreCanonicalList word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      change
        S5_345.doubleCanonicalList
            (S5_345.retainFirst (tail.getLastD head)
              (head :: tail).dropLast) ++
          [tail.getLastD head] ≠ []
      simp

namespace SameInitialSimpleFinalSignature

/-- The core canonical list is determined solely by first-occurrence order,
capped multiplicities, and the literal final letter. -/
theorem coreCanonicalList_eq {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    S5_345.coreCanonicalList left.toList =
      S5_345.coreCanonicalList right.toList := by
  calc
    S5_345.coreCanonicalList left.toList =
        subsystemCanonicalList left :=
      coreCanonicalList_eq_subsystemCanonicalList left
    _ = subsystemCanonicalList right :=
      subsystemCanonicalList_eq same
    _ = S5_345.coreCanonicalList right.toList :=
      (coreCanonicalList_eq_subsystemCanonicalList right).symm

/-- Equal exact signatures produce literally equal `S5_863` core canonical
words. -/
theorem coreCanonicalWord_eq {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    coreCanonicalWord left = coreCanonicalWord right := by
  have listEq := same.coreCanonicalList_eq
  unfold coreCanonicalWord
  rw [listEq]
  generalize listShape :
    S5_345.coreCanonicalList right.toList = rendered
  cases rendered with
  | nil =>
      exact False.elim <|
        coreCanonicalList_ne_nil right listShape
  | cons head tail =>
      rfl

end SameInitialSimpleFinalSignature

end SemigroupBasis.CoRoots.S5_863
