import SemigroupBasis.CoRoots.S5_345
import SemigroupBasis.CoRoots.S5_345Syntax

namespace SemigroupBasis.CoRoots.S5_345

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

private theorem listDerivesLeftEndpointContraction
    (pre suffix : List Nat) (x middleHead : Nat)
    (middleTail : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x] ++ (middleHead :: middleTail) ++ [x] ++ suffix)
      (pre ++ [x] ++ (middleHead :: middleTail) ++ [x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      (derivesLeftEndpointExpansion
        (Word.singleton x)
        (S5_107.listWordOfCons middleHead middleTail)).symm
  simpa [S5_107.listWordOfCons, List.append_assoc] using
    core.context pre suffix

private theorem listDerivesRightEndpointExpansion
    (pre suffix : List Nat) (x middleHead : Nat)
    (middleTail : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x] ++ (middleHead :: middleTail) ++ [x] ++ suffix)
      (pre ++ [x] ++ (middleHead :: middleTail) ++ [x, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesRightEndpointExpansion
        (Word.singleton x)
        (S5_107.listWordOfCons middleHead middleTail)
  simpa [S5_107.listWordOfCons, List.append_assoc] using
    core.context pre suffix

private theorem listDerivesSquareFinalSwitch
    (pre suffix : List Nat) (x final : Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x, final, final] ++ suffix)
      (pre ++ [x, final, final, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesSquareFinalSwitch
        (Word.singleton x) (Word.singleton final)
  simpa [List.append_assoc] using core.context pre suffix

private theorem listDerivesOpenTerminalSwitch
    (pre suffix : List Nat) (x final rightHead : Nat)
    (rightTail : List Nat) :
    S5_107.ListDerives basis
      (pre ++
        [x, x, final] ++ (rightHead :: rightTail) ++ [final] ++ suffix)
      (pre ++
        [x, final, final] ++ (rightHead :: rightTail) ++ [x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesOpenTerminalSwitch
        (Word.singleton x)
        (Word.singleton final)
        (S5_107.listWordOfCons rightHead rightTail)
  simpa [S5_107.listWordOfCons, List.append_assoc] using
    core.context pre suffix

private theorem listDerivesClosedTerminalSwitch
    (pre suffix : List Nat) (x leftHead : Nat)
    (leftTail : List Nat) (final : Nat) :
    S5_107.ListDerives basis
      (pre ++
        [x, x] ++ (leftHead :: leftTail) ++ [final, final] ++ suffix)
      (pre ++
        [x] ++ (leftHead :: leftTail) ++ [final, final, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesClosedTerminalSwitch
        (Word.singleton x)
        (S5_107.listWordOfCons leftHead leftTail)
        (Word.singleton final)
  simpa [S5_107.listWordOfCons, List.append_assoc] using
    core.context pre suffix

/-- Contextual three-to-two contraction for a singleton letter. -/
theorem listDerivesPowerContract
    (pre suffix : List Nat) (x : Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x, x] ++ suffix)
      (pre ++ [x, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesPowerContraction (Word.singleton x)
  simpa [List.append_assoc] using core.context pre suffix

/-- Gather two occurrences of `x` at the front of a segment whenever a
nonempty suffix follows the second occurrence. Empty middle context is the
reflexive case. -/
theorem listDerivesGatherNonfinal
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    S5_107.ListDerives basis
      (pre ++ [x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := basis) (pre ++ [x, x] ++ after ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨afterHead, afterTail, rfl⟩ :=
        List.exists_cons_of_ne_nil afterNonempty
      have core :=
        S5_107.ListDerives.ofWord <|
          (derivesDoubledInitialMove
            (Word.singleton x)
            (S5_107.listWordOfCons middleHead middleTail)
            (S5_107.listWordOfCons afterHead afterTail)).symm
      simpa [S5_107.listWordOfCons, List.append_assoc] using
        core.context pre suffix

/-- Delete a later copy of `x` once a leading square has been gathered. -/
theorem listDerivesAbsorbAfterSquare
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    S5_107.ListDerives basis
      (pre ++ [x, x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesPowerContract pre (after ++ suffix) x
  | cons middleHead middleTail =>
      have first :=
        listDerivesLeftEndpointContraction
          pre (after ++ suffix) x middleHead middleTail
      have second :=
        listDerivesGatherNonfinal
          pre suffix x (middleHead :: middleTail) after afterNonempty
      have firstStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix)
            (pre ++ [x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix) := by
        simpa [List.append_assoc] using first
      have secondStep :
          S5_107.ListDerives basis
            (pre ++ [x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix)
            (pre ++ [x, x] ++
              (middleHead :: middleTail) ++ after ++ suffix) := by
        simpa [List.append_assoc] using second
      exact firstStep.trans secondStep

/-- Delete one interior occurrence between equal endpoint copies. -/
theorem listDerivesDeleteInteriorFinal
    (pre suffix : List Nat) (x : Nat)
    (left right : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x] ++ left ++ [x] ++ right ++ [x] ++ suffix)
      (pre ++ [x] ++ left ++ right ++ [x] ++ suffix) := by
  have gathered :=
    listDerivesGatherNonfinal
      pre suffix x left (right ++ [x]) (by simp)
  have gatheredStep :
      S5_107.ListDerives basis
        (pre ++ [x] ++ left ++ [x] ++ right ++ [x] ++ suffix)
        (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix) := by
    simpa [List.append_assoc] using gathered
  cases middleShape : left ++ right with
  | nil =>
      have finish := listDerivesPowerContract pre suffix x
      have finishStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix)
            (pre ++ [x] ++ (left ++ right) ++ [x] ++ suffix) := by
        rw [middleShape]
        simpa [List.append_assoc] using finish
      exact gatheredStep.trans <| by
        simpa [List.append_assoc] using finishStep
  | cons middleHead middleTail =>
      have finish :=
        listDerivesLeftEndpointContraction
          pre suffix x middleHead middleTail
      have finishStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix)
            (pre ++ [x] ++ (left ++ right) ++ [x] ++ suffix) := by
        rw [middleShape]
        simpa [List.append_assoc] using finish
      exact gatheredStep.trans <| by
        simpa [List.append_assoc] using finishStep

/-- The unrestricted terminal-marker switch
`x² U f V f = x U f² V x`, including all three empty-context boundary
cases. -/
theorem listDerivesTerminalMarkerSwitch
    (pre suffix : List Nat) (x final : Nat)
    (left right : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x] ++ left ++ [final] ++ right ++ [final] ++ suffix)
      (pre ++ [x] ++ left ++ [final, final] ++ right ++ [x] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            listDerivesSquareFinalSwitch pre suffix x final
      | cons rightHead rightTail =>
          simpa [List.append_assoc] using
            listDerivesOpenTerminalSwitch
              pre suffix x final rightHead rightTail
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            listDerivesClosedTerminalSwitch
              pre suffix x leftHead leftTail final
      | cons rightHead rightTail =>
          let left := leftHead :: leftTail
          let right := rightHead :: rightTail
          have step₁ :=
            (listDerivesGatherNonfinal
              pre suffix x left
              ([final] ++ right ++ [final]) (by simp)).symm
          have step₂ :=
            listDerivesRightEndpointExpansion
              pre ([final] ++ right ++ [final] ++ suffix)
              x leftHead leftTail
          have step₃ :=
            listDerivesOpenTerminalSwitch
              (pre ++ [x] ++ left) suffix
              x final rightHead rightTail
          have step₄ :=
            listDerivesDeleteInteriorFinal
              pre suffix x left ([final, final] ++ right)
          have normalizedStep₁ :
              S5_107.ListDerives basis
                (pre ++ [x, x] ++ left ++ [final] ++ right ++
                  [final] ++ suffix)
                (pre ++ [x] ++ left ++ [x] ++ [final] ++ right ++
                  [final] ++ suffix) := by
            simpa [left, right, List.append_assoc] using step₁
          have normalizedStep₂ :
              S5_107.ListDerives basis
                (pre ++ [x] ++ left ++ [x] ++ [final] ++ right ++
                  [final] ++ suffix)
                (pre ++ [x] ++ left ++ [x, x] ++ [final] ++ right ++
                  [final] ++ suffix) := by
            simpa [left, right, List.append_assoc] using step₂
          have normalizedStep₃ :
              S5_107.ListDerives basis
                (pre ++ [x] ++ left ++ [x, x] ++ [final] ++ right ++
                  [final] ++ suffix)
                (pre ++ [x] ++ left ++ [x] ++ [final, final] ++
                  right ++ [x] ++ suffix) := by
            simpa [left, right, List.append_assoc] using step₃
          have normalizedStep₄ :
              S5_107.ListDerives basis
                (pre ++ [x] ++ left ++ [x] ++ [final, final] ++
                  right ++ [x] ++ suffix)
                (pre ++ [x] ++ left ++ [final, final] ++
                  right ++ [x] ++ suffix) := by
            simpa [left, right, List.append_assoc] using step₄
          exact normalizedStep₁.trans <|
            normalizedStep₂.trans <|
              normalizedStep₃.trans normalizedStep₄

/-- Remove every selected occurrence after a leading square. The final
nonempty suffix is retained verbatim. -/
theorem listDerivesAbsorbAllAfterSquare
    (x : Nat) :
    ∀ (pre rest suffix : List Nat), suffix ≠ [] →
      S5_107.ListDerives basis
        ([x, x] ++ pre ++ rest ++ suffix)
        ([x, x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ suffix)
  | pre, [], suffix, _ =>
      S5_107.ListDerives.refl _
  | pre, letter :: rest, suffix, suffixNonempty => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesAbsorbAfterSquare
            [] [] x pre (rest ++ suffix)
            (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare x pre rest suffix suffixNonempty
        have firstStep :
            S5_107.ListDerives basis
              ([x, x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have remaining :=
          listDerivesAbsorbAllAfterSquare
            x (pre ++ [letter]) rest suffix suffixNonempty
        simpa [equal, List.append_assoc] using remaining

/-- Gather the first selected occurrence into a leading square and remove all
remaining selected occurrences before a fixed nonempty suffix. -/
theorem listDerivesGatherAndDelete
    (x : Nat) :
    ∀ (pre rest suffix : List Nat), suffix ≠ [] → x ∈ rest →
      S5_107.ListDerives basis
        ([x] ++ pre ++ rest ++ suffix)
        ([x, x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ suffix)
  | _, [], _, _, member => by
      simp at member
  | pre, letter :: rest, suffix, suffixNonempty, member => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesGatherNonfinal
            [] [] x pre (rest ++ suffix)
            (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare
            x pre rest suffix suffixNonempty
        have firstStep :
            S5_107.ListDerives basis
              ([x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have restMember : x ∈ rest := by
          simpa [equal, Ne.symm equal] using member
        have remaining :=
          listDerivesGatherAndDelete
            x (pre ++ [letter]) rest suffix
            suffixNonempty restMember
        simpa [equal, List.append_assoc] using remaining

/-- Delete every selected interior occurrence between equal endpoint copies. -/
theorem listDerivesDeleteInteriorCopies
    (x : Nat) :
    ∀ (pre rest : List Nat),
      S5_107.ListDerives basis
        ([x] ++ pre ++ rest ++ [x])
        ([x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ [x])
  | pre, [] =>
      S5_107.ListDerives.refl _
  | pre, letter :: rest => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesDeleteInteriorFinal [] [] x pre rest
        have remaining :=
          listDerivesDeleteInteriorCopies x pre rest
        have firstStep :
            S5_107.ListDerives basis
              ([x] ++ pre ++ [x] ++ rest ++ [x])
              ([x] ++ pre ++ rest ++ [x]) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have remaining :=
          listDerivesDeleteInteriorCopies
            x (pre ++ [letter]) rest
        simpa [equal, List.append_assoc] using remaining

/-- Retain only the first occurrence of `selected`, preserving every other
letter and its position. -/
def retainFirst (selected : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then
        letter ::
          rest.filter (fun next => decide (next ≠ selected))
      else
        letter :: retainFirst selected rest

/-- Retaining only the first prefix occurrence of the final letter is a
derivable operation. -/
theorem listDerivesRetainFirstBeforeFinal
    (final : Nat) :
    ∀ letters : List Nat,
      S5_107.ListDerives basis
        (letters ++ [final])
        (retainFirst final letters ++ [final])
  | [] =>
      S5_107.ListDerives.refl _
  | letter :: rest => by
      by_cases equal : letter = final
      · subst letter
        simpa [retainFirst, List.append_assoc] using
          listDerivesDeleteInteriorCopies final [] rest
      · have remaining :=
          listDerivesRetainFirstBeforeFinal final rest
        simpa [retainFirst, equal, List.append_assoc] using
          remaining.prepend [letter]

/-- First-occurrence block normalization. Every letter is rendered once if
simple and twice if multiple; later blocks are kept in their original
first-occurrence order. -/
def doubleCanonicalList : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := doubleCanonicalList rest
      if letter ∈ reduced then
        [letter, letter] ++
          reduced.filter (fun next => decide (next ≠ letter))
      else
        letter :: reduced

/-- Render one first-occurrence block with multiplicity capped at two. -/
def saturatedBlock
    (letters : List Nat) (letter : Nat) : List Nat :=
  if letters.count letter = 1 then [letter] else [letter, letter]

/-- Render the cap-two blocks in first-occurrence order. -/
def saturatedCanonicalList (letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).flatMap
    (saturatedBlock letters)

/-- A variable occurs in the first-occurrence sequence exactly when it occurs
in the source list. -/
theorem mem_firstOccurrenceSequence_iff
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

/-- Saturated first-occurrence rendering preserves support. -/
theorem mem_saturatedCanonicalList_iff
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

/-- The recursive cap-two normalizer equals its explicit block rendering. -/
theorem doubleCanonicalList_eq_saturatedCanonicalList :
    ∀ letters : List Nat,
      doubleCanonicalList letters = saturatedCanonicalList letters
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
            letter ∈ doubleCanonicalList rest := by
          rw [induction]
          exact
            (mem_saturatedCanonicalList_iff letter rest).2 repeated
        have positive : 0 < rest.count letter :=
          List.count_pos_iff.mpr repeated
        have restCountNeZero : rest.count letter ≠ 0 :=
          Nat.ne_of_gt positive
        have tailEq :
            (doubleCanonicalList rest).filter
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
        simp only [doubleCanonicalList, repeatedReduced, if_pos]
        exact congrArg (List.append [letter, letter]) tailEq
      · have repeatedReduced :
            letter ∉ doubleCanonicalList rest := by
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
            doubleCanonicalList rest =
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
        simp only [doubleCanonicalList, repeatedReduced, if_neg]
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
      firstOccurrenceSequence (retainFirst selected letters) =
        firstOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_retainFirst selected rest
      by_cases equal : letter = selected
      · subst letter
        simp only [retainFirst, if_pos rfl,
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
      · simp only [retainFirst, if_neg equal,
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
      (retainFirst selected letters).count tested =
        letters.count tested
  | [] => rfl
  | letter :: rest => by
      have induction :=
        count_retainFirst_of_ne
          selected tested different rest
      by_cases equal : letter = selected
      · subst letter
        simpa only [retainFirst, if_pos,
          List.count_cons_of_ne (Ne.symm different)] using
          count_removeLetter_of_ne
            selected tested different rest
      · rw [retainFirst, if_neg equal,
          List.count_cons, List.count_cons, induction]

private theorem count_retainFirst_self_of_mem
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      (retainFirst selected letters).count selected = 1
  | [], member => by
      simp at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · subst letter
        rw [retainFirst, if_pos rfl,
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
        rw [retainFirst, if_neg equal,
          List.count_cons_of_ne equal]
        exact
          count_retainFirst_self_of_mem selected restMember

/-- Appending a final letter either preserves the first-occurrence sequence or
adds that letter once at the end. -/
theorem firstOccurrenceSequence_append_final
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
    saturatedBlock (retainFirst final before) letter =
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
          (saturatedBlock (retainFirst final before)) =
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
    doubleCanonicalList (retainFirst final before) =
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

/-- Normalize a prefix to first-occurrence single/double blocks while keeping
a fixed final letter available as the nonempty right context. -/
theorem listDerivesDoubleCanonicalBeforeFinal
    (final : Nat) :
    ∀ letters : List Nat,
      S5_107.ListDerives basis
        (letters ++ [final])
        (doubleCanonicalList letters ++ [final])
  | [] =>
      S5_107.ListDerives.refl _
  | letter :: rest => by
      let reduced := doubleCanonicalList rest
      have first :=
        (listDerivesDoubleCanonicalBeforeFinal final rest).prepend [letter]
      by_cases member : letter ∈ reduced
      · have gathered :=
          listDerivesGatherAndDelete
            letter [] reduced [final] (by simp) member
        exact first.trans <| by
          simpa [doubleCanonicalList, reduced, member,
            List.append_assoc] using gathered
      · simpa [doubleCanonicalList, reduced, member,
          List.append_assoc] using first

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

/-- The `S5_863` subsystem normal form. Multiple nonfinal variables become
leading double blocks. A multiple final variable is retained once at its
first occurrence and once at the end. -/
def coreCanonicalList : List Nat → List Nat
  | [] => []
  | head :: tail =>
      let letters := head :: tail
      let final := tail.getLastD head
      doubleCanonicalList
          (retainFirst final letters.dropLast) ++
        [final]

private theorem coreCanonicalList_eq_subsystemCanonicalList
    (word : Word Nat) :
    coreCanonicalList word.toList =
      subsystemCanonicalList word := by
  cases word with
  | mk head tail =>
      unfold subsystemCanonicalList
      simp only [Word.toList, Word.final]
      let letters := head :: tail
      let final := tail.getLastD head
      let before := letters.dropLast
      change
        doubleCanonicalList
              (retainFirst final before) ++ [final] =
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

/-- Every list derives directly to the subsystem normal form. -/
theorem listDerivesCoreCanonical :
    ∀ letters : List Nat,
      S5_107.ListDerives basis letters (coreCanonicalList letters)
  | [] =>
      S5_107.ListDerives.empty
  | head :: tail => by
      let letters := head :: tail
      let final := tail.getLastD head
      let beforeFinal := letters.dropLast
      have retained :=
        listDerivesRetainFirstBeforeFinal final beforeFinal
      have doubled :=
        listDerivesDoubleCanonicalBeforeFinal
          final (retainFirst final beforeFinal)
      have normalized := retained.trans doubled
      have reconstruction :
          beforeFinal ++ [final] = letters := by
        simpa [beforeFinal, final, letters] using
          dropLast_append_final head tail
      rw [reconstruction] at normalized
      simpa [coreCanonicalList, letters, final, beforeFinal] using normalized

/-- A certified split at one occurrence of `selected`. -/
structure FirstSplit where
  before : List Nat
  after : List Nat

/-- Split at the first occurrence of a selected letter. -/
def splitFirst (selected : Nat) :
    List Nat → Option FirstSplit
  | [] => none
  | letter :: rest =>
      if equal : letter = selected then
        some
          { before := []
            after := rest }
      else
        match splitFirst selected rest with
        | none => none
        | some split =>
            some
              { before := letter :: split.before
                after := split.after }

/-- Reconstruct a list from a successful first-occurrence split. -/
theorem splitFirst_reconstruction
    (selected : Nat) :
    ∀ (letters : List Nat) (split : FirstSplit),
      splitFirst selected letters = some split →
      letters = split.before ++ selected :: split.after
  | [], _, result => by
      simp [splitFirst] at result
  | letter :: rest, split, result => by
      by_cases equal : letter = selected
      · subst letter
        have splitShape :
            ({ before := []
               after := rest } : FirstSplit) = split := by
          simpa [splitFirst] using result
        subst split
        rfl
      · cases restShape : splitFirst selected rest with
        | none =>
            simp [splitFirst, equal, restShape] at result
        | some restSplit =>
            have reconstruction :=
              splitFirst_reconstruction
                selected rest restSplit restShape
            have splitShape :
                ({ before := letter :: restSplit.before
                   after := restSplit.after } : FirstSplit) =
                  split := by
              simpa [splitFirst, equal, restShape] using result
            subst split
            exact congrArg (List.cons letter) reconstruction

/-- Every member admits a successful first-occurrence split. -/
theorem splitFirst_some_of_mem
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      ∃ split, splitFirst selected letters = some split
  | [], member => by
      simp at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · subst letter
        refine
          ⟨{ before := []
             after := rest }, ?_⟩
        simp [splitFirst]
      · have restMember : selected ∈ rest := by
          simpa [equal, Ne.symm equal] using member
        obtain ⟨split, splitShape⟩ :=
          splitFirst_some_of_mem selected restMember
        refine
          ⟨{ before := letter :: split.before
             after := split.after }, ?_⟩
        simp [splitFirst, equal, splitShape]

/-- A successful first-multiple search exposes the preceding nonmultiple
labels and the selected multiplicity-two marker. -/
theorem firstMultiple_split_of_exists
    (multiplicity : Nat → Nat) :
    ∀ (letters : List Nat),
      (∃ letter ∈ letters, multiplicity letter = 2) →
      ∃ marker before after,
        firstMultiple multiplicity letters = some marker ∧
        letters = before ++ marker :: after ∧
        (∀ letter ∈ before, multiplicity letter ≠ 2) ∧
        multiplicity marker = 2
  | [], existsMultiple => by
      simp at existsMultiple
  | letter :: rest, existsMultiple => by
      by_cases multiple : multiplicity letter = 2
      · refine ⟨letter, [], rest, ?_, rfl, ?_, multiple⟩
        · simp [firstMultiple, multiple]
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
        · simp [firstMultiple, multiple, firstShape]
        · exact congrArg (List.cons letter) reconstruction
        · intro selected member
          rcases List.mem_cons.mp member with equal | beforeMember
          · subst selected
            exact multiple
          · exact beforeNonmultiple selected beforeMember

private theorem not_mem_parts_of_nodup_split
    {letters before after : List Nat} {letter : Nat}
    (nodup : letters.Nodup)
    (split : letters = before ++ letter :: after) :
    letter ∉ before ∧ letter ∉ after := by
  have splitNodup :
      (before ++ letter :: after).Nodup := by
    rw [← split]
    exact nodup
  have appendData := List.nodup_append.mp splitNodup
  constructor
  · intro member
    exact appendData.2.2
      letter member letter (by simp) rfl
  · exact (List.nodup_cons.mp appendData.2.1).1

private theorem flatMap_congr_of_mem
    (left right : Nat → List Nat) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, left letter = right letter) →
      letters.flatMap left = letters.flatMap right
  | [], _ => rfl
  | letter :: rest, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => right letter ++ suffix) <|
        flatMap_congr_of_mem left right rest <| by
          intro selected member
          exact same selected (by simp [member])

private theorem subsystemBlock_eq_canonicalBlock_of_ne
    (word : Word Nat) (marker letter : Nat)
    (markerShape : terminalMarker word = some marker)
    (notFinal : letter ≠ word.final)
    (notMarker : letter ≠ marker) :
    subsystemBlock word.toList word.final letter =
      canonicalBlock word letter := by
  simp [subsystemBlock, canonicalBlock, notFinal, markerShape,
    notMarker, Ne.symm notMarker, cappedMultiplicity_eq_one_iff]

private theorem listDerivesSubsystemCanonical
    (word : Word Nat) :
    S5_107.ListDerives basis
      (subsystemCanonicalList word) (canonicalList word) := by
  by_cases finalSimple :
      word.toList.count word.final = 1
  · have markerNone : terminalMarker word = none := by
      simp [terminalMarker, simpleFinalVariable, finalSimple]
    have blockEq :
        subsystemBlock word.toList word.final =
          canonicalBlock word := by
      funext letter
      by_cases equal : letter = word.final
      · subst letter
        simp [subsystemBlock, canonicalBlock, finalSimple,
          markerNone, cappedMultiplicity_eq_one_iff]
      · simp [subsystemBlock, canonicalBlock, equal,
          markerNone, cappedMultiplicity_eq_one_iff]
    have formsEqual :
        subsystemCanonicalList word = canonicalList word := by
      simp [subsystemCanonicalList, canonicalList,
        finalSimple, markerNone, blockEq]
    rw [formsEqual]
    exact S5_107.ListDerives.refl _
  · have finalMember : word.final ∈ word.toList := by
      cases word with
      | mk head tail =>
          simpa [Word.final, Word.toList] using
            (List.getLastD_mem_cons (l := tail) (a := head))
    have finalPositive :
        0 < word.toList.count word.final :=
      List.count_pos_iff.mpr finalMember
    have finalMultiple :
        cappedMultiplicity word word.final = 2 :=
      (cappedMultiplicity_eq_two_iff word word.final).2 <| by
        omega
    have finalSequenceMember :
        word.final ∈
          firstOccurrenceSequence word.toList :=
      (mem_firstOccurrenceSequence_iff
        word.final word.toList).2 finalMember
    obtain
      ⟨marker, before, markerTail, firstShape, sequenceShape,
        beforeNonmultiple, markerMultiple⟩ :=
      firstMultiple_split_of_exists
        (cappedMultiplicity word)
        (firstOccurrenceSequence word.toList)
        ⟨word.final, finalSequenceMember, finalMultiple⟩
    have markerShape :
        terminalMarker word = some marker := by
      simp [terminalMarker, simpleFinalVariable, finalSimple,
        earliestMultiple, firstShape]
    by_cases markerFinal : marker = word.final
    · subst marker
      have blockEq :
          subsystemBlock word.toList word.final =
            canonicalBlock word := by
        funext letter
        by_cases equal : letter = word.final
        · subst letter
          simp [subsystemBlock, canonicalBlock, markerShape]
        · simp [subsystemBlock, canonicalBlock, equal,
            markerShape, Ne.symm equal,
            cappedMultiplicity_eq_one_iff]
      have formsEqual :
          subsystemCanonicalList word = canonicalList word := by
        simp [subsystemCanonicalList, canonicalList,
          finalSimple, markerShape, blockEq]
      rw [formsEqual]
      exact S5_107.ListDerives.refl _
    · have finalInTail : word.final ∈ markerTail := by
        rw [sequenceShape] at finalSequenceMember
        rcases List.mem_append.mp finalSequenceMember with
          finalBefore | finalAtOrAfter
        · exact False.elim <|
            (beforeNonmultiple word.final finalBefore)
              finalMultiple
        · rcases List.mem_cons.mp finalAtOrAfter with
            equal | finalTail
          · exact False.elim (markerFinal equal.symm)
          · exact finalTail
      obtain ⟨finalSplit, finalSplitShape⟩ :=
        splitFirst_some_of_mem word.final finalInTail
      have tailShape :
          markerTail =
            finalSplit.before ++ word.final :: finalSplit.after :=
        splitFirst_reconstruction
          word.final markerTail finalSplit finalSplitShape
      have labelsNodup :
          (firstOccurrenceSequence word.toList).Nodup :=
        firstOccurrenceSequence_nodup word.toList
      have markerAbsent :=
        not_mem_parts_of_nodup_split
          labelsNodup sequenceShape
      have finalSequenceShape :
          firstOccurrenceSequence word.toList =
            (before ++ marker :: finalSplit.before) ++
              word.final :: finalSplit.after := by
        rw [sequenceShape, tailShape]
        simp [List.append_assoc]
      have finalAbsent :=
        not_mem_parts_of_nodup_split
          labelsNodup finalSequenceShape
      have markerNotBefore : marker ∉ before :=
        markerAbsent.1
      have markerNotMiddle : marker ∉ finalSplit.before := by
        intro member
        apply markerAbsent.2
        rw [tailShape]
        exact List.mem_append_left _ member
      have markerNotAfter : marker ∉ finalSplit.after := by
        intro member
        apply markerAbsent.2
        rw [tailShape]
        exact
          List.mem_append_right finalSplit.before <|
            List.Mem.tail word.final member
      have finalNotBefore : word.final ∉ before := by
        intro member
        apply finalAbsent.1
        exact List.mem_append_left _ member
      have finalNotMiddle :
          word.final ∉ finalSplit.before := by
        intro member
        apply finalAbsent.1
        exact
          List.mem_append_right before <|
            List.Mem.tail marker member
      have finalNotAfter : word.final ∉ finalSplit.after :=
        finalAbsent.2
      have markerNotSimple :
          word.toList.count marker ≠ 1 := by
        intro markerSimple
        have markerCapped :
            cappedMultiplicity word marker = 1 :=
          (cappedMultiplicity_eq_one_iff word marker).2
            markerSimple
        rw [markerMultiple] at markerCapped
        omega
      have subsystemMarker :
          subsystemBlock word.toList word.final marker =
            [marker, marker] := by
        simp [subsystemBlock, markerFinal, markerNotSimple]
      have subsystemFinal :
          subsystemBlock word.toList word.final word.final =
            [word.final] := by
        simp [subsystemBlock]
      have canonicalMarker :
          canonicalBlock word marker = [marker] := by
        simp [canonicalBlock, markerShape]
      have canonicalFinal :
          canonicalBlock word word.final =
            [word.final, word.final] := by
        simp [canonicalBlock, markerShape, markerFinal,
          finalSimple, cappedMultiplicity_eq_one_iff]
      have beforeBlocks :
          before.flatMap (canonicalBlock word) =
            before.flatMap
              (subsystemBlock word.toList word.final) := by
        apply flatMap_congr_of_mem
        intro letter member
        exact
          (subsystemBlock_eq_canonicalBlock_of_ne
            word marker letter markerShape
            (fun equal => finalNotBefore <| equal ▸ member)
            (fun equal => markerNotBefore <| equal ▸ member)).symm
      have middleBlocks :
          finalSplit.before.flatMap (canonicalBlock word) =
            finalSplit.before.flatMap
              (subsystemBlock word.toList word.final) := by
        apply flatMap_congr_of_mem
        intro letter member
        exact
          (subsystemBlock_eq_canonicalBlock_of_ne
            word marker letter markerShape
            (fun equal => finalNotMiddle <| equal ▸ member)
            (fun equal => markerNotMiddle <| equal ▸ member)).symm
      have afterBlocks :
          finalSplit.after.flatMap (canonicalBlock word) =
            finalSplit.after.flatMap
              (subsystemBlock word.toList word.final) := by
        apply flatMap_congr_of_mem
        intro letter member
        exact
          (subsystemBlock_eq_canonicalBlock_of_ne
            word marker letter markerShape
            (fun equal => finalNotAfter <| equal ▸ member)
            (fun equal => markerNotAfter <| equal ▸ member)).symm
      have sourceShape :
          subsystemCanonicalList word =
            before.flatMap
                (subsystemBlock word.toList word.final) ++
              [marker, marker] ++
              finalSplit.before.flatMap
                (subsystemBlock word.toList word.final) ++
              [word.final] ++
              finalSplit.after.flatMap
                (subsystemBlock word.toList word.final) ++
              [word.final] := by
        unfold subsystemCanonicalList
        rw [sequenceShape, tailShape]
        simp only [List.flatMap_append, List.flatMap_cons]
        rw [subsystemMarker, subsystemFinal,
          if_neg finalSimple]
        simp [List.append_assoc]
      have targetShape :
          canonicalList word =
            before.flatMap
                (subsystemBlock word.toList word.final) ++
              [marker] ++
              finalSplit.before.flatMap
                (subsystemBlock word.toList word.final) ++
              [word.final, word.final] ++
              finalSplit.after.flatMap
                (subsystemBlock word.toList word.final) ++
              [marker] := by
        unfold canonicalList
        rw [sequenceShape, tailShape]
        simp only [List.flatMap_append, List.flatMap_cons]
        rw [canonicalMarker, canonicalFinal, beforeBlocks,
          middleBlocks, afterBlocks, markerShape]
        simp [List.append_assoc]
      rw [sourceShape, targetShape]
      simpa [List.append_assoc] using
        listDerivesTerminalMarkerSwitch
          (before.flatMap
            (subsystemBlock word.toList word.final))
          [] marker word.final
          (finalSplit.before.flatMap
            (subsystemBlock word.toList word.final))
          (finalSplit.after.flatMap
            (subsystemBlock word.toList word.final))

/-- A certified split at an adjacent selected square. -/
structure DoubleSplit where
  before : List Nat
  after : List Nat

/-- Split at the first adjacent selected square. -/
def splitDouble (selected : Nat) :
    List Nat → Option DoubleSplit
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if firstEqual : first = selected then
        if secondEqual : second = selected then
          some
            { before := []
              after := rest }
        else
          match splitDouble selected (second :: rest) with
          | none => none
          | some split =>
              some
                { before := first :: split.before
                  after := split.after }
      else
        match splitDouble selected (second :: rest) with
        | none => none
        | some split =>
            some
              { before := first :: split.before
                after := split.after }
termination_by letters => letters.length

private theorem splitDouble_reconstruction
    (selected : Nat) :
    ∀ (letters : List Nat) (split : DoubleSplit),
      splitDouble selected letters = some split →
      letters =
        split.before ++ selected :: selected :: split.after
  | [], _, result => by
      simp [splitDouble] at result
  | [_], _, result => by
      simp [splitDouble] at result
  | first :: second :: rest, split, result => by
      by_cases firstEqual : first = selected
      · subst first
        by_cases secondEqual : second = selected
        · subst second
          have splitShape :
              ({ before := []
                 after := rest } : DoubleSplit) = split := by
            simpa [splitDouble] using result
          subst split
          rfl
        · cases restShape :
            splitDouble selected (second :: rest) with
          | none =>
              simp [splitDouble, secondEqual, restShape] at result
          | some restSplit =>
              have reconstruction :=
                splitDouble_reconstruction
                  selected (second :: rest) restSplit restShape
              have splitShape :
                  ({ before := selected :: restSplit.before
                     after := restSplit.after } : DoubleSplit) =
                    split := by
                simpa [splitDouble, secondEqual, restShape] using result
              subst split
              exact
                congrArg (List.cons selected) reconstruction
      · cases restShape :
          splitDouble selected (second :: rest) with
        | none =>
            simp [splitDouble, firstEqual, restShape] at result
        | some restSplit =>
            have reconstruction :=
              splitDouble_reconstruction
                selected (second :: rest) restSplit restShape
            have splitShape :
                ({ before := first :: restSplit.before
                   after := restSplit.after } : DoubleSplit) =
                  split := by
              simpa [splitDouble, firstEqual, restShape] using result
            subst split
            exact congrArg (List.cons first) reconstruction
termination_by letters => letters.length

/-- Search after a selected square for two occurrences of the final letter.
The returned list is the result of the terminal-marker switch. -/
def switchAfterMarker (marker final : Nat) :
    List Nat → List Nat → Option (List Nat)
  | _, [] => none
  | before, letter :: rest =>
      if equal : letter = final then
        match splitFirst final rest with
        | none => none
        | some split =>
            some
              ([marker] ++ before ++ [final, final] ++
                split.before ++ [marker] ++ split.after)
      else
        switchAfterMarker marker final
          (before ++ [letter]) rest
termination_by _ rest => rest.length

/-- Every successful result returned by `switchAfterMarker` is connected to
its source by the unrestricted terminal-marker switch. -/
theorem listDerivesSwitchAfterMarker
    (marker final : Nat) :
    ∀ (before rest target : List Nat),
      switchAfterMarker marker final before rest = some target →
      S5_107.ListDerives basis
        ([marker, marker] ++ before ++ rest)
        target
  | _, [], _, result => by
      simp [switchAfterMarker] at result
  | before, letter :: rest, target, result => by
      by_cases equal : letter = final
      · subst letter
        cases splitShape : splitFirst final rest with
        | none =>
            simp [switchAfterMarker, splitShape] at result
        | some split =>
            have restReconstruction :=
              splitFirst_reconstruction
                final rest split splitShape
            have targetShape :
                [marker] ++ before ++ [final, final] ++
                    split.before ++ [marker] ++ split.after =
                  target := by
              simpa [switchAfterMarker, splitShape] using result
            subst target
            rw [restReconstruction]
            simpa [List.append_assoc] using
              listDerivesTerminalMarkerSwitch
                [] split.after marker final before split.before
      · have recursiveResult :
            switchAfterMarker marker final
                (before ++ [letter]) rest =
              some target := by
          simpa [switchAfterMarker, equal] using result
        have remaining :=
          listDerivesSwitchAfterMarker
            marker final (before ++ [letter]) rest target
              recursiveResult
        simpa [List.append_assoc] using remaining

/-- Apply at most one terminal-marker switch to the first adjacent square of
the selected marker. The function is total and leaves malformed inputs
unchanged. -/
def terminalSwitchCanonical
    (marker final : Nat) (letters : List Nat) : List Nat :=
  match splitDouble marker letters with
  | none => letters
  | some split =>
      match switchAfterMarker marker final [] split.after with
      | none => letters
      | some switched => split.before ++ switched

/-- The total terminal-switch postprocessor is always derivable from its
input, including its unchanged fallback cases. -/
theorem listDerivesTerminalSwitchCanonical
    (marker final : Nat) (letters : List Nat) :
    S5_107.ListDerives basis letters
      (terminalSwitchCanonical marker final letters) := by
  cases splitShape : splitDouble marker letters with
  | none =>
      simpa [terminalSwitchCanonical, splitShape] using
        S5_107.ListDerives.refl (basis := basis) letters
  | some split =>
      cases switchShape :
          switchAfterMarker marker final [] split.after with
      | none =>
          simpa [terminalSwitchCanonical, splitShape, switchShape] using
            S5_107.ListDerives.refl (basis := basis) letters
      | some switched =>
          have core :=
            listDerivesSwitchAfterMarker
              marker final [] split.after switched switchShape
          have contextual := core.prepend split.before
          have reconstruction :=
            splitDouble_reconstruction
              marker letters split splitShape
          have targetShape :
              terminalSwitchCanonical marker final letters =
                split.before ++ switched := by
            simp [terminalSwitchCanonical, splitShape, switchShape]
          rw [targetShape, reconstruction]
          simpa [List.append_assoc] using contextual

/-- Deterministic normal form for the full eight-law basis. It first uses the
`S5_863` block normalization and then, when present, turns the earliest
multiple variable into the repeated terminal marker. -/
private def algorithmicCanonicalList (word : Word Nat) : List Nat :=
  let core := coreCanonicalList word.toList
  match terminalMarker word with
  | none => core
  | some marker =>
      terminalSwitchCanonical marker word.final core

/-- Every list derives directly to the deterministic full normal form. -/
private theorem listDerivesAlgorithmicCanonical
    (word : Word Nat) :
    S5_107.ListDerives basis word.toList
      (algorithmicCanonicalList word) := by
  let core := coreCanonicalList word.toList
  have coreDerivation := listDerivesCoreCanonical word.toList
  cases markerShape : terminalMarker word with
  | none =>
      simpa [algorithmicCanonicalList, core, markerShape] using
        coreDerivation
  | some marker =>
      have switched :=
        listDerivesTerminalSwitchCanonical
          marker word.final core
      exact coreDerivation.trans <| by
        simpa [algorithmicCanonicalList, core, markerShape] using switched

private def algorithmicWordOfListD
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

private def algorithmicCanonicalWord (word : Word Nat) : Word Nat :=
  algorithmicWordOfListD word.head
    (algorithmicCanonicalList word)

/-- Every semigroup word derives to its deterministic `S5_345` canonical
word. -/
theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonicalWord word) := by
  cases word with
  | mk head tail =>
      have coreDerivation :=
        listDerivesCoreCanonical (Word.mk head tail).toList
      rw [
        coreCanonicalList_eq_subsystemCanonicalList
          (Word.mk head tail)
      ] at coreDerivation
      have listDerivation :=
        coreDerivation.trans <|
          listDerivesSubsystemCanonical (Word.mk head tail)
      cases canonicalShape :
          canonicalList (Word.mk head tail) with
      | nil =>
          have nonempty :=
            S5_107.ListDerives.target_ne_nil listDerivation
          exact False.elim (nonempty canonicalShape)
      | cons canonicalHead canonicalTail =>
          have listDerivation' :
              S5_107.ListDerives basis
                (head :: tail)
                (canonicalHead :: canonicalTail) := by
            simpa [canonicalShape] using listDerivation
          have wordDerivation :=
            S5_107.ListDerives.toWord listDerivation'
          have targetEq :
              (⟨canonicalHead, canonicalTail⟩ : Word Nat) =
                canonicalWord (Word.mk head tail) := by
            apply Word.toList_injective
            rw [toList_canonicalWord]
            exact canonicalShape.symm
          rw [← targetEq]
          exact wordDerivation

end SemigroupBasis.CoRoots.S5_345
