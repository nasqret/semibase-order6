import SemigroupBasis.CoRoots.S5_869Invariant
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.S5_869

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev wordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- Delete a repeated singleton after a nonempty prefix. -/
private theorem listDerivesDeleteRepeat
    (stem middle suffix : List Nat) (letter : Nat)
    (stemNonempty : stem ≠ []) :
    ListDerives
      (stem ++ [letter] ++ middle ++ [letter] ++ suffix)
      (stem ++ [letter] ++ middle ++ suffix) := by
  obtain ⟨prefixHead, prefixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil stemNonempty
  cases middle with
  | nil =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesTailContraction
            (wordOfCons prefixHead prefixTail)
            (Word.singleton letter)
      simpa [wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using core.append suffix
  | cons middleHead middleTail =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesNoninitialRepeatDeletion
            (wordOfCons prefixHead prefixTail)
            (Word.singleton letter)
            (wordOfCons middleHead middleTail)
      simpa [wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using core.append suffix

/-- Output of the stateful pass that removes repeated noninitial letters. -/
private def noninitialScanOutput (initial : Nat)
    (prefixTail : List Nat) : List Nat → List Nat
  | [] => prefixTail
  | letter :: rest =>
      if letter = initial then
        noninitialScanOutput initial (prefixTail ++ [letter]) rest
      else if letter ∈ prefixTail then
        noninitialScanOutput initial prefixTail rest
      else
        noninitialScanOutput initial (prefixTail ++ [letter]) rest

/-- Run the noninitial pass behind the actual nonempty prefix. -/
private theorem listDerivesNoninitialScan (initial : Nat) :
    ∀ (prefixTail rest : List Nat),
      ListDerives
        ((initial :: prefixTail) ++ rest)
        (initial :: noninitialScanOutput initial prefixTail rest)
  | prefixTail, [] => by
      simpa [noninitialScanOutput] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (initial :: prefixTail))
  | prefixTail, letter :: rest => by
      by_cases equal : letter = initial
      · subst letter
        have remaining :=
          listDerivesNoninitialScan initial
            (prefixTail ++ [initial]) rest
        simpa [noninitialScanOutput, List.append_assoc] using remaining
      · by_cases seen : letter ∈ prefixTail
        · obtain ⟨before, after, split⟩ :=
            List.mem_iff_append.mp seen
          have deleted :=
            listDerivesDeleteRepeat
              (initial :: before) after rest letter (by simp)
          have deletedCurrent :
              ListDerives
                ((initial :: prefixTail) ++ (letter :: rest))
                ((initial :: prefixTail) ++ rest) := by
            simpa [split, List.append_assoc] using deleted
          have remaining :=
            listDerivesNoninitialScan initial prefixTail rest
          simpa [noninitialScanOutput, equal, seen,
            List.append_assoc] using deletedCurrent.trans remaining
        · have remaining :=
            listDerivesNoninitialScan initial
              (prefixTail ++ [letter]) rest
          simpa [noninitialScanOutput, equal, seen,
            List.append_assoc] using remaining

/-- Delete a third or later occurrence of the initial singleton. -/
private theorem listDerivesDeleteThirdInitial
    (initial : Nat) (before middle suffix : List Nat) :
    ListDerives
      ([initial] ++ before ++ [initial] ++ middle ++ [initial] ++ suffix)
      ([initial] ++ before ++ [initial] ++ middle ++ suffix) := by
  cases before with
  | nil =>
      cases middle with
      | nil =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesInitialExcessDeletion_bothEmpty
                (Word.singleton initial)
          simpa [Word.append, Word.singleton,
            List.append_assoc] using core.append suffix
      | cons middleHead middleTail =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesInitialExcessDeletion_leftEmpty
                (Word.singleton initial)
                (wordOfCons middleHead middleTail)
          simpa [wordOfCons, Word.append, Word.singleton,
            List.append_assoc] using core.append suffix
  | cons beforeHead beforeTail =>
      cases middle with
      | nil =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesInitialExcessDeletion_rightEmpty
                (Word.singleton initial)
                (wordOfCons beforeHead beforeTail)
          simpa [wordOfCons, Word.append, Word.singleton,
            List.append_assoc] using core.append suffix
      | cons middleHead middleTail =>
          have core :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesInitialExcessDeletion
                (Word.singleton initial)
                (wordOfCons beforeHead beforeTail)
                (wordOfCons middleHead middleTail)
          simpa [wordOfCons, Word.append, Word.singleton,
            List.append_assoc] using core.append suffix

/-- Remove every later initial letter once two copies have been retained. -/
private def deleteLaterInitial (initial : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = initial then
        deleteLaterInitial initial rest
      else
        letter :: deleteLaterInitial initial rest

private theorem listDerivesDeleteLaterInitial (initial : Nat) :
    ∀ (before middle rest : List Nat),
      ListDerives
        ([initial] ++ before ++ [initial] ++ middle ++ rest)
        ([initial] ++ before ++ [initial] ++ middle ++
          deleteLaterInitial initial rest)
  | before, middle, [] => by
      simpa [deleteLaterInitial] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          ([initial] ++ before ++ [initial] ++ middle))
  | before, middle, letter :: rest => by
      by_cases equal : letter = initial
      · subst letter
        have deleted :=
          listDerivesDeleteThirdInitial initial before middle rest
        have remaining :=
          listDerivesDeleteLaterInitial initial before middle rest
        have deletedCurrent :
            ListDerives
              ([initial] ++ before ++ [initial] ++ middle ++
                [initial] ++ rest)
              ([initial] ++ before ++ [initial] ++ middle ++ rest) := by
          simpa [List.append_assoc] using deleted
        have composed := deletedCurrent.trans remaining
        simpa [deleteLaterInitial, List.append_assoc] using composed
      · have remaining :=
          listDerivesDeleteLaterInitial initial
            before (middle ++ [letter]) rest
        simpa [deleteLaterInitial, equal,
          List.append_assoc] using remaining

/-- Retain the first initial letter found in a tail as the second copy. -/
private def seekSecondInitial (initial : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = initial then
        letter :: deleteLaterInitial initial rest
      else
        letter :: seekSecondInitial initial rest

private theorem listDerivesSeekSecondInitial (initial : Nat) :
    ∀ (before rest : List Nat),
      ListDerives
        ([initial] ++ before ++ rest)
        ([initial] ++ before ++ seekSecondInitial initial rest)
  | before, [] => by
      simpa [seekSecondInitial] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) ([initial] ++ before))
  | before, letter :: rest => by
      by_cases equal : letter = initial
      · subst letter
        have deleted :=
          listDerivesDeleteLaterInitial initial before [] rest
        simpa [seekSecondInitial,
          List.append_assoc] using deleted
      · have remaining :=
          listDerivesSeekSecondInitial initial
            (before ++ [letter]) rest
        simpa [seekSecondInitial, equal,
          List.append_assoc] using remaining

/-- Render the first-occurrence order with one extra initial at its exact
second-occurrence cut. -/
def renderInitialSecondGap
    (sequence : List Nat) (repeated : Bool)
    (beforeSecond : Nat → Bool) : List Nat :=
  if repeated then
    match sequence.head? with
    | none => []
    | some head =>
        sequence.filter beforeSecond ++ [head] ++
          sequence.filter (fun letter => !(beforeSecond letter))
  else
    sequence

private def noninitialScanDelta (initial : Nat)
    (seen : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = initial then
        letter :: noninitialScanDelta initial (seen ++ [letter]) rest
      else if letter ∈ seen then
        noninitialScanDelta initial seen rest
      else
        letter :: noninitialScanDelta initial (seen ++ [letter]) rest

private theorem noninitialScanOutput_eq_append_delta
    (initial : Nat) :
    ∀ (seen rest : List Nat),
      noninitialScanOutput initial seen rest =
        seen ++ noninitialScanDelta initial seen rest := by
  intro seen rest
  induction rest generalizing seen with
  | nil =>
      simp [noninitialScanOutput, noninitialScanDelta]
  | cons letter rest induction =>
      by_cases equal : letter = initial
      · subst letter
        simp [noninitialScanOutput, noninitialScanDelta,
          induction, List.append_assoc]
      · by_cases member : letter ∈ seen
        · simp [noninitialScanOutput, noninitialScanDelta,
            equal, member, induction]
        · simp [noninitialScanOutput, noninitialScanDelta,
            equal, member, induction, List.append_assoc]

private def unseenNoninitial
    (initial : Nat) (seen : List Nat) : Nat → Bool :=
  fun letter => decide (letter ≠ initial ∧ letter ∉ seen)

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
    (dropped : ¬keep selected)
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

private theorem firstOccurrenceSequence_filter
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

private theorem filter_unseen_append
    (initial selected : Nat) (seen letters : List Nat) :
    letters.filter
        (unseenNoninitial initial (seen ++ [selected])) =
      (letters.filter (unseenNoninitial initial seen)).filter
        (fun letter => decide (letter ≠ selected)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases differentInitial : letter ≠ initial
  · by_cases absentSeen : letter ∉ seen
    · by_cases differentSelected : letter ≠ selected
      · simp [unseenNoninitial, differentInitial, absentSeen,
          differentSelected, List.mem_append]
      · simp [unseenNoninitial, differentInitial, absentSeen,
          differentSelected, List.mem_append]
    · simp [unseenNoninitial, differentInitial, absentSeen,
        List.mem_append]
  · simp [unseenNoninitial, differentInitial]

private theorem deleteLaterInitial_noninitialScanDelta
    (initial : Nat) :
    ∀ (seen rest : List Nat),
      deleteLaterInitial initial
          (noninitialScanDelta initial seen rest) =
        (firstOccurrenceSequence rest).filter
          (unseenNoninitial initial seen)
  | seen, [] => by
      simp [noninitialScanDelta, deleteLaterInitial,
        firstOccurrenceSequence]
  | seen, letter :: rest => by
      by_cases equal : letter = initial
      · subst letter
        have induction :=
          deleteLaterInitial_noninitialScanDelta initial
            (seen ++ [initial]) rest
        have predicateEq :
            unseenNoninitial initial (seen ++ [initial]) =
              unseenNoninitial initial seen := by
          funext tested
          by_cases different : tested ≠ initial
          · simp [unseenNoninitial, different, List.mem_append]
          · simp [unseenNoninitial, different]
        have dropped : ¬unseenNoninitial initial seen initial := by
          simp [unseenNoninitial]
        simp only [noninitialScanDelta, deleteLaterInitial,
          ↓reduceIte]
        rw [induction, predicateEq]
        change
          (firstOccurrenceSequence rest).filter
              (unseenNoninitial initial seen) =
            (initial ::
                (firstOccurrenceSequence rest).filter
                  (fun tested => decide (tested ≠ initial))).filter
              (unseenNoninitial initial seen)
        rw [List.filter_cons, if_neg dropped]
        exact
          (filter_ne_then_keep_of_drop
            (unseenNoninitial initial seen) initial dropped
            (firstOccurrenceSequence rest)).symm
      · by_cases member : letter ∈ seen
        · have induction :=
            deleteLaterInitial_noninitialScanDelta initial seen rest
          have dropped : ¬unseenNoninitial initial seen letter := by
            simp [unseenNoninitial, member]
          simp only [noninitialScanDelta, equal, member,
            ↓reduceIte]
          rw [induction]
          change
            (firstOccurrenceSequence rest).filter
                (unseenNoninitial initial seen) =
              (letter ::
                  (firstOccurrenceSequence rest).filter
                    (fun tested => decide (tested ≠ letter))).filter
                (unseenNoninitial initial seen)
          rw [List.filter_cons, if_neg dropped]
          exact
            (filter_ne_then_keep_of_drop
              (unseenNoninitial initial seen) letter dropped
              (firstOccurrenceSequence rest)).symm
        · have induction :=
            deleteLaterInitial_noninitialScanDelta initial
              (seen ++ [letter]) rest
          have kept : unseenNoninitial initial seen letter := by
            simp [unseenNoninitial, equal, member]
          simp only [noninitialScanDelta, deleteLaterInitial,
            equal, member, ↓reduceIte]
          rw [induction]
          change
            letter ::
                (firstOccurrenceSequence rest).filter
                  (unseenNoninitial initial (seen ++ [letter])) =
              (letter ::
                  (firstOccurrenceSequence rest).filter
                    (fun tested => decide (tested ≠ letter))).filter
                (unseenNoninitial initial seen)
          rw [List.filter_cons, if_pos kept]
          rw [← filter_filter_ne_comm
            (unseenNoninitial initial seen) letter
            (firstOccurrenceSequence rest)]
          exact congrArg (List.cons letter) <|
            filter_unseen_append initial letter seen
              (firstOccurrenceSequence rest)

private theorem mem_noninitialScanDelta
    (initial tested : Nat) :
    ∀ {seen rest : List Nat},
      tested ∈ noninitialScanDelta initial seen rest → tested ∈ rest
  | _, [], member => by
      simp [noninitialScanDelta] at member
  | seen, letter :: rest, member => by
      by_cases equal : letter = initial
      · simp only [noninitialScanDelta, equal, ↓reduceIte,
          List.mem_cons] at member
        rcases member with same | member
        · exact List.mem_cons.mpr <| Or.inl (same.trans equal.symm)
        · exact List.mem_cons.mpr <| Or.inr <|
            mem_noninitialScanDelta initial tested member
      · by_cases seenMember : letter ∈ seen
        · simp only [noninitialScanDelta, equal, seenMember,
            ↓reduceIte] at member
          exact List.mem_cons.mpr <| Or.inr <|
            mem_noninitialScanDelta initial tested member
        · simp only [noninitialScanDelta, equal, seenMember,
            ↓reduceIte, List.mem_cons] at member
          rcases member with same | member
          · exact List.mem_cons.mpr <| Or.inl same
          · exact List.mem_cons.mpr <| Or.inr <|
              mem_noninitialScanDelta initial tested member

private theorem deleteLaterInitial_eq_self_of_not_mem
    (initial : Nat) :
    ∀ {letters : List Nat}, initial ∉ letters →
      deleteLaterInitial initial letters = letters
  | [], _ => rfl
  | letter :: rest, absent => by
      have different : letter ≠ initial := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : initial ∉ rest := fun member =>
        absent (List.Mem.tail letter member)
      simp [deleteLaterInitial, different,
        deleteLaterInitial_eq_self_of_not_mem initial restAbsent]

private theorem noninitialScanOutput_eq_firstOccurrenceSequence_of_not_mem
    (initial : Nat) (letters : List Nat)
    (absent : initial ∉ letters) :
    noninitialScanOutput initial [] letters =
      firstOccurrenceSequence letters := by
  rw [noninitialScanOutput_eq_append_delta initial [] letters]
  simp only [List.nil_append]
  have deltaAbsent :
      initial ∉ noninitialScanDelta initial [] letters := by
    intro member
    exact absent <|
      mem_noninitialScanDelta initial initial member
  have sequenceAbsent :
      initial ∉ firstOccurrenceSequence letters := by
    intro member
    exact absent <|
      (mem_firstOccurrenceSequence_iff initial letters).mp member
  have keepSequence :
      (firstOccurrenceSequence letters).filter
          (unseenNoninitial initial []) =
        firstOccurrenceSequence letters := by
    apply List.filter_eq_self.mpr
    intro letter member
    have different : letter ≠ initial := by
      intro equal
      subst letter
      exact sequenceAbsent member
    simp [unseenNoninitial, different]
  calc
    noninitialScanDelta initial [] letters =
        deleteLaterInitial initial
          (noninitialScanDelta initial [] letters) :=
      (deleteLaterInitial_eq_self_of_not_mem
        initial deltaAbsent).symm
    _ = (firstOccurrenceSequence letters).filter
          (unseenNoninitial initial []) :=
      deleteLaterInitial_noninitialScanDelta initial [] letters
    _ = firstOccurrenceSequence letters := keepSequence

private theorem noninitialScanOutput_append
    (initial : Nat) :
    ∀ (seen left right : List Nat),
      noninitialScanOutput initial seen (left ++ right) =
        noninitialScanOutput initial
          (noninitialScanOutput initial seen left) right
  | seen, [], right => by
      simp [noninitialScanOutput]
  | seen, letter :: rest, right => by
      by_cases equal : letter = initial
      · subst letter
        simp [noninitialScanOutput,
          noninitialScanOutput_append initial]
      · by_cases member : letter ∈ seen
        · simp [noninitialScanOutput, equal, member,
            noninitialScanOutput_append initial]
        · simp [noninitialScanOutput, equal, member,
            noninitialScanOutput_append initial]

private theorem seekSecondInitial_eq_self_of_not_mem
    (initial : Nat) :
    ∀ {letters : List Nat}, initial ∉ letters →
      seekSecondInitial initial letters = letters
  | [], _ => rfl
  | letter :: rest, absent => by
      have different : letter ≠ initial := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : initial ∉ rest := fun member =>
        absent (List.Mem.tail letter member)
      simp [seekSecondInitial, different,
        seekSecondInitial_eq_self_of_not_mem initial restAbsent]

private theorem seekSecondInitial_at_first
    (initial : Nat) :
    ∀ (before rest : List Nat), initial ∉ before →
      seekSecondInitial initial (before ++ [initial] ++ rest) =
        before ++ [initial] ++ deleteLaterInitial initial rest
  | [], rest, _ => by
      simp [seekSecondInitial]
  | letter :: before, rest, absent => by
      have different : letter ≠ initial := by
        intro equal
        subst letter
        exact absent (List.Mem.head before)
      have beforeAbsent : initial ∉ before := fun member =>
        absent (List.Mem.tail letter member)
      simpa [seekSecondInitial, different, List.append_assoc] using
        seekSecondInitial_at_first initial before rest beforeAbsent

private def tailAfterFirst (selected : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter = selected then rest else tailAfterFirst selected rest

private theorem splitAtFirst
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      letters = prefixBefore selected letters ++
        selected :: tailAfterFirst selected letters
  | [], member => by
      simp at member
  | letter :: rest, member => by
      by_cases equal : letter = selected
      · subst letter
        simp [prefixBefore, tailAfterFirst]
      · have restMember : selected ∈ rest := by
          rcases List.mem_cons.mp member with same | member
          · exact False.elim (equal same.symm)
          · exact member
        simp only [prefixBefore, tailAfterFirst, equal, ↓reduceIte]
        exact congrArg (List.cons letter) <|
          splitAtFirst selected restMember

private theorem not_mem_prefixBefore
    (selected : Nat) :
    ∀ letters : List Nat, selected ∉ prefixBefore selected letters
  | [] => by simp [prefixBefore]
  | letter :: rest => by
      by_cases equal : letter = selected
      · subst letter
        simp [prefixBefore]
      · simp [prefixBefore, equal, Ne.symm equal,
          not_mem_prefixBefore selected rest]

private theorem prefixBefore_append_selected
    (selected : Nat) :
    ∀ (before after : List Nat), selected ∉ before →
      prefixBefore selected (before ++ selected :: after) = before
  | [], after, _ => by
      simp [prefixBefore]
  | letter :: before, after, absent => by
      have different : letter ≠ selected := by
        intro equal
        subst letter
        exact absent (List.Mem.head before)
      have beforeAbsent : selected ∉ before := fun member =>
        absent (List.Mem.tail letter member)
      simp [prefixBefore, different,
        prefixBefore_append_selected selected before after beforeAbsent]

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
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

private theorem firstOccurrenceSequence_append_of_subset :
    ∀ (right left : List Nat),
      (∀ letter, letter ∈ right → letter ∈ left) →
      firstOccurrenceSequence (left ++ right) =
        firstOccurrenceSequence left
  | [], left, _ => by simp
  | letter :: rest, left, subset => by
      have letterMember : letter ∈ left :=
        subset letter (List.Mem.head rest)
      have restSubset :
          ∀ tested, tested ∈ rest → tested ∈ left ++ [letter] := by
        intro tested member
        exact List.mem_append_left [letter] (subset tested <|
          List.Mem.tail letter member)
      calc
        firstOccurrenceSequence (left ++ letter :: rest) =
            firstOccurrenceSequence ((left ++ [letter]) ++ rest) := by
          simp [List.append_assoc]
        _ = firstOccurrenceSequence (left ++ [letter]) :=
          firstOccurrenceSequence_append_of_subset rest
            (left ++ [letter]) restSubset
        _ = firstOccurrenceSequence left := by
          rw [firstOccurrenceSequence_append_singleton,
            if_pos letterMember]

private def splitProfile
    (initial : Nat) (before : List Nat) : Nat → Bool :=
  fun tested => decide (tested = initial ∨ tested ∈ before)

private theorem not_splitProfile_eq_unseen
    (initial : Nat) (before : List Nat) :
    (fun tested => !(splitProfile initial before tested)) =
      unseenNoninitial initial
        (firstOccurrenceSequence before ++ [initial]) := by
  funext tested
  by_cases equal : tested = initial
  · subst tested
    simp [splitProfile, unseenNoninitial]
  · by_cases member : tested ∈ before
    · have sequenceMember :
          tested ∈ firstOccurrenceSequence before :=
        (mem_firstOccurrenceSequence_iff tested before).mpr member
      simp [splitProfile, unseenNoninitial, equal, member,
        sequenceMember, List.mem_append]
    · have sequenceAbsent :
          tested ∉ firstOccurrenceSequence before := by
        intro sequenceMember
        exact member <|
          (mem_firstOccurrenceSequence_iff tested before).mp
            sequenceMember
      simp [splitProfile, unseenNoninitial, equal, member,
        sequenceAbsent, List.mem_append]

private theorem filter_splitProfile_source
    (initial : Nat) (before after : List Nat) :
    (initial :: before ++ initial :: after).filter
        (splitProfile initial before) =
      (initial :: before) ++
        (initial :: after.filter (splitProfile initial before)) := by
  have keepBefore :
      before.filter (splitProfile initial before) = before := by
    apply List.filter_eq_self.mpr
    intro tested member
    simp [splitProfile, member]
  rw [show initial :: before ++ initial :: after =
      [initial] ++ before ++ [initial] ++ after by
    simp [List.append_assoc]]
  simp [List.filter_append, splitProfile, keepBefore,
    List.append_assoc]

private theorem filter_not_splitProfile_source
    (initial : Nat) (before after : List Nat) :
    (initial :: before ++ initial :: after).filter
        (fun tested => !(splitProfile initial before tested)) =
      after.filter (fun tested => !(splitProfile initial before tested)) := by
  have dropBefore :
      before.filter
          (fun tested => !(splitProfile initial before tested)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro tested member
    simp [splitProfile, member]
  rw [show initial :: before ++ initial :: after =
      [initial] ++ before ++ [initial] ++ after by
    simp [List.append_assoc]]
  simp [List.filter_append, splitProfile, dropBefore,
    List.append_assoc]
  exact fun _ member _ => member

private theorem firstOccurrences_filter_splitProfile
    (initial : Nat) (before after : List Nat)
    (absent : initial ∉ before) :
    (firstOccurrenceSequence
        (initial :: before ++ initial :: after)).filter
        (splitProfile initial before) =
      initial :: firstOccurrenceSequence before := by
  have suffixSubset :
      ∀ tested,
        tested ∈ initial ::
            after.filter (splitProfile initial before) →
          tested ∈ initial :: before := by
    intro tested member
    rcases List.mem_cons.mp member with equal | member
    · exact List.mem_cons.mpr <| Or.inl equal
    · have kept := (List.mem_filter.mp member).2
      simp only [splitProfile, decide_eq_true_eq] at kept
      rcases kept with equal | beforeMember
      · exact List.mem_cons.mpr <| Or.inl equal
      · exact List.mem_cons.mpr <| Or.inr beforeMember
  have sequenceAbsent :
      initial ∉ firstOccurrenceSequence before := by
    intro member
    exact absent <|
      (mem_firstOccurrenceSequence_iff initial before).mp member
  have keepSequence :
      (firstOccurrenceSequence before).filter
          (fun tested => decide (tested ≠ initial)) =
        firstOccurrenceSequence before := by
    apply List.filter_eq_self.mpr
    intro tested member
    have different : tested ≠ initial := by
      intro equal
      subst tested
      exact sequenceAbsent member
    simp [different]
  rw [← firstOccurrenceSequence_filter]
  rw [filter_splitProfile_source]
  rw [firstOccurrenceSequence_append_of_subset
    (initial :: after.filter (splitProfile initial before))
    (initial :: before) suffixSubset]
  simp only [firstOccurrenceSequence]
  rw [keepSequence]

private theorem firstOccurrences_filter_not_splitProfile
    (initial : Nat) (before after : List Nat) :
    (firstOccurrenceSequence
        (initial :: before ++ initial :: after)).filter
        (fun tested => !(splitProfile initial before tested)) =
      (firstOccurrenceSequence after).filter
        (unseenNoninitial initial
          (firstOccurrenceSequence before ++ [initial])) := by
  rw [← firstOccurrenceSequence_filter]
  rw [filter_not_splitProfile_source]
  rw [firstOccurrenceSequence_filter]
  rw [not_splitProfile_eq_unseen]

private theorem renderInitialSecondGap_split
    (initial : Nat) (before after : List Nat)
    (absent : initial ∉ before) :
    renderInitialSecondGap
        (firstOccurrenceSequence
          (initial :: before ++ initial :: after))
        true (splitProfile initial before) =
      (initial :: firstOccurrenceSequence before) ++ [initial] ++
        (firstOccurrenceSequence after).filter
          (unseenNoninitial initial
            (firstOccurrenceSequence before ++ [initial])) := by
  have headValue :
      (firstOccurrenceSequence
        (initial :: before ++ initial :: after)).head? = some initial := by
    rfl
  simp only [renderInitialSecondGap, if_true, headValue]
  rw [firstOccurrences_filter_splitProfile initial before after absent,
    firstOccurrences_filter_not_splitProfile]

/-- Deterministic output of the two operational deletion passes. -/
def operationalNormalList (word : Word Nat) : List Nat :=
  word.head ::
    seekSecondInitial word.head
      (noninitialScanOutput word.head [] word.tail)

private theorem operationalNormalList_split
    (initial : Nat) (before after : List Nat)
    (absent : initial ∉ before) :
    operationalNormalList
        (Word.mk initial (before ++ initial :: after)) =
      (initial :: firstOccurrenceSequence before) ++ [initial] ++
        (firstOccurrenceSequence after).filter
          (unseenNoninitial initial
            (firstOccurrenceSequence before ++ [initial])) := by
  have scannedBefore :=
    noninitialScanOutput_eq_firstOccurrenceSequence_of_not_mem
      initial before absent
  have sequenceAbsent :
      initial ∉ firstOccurrenceSequence before := by
    intro member
    exact absent <|
      (mem_firstOccurrenceSequence_iff initial before).mp member
  change
    initial :: seekSecondInitial initial
        (noninitialScanOutput initial []
          (before ++ initial :: after)) = _
  rw [noninitialScanOutput_append initial [] before
    (initial :: after)]
  rw [scannedBefore]
  simp only [noninitialScanOutput, ↓reduceIte]
  rw [noninitialScanOutput_eq_append_delta]
  rw [seekSecondInitial_at_first initial
    (firstOccurrenceSequence before)
    (noninitialScanDelta initial
      (firstOccurrenceSequence before ++ [initial]) after)
    sequenceAbsent]
  rw [deleteLaterInitial_noninitialScanDelta]
  simp [List.append_assoc]

/-- The canonical normal list determined by the exact semantic signature. -/
def canonicalNormalList (word : Word Nat) : List Nat :=
  renderInitialSecondGap
    (firstOccurrenceSequence word.toList)
    (repeatedInitial word)
    (beforeSecondProfile word)

def normalList (word : Word Nat) : List Nat :=
  canonicalNormalList word

/-- The operational two-pass scan computes the canonical signature render. -/
theorem operationalNormalList_eq_canonicalNormalList (word : Word Nat) :
    operationalNormalList word = canonicalNormalList word := by
  cases word with
  | mk initial tail =>
      by_cases repeated : initial ∈ tail
      · let before := prefixBefore initial tail
        let after := tailAfterFirst initial tail
        have tailSplit : tail = before ++ initial :: after := by
          simpa [before, after] using splitAtFirst initial repeated
        have beforeAbsent : initial ∉ before := by
          simpa [before] using not_mem_prefixBefore initial tail
        have repeatedValue :
            repeatedInitial
                (Word.mk initial (before ++ initial :: after)) = true := by
          simp [repeatedInitial]
        have profileValue :
            beforeSecondProfile
                (Word.mk initial (before ++ initial :: after)) =
              splitProfile initial before := by
          funext tested
          simp [beforeSecondProfile, splitProfile,
            prefixBefore_append_selected initial before after beforeAbsent]
        have canonicalValue :
            canonicalNormalList
                (Word.mk initial (before ++ initial :: after)) =
              renderInitialSecondGap
                (firstOccurrenceSequence
                  (initial :: before ++ initial :: after))
                true (splitProfile initial before) := by
          unfold canonicalNormalList
          rw [repeatedValue, profileValue]
          rfl
        calc
          operationalNormalList (Word.mk initial tail) =
              operationalNormalList
                (Word.mk initial (before ++ initial :: after)) := by
            rw [tailSplit]
          _ = (initial :: firstOccurrenceSequence before) ++ [initial] ++
                (firstOccurrenceSequence after).filter
                  (unseenNoninitial initial
                    (firstOccurrenceSequence before ++ [initial])) :=
            operationalNormalList_split initial before after beforeAbsent
          _ = renderInitialSecondGap
                (firstOccurrenceSequence
                  (initial :: before ++ initial :: after))
                true (splitProfile initial before) :=
            (renderInitialSecondGap_split
              initial before after beforeAbsent).symm
          _ = canonicalNormalList
                (Word.mk initial (before ++ initial :: after)) :=
            canonicalValue.symm
          _ = canonicalNormalList (Word.mk initial tail) := by
            rw [tailSplit]
      · have scanned :=
          noninitialScanOutput_eq_firstOccurrenceSequence_of_not_mem
            initial tail repeated
        have sequenceAbsent :
            initial ∉ firstOccurrenceSequence tail := by
          intro member
          exact repeated <|
            (mem_firstOccurrenceSequence_iff initial tail).mp member
        have keepSequence :
            (firstOccurrenceSequence tail).filter
                (fun tested => decide (tested ≠ initial)) =
              firstOccurrenceSequence tail := by
          apply List.filter_eq_self.mpr
          intro tested member
          have different : tested ≠ initial := by
            intro equal
            subst tested
            exact sequenceAbsent member
          simp [different]
        have firstSequence :
            firstOccurrenceSequence (initial :: tail) =
              initial :: firstOccurrenceSequence tail := by
          simp only [firstOccurrenceSequence]
          rw [keepSequence]
        calc
          operationalNormalList (Word.mk initial tail) =
              initial :: seekSecondInitial initial
                (noninitialScanOutput initial [] tail) := rfl
          _ = initial :: firstOccurrenceSequence tail := by
            rw [scanned,
              seekSecondInitial_eq_self_of_not_mem initial sequenceAbsent]
          _ = firstOccurrenceSequence (initial :: tail) :=
            firstSequence.symm
          _ = canonicalNormalList (Word.mk initial tail) := by
            simp [canonicalNormalList, renderInitialSecondGap,
              repeatedInitial, repeated, Word.toList]

theorem operationalNormalList_ne_nil (word : Word Nat) :
    operationalNormalList word ≠ [] := by
  simp [operationalNormalList]

theorem canonicalNormalList_ne_nil (word : Word Nat) :
    canonicalNormalList word ≠ [] := by
  rw [← operationalNormalList_eq_canonicalNormalList]
  exact operationalNormalList_ne_nil word

theorem normalList_ne_nil (word : Word Nat) :
    normalList word ≠ [] := by
  simpa [normalList] using canonicalNormalList_ne_nil word

private theorem listDerivesOperationalNormal (word : Word Nat) :
    ListDerives word.toList (operationalNormalList word) := by
  cases word with
  | mk initial tail =>
      have scanned :=
        listDerivesNoninitialScan initial [] tail
      have scanned' :
          ListDerives
            (initial :: tail)
            (initial :: noninitialScanOutput initial [] tail) := by
        simpa using scanned
      have sought :=
        listDerivesSeekSecondInitial initial []
          (noninitialScanOutput initial [] tail)
      have sought' :
          ListDerives
            (initial :: noninitialScanOutput initial [] tail)
            (initial :: seekSecondInitial initial
              (noninitialScanOutput initial [] tail)) := by
        simpa using sought
      simpa [operationalNormalList] using scanned'.trans sought'

def operationalNormalWord (word : Word Nat) : Word Nat :=
  match operationalNormalList word with
  | [] => Word.singleton word.head
  | head :: tail => wordOfCons head tail

@[simp]
theorem toList_operationalNormalWord (word : Word Nat) :
    (operationalNormalWord word).toList = operationalNormalList word := by
  unfold operationalNormalWord
  cases normalShape : operationalNormalList word with
  | nil =>
      exact False.elim (operationalNormalList_ne_nil word normalShape)
  | cons head tail =>
      rfl

/-- Every word derives to the output of the operational normalizer. -/
theorem derivesOperationalNormal (word : Word Nat) :
    Derives basis word (operationalNormalWord word) := by
  have normalized := listDerivesOperationalNormal word
  rw [← toList_operationalNormalWord word] at normalized
  generalize targetShape : operationalNormalWord word = target at normalized ⊢
  cases word with
  | mk sourceHead sourceTail =>
      cases target with
      | mk targetHead targetTail =>
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord normalized

def normalWord (word : Word Nat) : Word Nat :=
  match normalList word with
  | [] => Word.singleton word.head
  | head :: tail => wordOfCons head tail

@[simp]
theorem toList_normalWord (word : Word Nat) :
    (normalWord word).toList = normalList word := by
  unfold normalWord
  cases normalShape : normalList word with
  | nil =>
      exact False.elim (normalList_ne_nil word normalShape)
  | cons head tail =>
      rfl

theorem operationalNormalWord_eq_normalWord (word : Word Nat) :
    operationalNormalWord word = normalWord word := by
  apply Word.toList_injective
  rw [toList_operationalNormalWord, toList_normalWord,
    operationalNormalList_eq_canonicalNormalList]
  rfl

/-- Every word derives to its canonical signature normal word. -/
theorem derivesNormal (word : Word Nat) :
    Derives basis word (normalWord word) := by
  have normalized := derivesOperationalNormal word
  rw [operationalNormalWord_eq_normalWord] at normalized
  exact normalized

namespace SameInitialSecondGapSignature

theorem canonicalNormalList_eq {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    canonicalNormalList left = canonicalNormalList right := by
  unfold canonicalNormalList
  rw [same.firstOccurrences, same.repeatedInitial, same.beforeSecond]

theorem normalList_eq {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    normalList left = normalList right := by
  simpa [normalList] using same.canonicalNormalList_eq

theorem normalWord_eq {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    normalWord left = normalWord right := by
  apply Word.toList_injective
  simpa using same.normalList_eq

end SameInitialSecondGapSignature

/-- Equal initial-second-gap signatures are derivable through their common
canonical normal word. -/
theorem derives_of_sameInitialSecondGapSignature
    {left right : Word Nat}
    (same : SameInitialSecondGapSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesNormal left
  have rightNormal := derivesNormal right
  rw [same.normalWord_eq] at leftNormal
  exact leftNormal.trans rightNormal.symm

end SemigroupBasis.CoRoots.S5_869
