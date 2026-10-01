import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_855

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩
def xyxz : Word Nat := ⟨0, [1, 0, 2]⟩

def rightDuplicationLaw : Identity Nat := ⟨xy, xyy⟩
def initialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩

/-- The exact S5_855 basis `xy = xyy`, `xxyz = xyxz`. -/
def basis : List (Identity Nat) :=
  [rightDuplicationLaw, initialMoveLaw]

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev wordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private def instantiateThree
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Delete an adjacent repeated nonempty block after a nonempty prefix. -/
theorem derivesRightContraction (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) (u ++ v) := by
  have base :
      Derives basis xyy xy :=
    Derives.symm <|
      Derives.fromBasis (e := rightDuplicationLaw) <|
        List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThree u v v)
  simpa [basis, rightDuplicationLaw, xyy, xy, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Gather a later copy of `u` next to the initial copy while retaining a
nonempty suffix. -/
theorem derivesReturnGather (u v q : Word Nat) :
    Derives basis
      (((u ++ v) ++ u) ++ q)
      (((u ++ u) ++ v) ++ q) := by
  have base :
      Derives basis xyxz xxyz :=
    Derives.symm <|
      Derives.fromBasis (e := initialMoveLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, initialMoveLaw, xyxz, xxyz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Move the second initial block across a nonempty middle and retain the
nonempty suffix. -/
theorem derivesInitialMove (u v q : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ q)
      (((u ++ v) ++ u) ++ q) := by
  have base :
      Derives basis xxyz xyxz :=
    Derives.fromBasis (e := initialMoveLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have substituted :=
    Derives.subst base (instantiateThree u v q)
  simpa [basis, initialMoveLaw, xxyz, xyxz, instantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The derived power law `xx = xxx`, oriented as contraction. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  derivesRightContraction u u

/-- When the final block is also initial, a retained initial double can be
moved to the end and contracted there. -/
theorem derivesRepeatedInitialFinalContraction
    (u middle : Word Nat) :
    Derives basis
      (((u ++ u) ++ middle) ++ u)
      ((u ++ middle) ++ u) := by
  exact Derives.trans
    (derivesInitialMove u middle u)
    (derivesRightContraction (u ++ middle) u)

private def removeLetter
    (selected : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ selected))

private theorem removeLetter_append
    (selected : Nat) (left right : List Nat) :
    removeLetter selected (left ++ right) =
      removeLetter selected left ++
        removeLetter selected right := by
  simp [removeLetter, List.filter_append]

private theorem listDerivesContractSquare
    (pre suffix : List Nat) (letter : Nat)
    (preNonempty : pre ≠ []) :
    ListDerives
      (pre ++ [letter, letter] ++ suffix)
      (pre ++ [letter] ++ suffix) := by
  obtain ⟨prefixHead, prefixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil preNonempty
  have core :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesRightContraction
        (wordOfCons prefixHead prefixTail)
        (Word.singleton letter)
  simpa [wordOfCons, Word.append, Word.singleton,
    List.append_assoc] using core.append suffix

private theorem listDerivesGatherRepeat
    (pre middle suffix : List Nat) (letter : Nat)
    (middleNonempty : middle ≠ [])
    (suffixNonempty : suffix ≠ []) :
    ListDerives
      (pre ++ [letter] ++ middle ++ [letter] ++ suffix)
      (pre ++ [letter, letter] ++ middle ++ suffix) := by
  obtain ⟨middleHead, middleTail, rfl⟩ :=
    List.exists_cons_of_ne_nil middleNonempty
  obtain ⟨suffixHead, suffixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil suffixNonempty
  have core :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesReturnGather
        (Word.singleton letter)
        (wordOfCons middleHead middleTail)
        (wordOfCons suffixHead suffixTail)
  simpa [wordOfCons, Word.append, Word.singleton,
    List.append_assoc] using core.prepend pre

private theorem listDerivesDeleteRepeat
    (pre middle suffix : List Nat) (letter : Nat)
    (preNonempty : pre ≠ [])
    (suffixNonempty : suffix ≠ []) :
    ListDerives
      (pre ++ [letter] ++ middle ++ [letter] ++ suffix)
      (pre ++ [letter] ++ middle ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesContractSquare pre suffix letter preNonempty
  | cons middleHead middleTail =>
      have gathered :=
        listDerivesGatherRepeat
          pre (middleHead :: middleTail) suffix letter
          (by simp) suffixNonempty
      have contracted :=
        listDerivesContractSquare
          pre ((middleHead :: middleTail) ++ suffix)
          letter preNonempty
      apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
        (middle :=
          pre ++ [letter, letter] ++
            (middleHead :: middleTail) ++ suffix)
      · simpa [List.append_assoc] using gathered
      · simpa [List.append_assoc] using contracted

/-- Delete every later occurrence of `letter` from `rest`. The first copy has
a fixed nonempty prefix before it, and the complete rewrite retains a fixed
nonempty suffix. -/
private theorem listDerivesDeleteAfter :
    ∀ (pre : List Nat) (letter : Nat)
      (middle rest suffix : List Nat),
      pre ≠ [] →
      suffix ≠ [] →
      ListDerives
        (pre ++ [letter] ++ middle ++ rest ++ suffix)
        (pre ++ [letter] ++ middle ++
          removeLetter letter rest ++ suffix)
  | pre, letter, middle, [], suffix, _, _ => by
      simpa [removeLetter] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (pre ++ [letter] ++ middle ++ suffix))
  | pre, letter, middle, current :: rest, suffix,
      preNonempty, suffixNonempty => by
      by_cases equal : current = letter
      · subst current
        have deleted :=
          listDerivesDeleteRepeat
            pre middle (rest ++ suffix) letter
            preNonempty (by simp [suffixNonempty])
        have remaining :=
          listDerivesDeleteAfter
            pre letter middle rest suffix
            preNonempty suffixNonempty
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          (middle :=
            pre ++ [letter] ++ middle ++ rest ++ suffix)
        · simpa [List.append_assoc] using deleted
        · simpa [removeLetter, List.append_assoc] using remaining
      · have remaining :=
          listDerivesDeleteAfter
            pre letter (middle ++ [current]) rest suffix
            preNonempty suffixNonempty
        simpa [removeLetter, equal, List.append_assoc] using remaining

/-- Normalize an interior list to first-occurrence order while preserving
fixed nonempty left and right contexts. -/
private theorem listDerivesNormalizeInterior :
    ∀ (pre letters suffix : List Nat),
      pre ≠ [] →
      suffix ≠ [] →
      ListDerives
        (pre ++ letters ++ suffix)
        (pre ++ firstOccurrenceSequence letters ++ suffix)
  | pre, [], suffix, _, _ => by
      simpa [firstOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (pre ++ suffix))
  | pre, letter :: rest, suffix,
      preNonempty, suffixNonempty => by
      have normalizedRest :=
        listDerivesNormalizeInterior
          (pre ++ [letter]) rest suffix
          (by simp [preNonempty]) suffixNonempty
      have deleted :=
        listDerivesDeleteAfter
          pre letter [] (firstOccurrenceSequence rest) suffix
          preNonempty suffixNonempty
      apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
        (middle :=
          pre ++ [letter] ++ firstOccurrenceSequence rest ++ suffix)
      · simpa [List.append_assoc] using normalizedRest
      · simpa [firstOccurrenceSequence, removeLetter,
          List.append_assoc] using deleted

private def initialBlock
    (head final : Nat) (order : List Nat) : List Nat :=
  if head ∈ order ∧ final ≠ head then [head, head] else [head]

private theorem listDerivesContractRepeatedInitialFinal
    (middle : List Nat) (letter : Nat) :
    ListDerives
      ([letter, letter] ++ middle ++ [letter])
      ([letter] ++ middle ++ [letter]) := by
  cases middle with
  | nil =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesPowerContraction (Word.singleton letter)
      simpa [Word.append, Word.singleton, List.append_assoc] using core
  | cons middleHead middleTail =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesRepeatedInitialFinalContraction
            (Word.singleton letter)
            (wordOfCons middleHead middleTail)
      simpa [wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using core

private theorem listDerivesDeleteInitialRepeat
    (before after : List Nat) (letter : Nat) :
    ListDerives
      ([letter] ++ before ++ [letter] ++ after ++ [letter])
      ([letter] ++ before ++ after ++ [letter]) := by
  cases before with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesContractRepeatedInitialFinal after letter
  | cons beforeHead beforeTail =>
      have gathered :=
        listDerivesGatherRepeat
          [] (beforeHead :: beforeTail)
          (after ++ [letter]) letter (by simp) (by simp)
      have contracted :=
        listDerivesContractRepeatedInitialFinal
          ((beforeHead :: beforeTail) ++ after) letter
      apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
        (middle :=
          [letter, letter] ++
            (beforeHead :: beforeTail) ++ after ++ [letter])
      · simpa [List.append_assoc] using gathered
      · simpa [List.append_assoc] using contracted

private theorem listDerivesDeleteInitialAfter
    (letter : Nat) :
    ∀ (before rest : List Nat),
      ListDerives
        ([letter] ++ before ++ rest ++ [letter])
        ([letter] ++ before ++ removeLetter letter rest ++ [letter])
  | before, [] => by
      simpa [removeLetter] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) ([letter] ++ before ++ [letter]))
  | before, current :: rest => by
      by_cases equal : current = letter
      · subst current
        have deleted :=
          listDerivesDeleteInitialRepeat before rest letter
        have remaining :=
          listDerivesDeleteInitialAfter letter before rest
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          (middle := [letter] ++ before ++ rest ++ [letter])
        · simpa [List.append_assoc] using deleted
        · simpa [removeLetter, List.append_assoc] using remaining
      · have remaining :=
          listDerivesDeleteInitialAfter
            letter (before ++ [current]) rest
        simpa [removeLetter, equal, List.append_assoc] using remaining

/-- Retain exactly one witness of a repeated initial letter before the final
position, unless the final letter itself supplies that second witness. -/
private theorem listDerivesHandleInitial
    (head final : Nat) (order : List Nat) :
    ListDerives
      ([head] ++ order ++ [final])
      (initialBlock head final order ++
        removeLetter head order ++ [final]) := by
  by_cases member : head ∈ order
  · obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp member
    by_cases finalHead : final = head
    · subst final
      have deleted :=
        listDerivesDeleteInitialAfter head [] order
      simpa [initialBlock, member, removeLetter,
        List.append_assoc] using deleted
    · cases before with
      | nil =>
          have deleted :=
            listDerivesDeleteAfter
              [head] head [] after [final] (by simp) (by simp)
          simpa [split, initialBlock, member, finalHead,
            removeLetter, List.append_assoc] using deleted
      | cons beforeHead beforeTail =>
          have gathered :=
            listDerivesGatherRepeat
              [] (beforeHead :: beforeTail)
              (after ++ [final]) head (by simp) (by simp)
          have deleted :=
            listDerivesDeleteAfter
              [head] head [] ((beforeHead :: beforeTail) ++ after)
              [final] (by simp) (by simp)
          have removedOrder :
              removeLetter head order =
                removeLetter head
                  ((beforeHead :: beforeTail) ++ after) := by
            calc
              removeLetter head order =
                  removeLetter head
                    ((beforeHead :: beforeTail) ++ head :: after) := by
                rw [split]
              _ = removeLetter head (beforeHead :: beforeTail) ++
                    removeLetter head (head :: after) := by
                rw [removeLetter_append]
              _ = removeLetter head (beforeHead :: beforeTail) ++
                    removeLetter head after := by
                simp [removeLetter]
              _ = removeLetter head
                    ((beforeHead :: beforeTail) ++ after) := by
                rw [removeLetter_append]
          rw [removedOrder]
          apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
            (middle :=
              [head, head] ++ (beforeHead :: beforeTail) ++
                after ++ [final])
          · simpa [split, List.append_assoc] using gathered
          · simpa [split, initialBlock, member, finalHead,
              removeLetter, List.filter_append,
              List.append_assoc] using deleted
  · have removed : removeLetter head order = order := by
      apply List.filter_eq_self.2
      intro letter letterMember
      simp only [decide_eq_true_eq]
      intro equal
      subst letter
      exact member letterMember
    simpa [initialBlock, member, removed] using
      (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis := basis) ([head] ++ order ++ [final]))

/-- Remove the last list entry exactly when it is the designated final
letter. -/
def trimFinal (final : Nat) : List Nat → List Nat
  | [] => []
  | [letter] => if letter = final then [] else [letter]
  | letter :: next :: rest =>
      letter :: trimFinal final (next :: rest)

private theorem trimFinal_eq_self_of_not_mem
    (final : Nat) :
    ∀ letters : List Nat,
      final ∉ letters → trimFinal final letters = letters
  | [], _ => rfl
  | [letter], absent => by
      have different : final ≠ letter := by
        simpa using absent
      have reverse : letter ≠ final := Ne.symm different
      simp [trimFinal, reverse]
  | letter :: next :: rest, absent => by
      have tailAbsent : final ∉ next :: rest := by
        intro member
        exact absent (List.Mem.tail letter member)
      rw [trimFinal,
        trimFinal_eq_self_of_not_mem final (next :: rest) tailAbsent]

private theorem trimFinal_append_same
    (final : Nat) :
    ∀ before : List Nat,
      trimFinal final (before ++ [final]) = before
  | [] => by simp [trimFinal]
  | letter :: rest => by
      cases rest with
      | nil =>
          simp [trimFinal]
      | cons next tail =>
          change
            letter ::
                trimFinal final ((next :: tail) ++ [final]) =
              letter :: next :: tail
          exact congrArg (List.cons letter) <|
            trimFinal_append_same final (next :: tail)

private theorem trimFinal_append_final_of_ne_nil
    (final : Nat) :
    ∀ letters : List Nat,
      letters ≠ [] →
      trimFinal final letters ++ [final] =
        if letters.getLastD final = final then
          letters
        else
          letters ++ [final]
  | [], nonempty => False.elim (nonempty rfl)
  | [letter], _ => by
      by_cases equal : letter = final
      · subst letter
        simp [trimFinal]
      · simp [trimFinal, equal]
  | letter :: next :: rest, _ => by
      have induction :=
        trimFinal_append_final_of_ne_nil
          final (next :: rest) (by simp)
      simp only [List.getLastD_cons] at induction ⊢
      by_cases equal : rest.getLastD next = final
      · rw [if_pos equal] at induction ⊢
        change
          letter ::
              (trimFinal final (next :: rest) ++ [final]) =
            letter :: next :: rest
        exact congrArg (List.cons letter) induction
      · rw [if_neg equal] at induction ⊢
        change
          letter ::
              (trimFinal final (next :: rest) ++ [final]) =
            letter :: ((next :: rest) ++ [final])
        exact congrArg (List.cons letter) induction

private theorem listDerivesTrimFinal
    (pre : List Nat) (preNonempty : pre ≠ [])
    (final : Nat) :
    ∀ order : List Nat,
      ListDerives
        (pre ++ order ++ [final])
        (pre ++ trimFinal final order ++ [final])
  | [] => by
      simpa [trimFinal] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (pre ++ [final]))
  | [letter] => by
      by_cases equal : letter = final
      · subst letter
        simpa [trimFinal] using
          listDerivesContractSquare pre [] final preNonempty
      · simpa [trimFinal, equal] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis) (pre ++ [letter, final]))
  | letter :: next :: rest => by
      have remaining :=
        listDerivesTrimFinal
          (pre ++ [letter]) (by simp [preNonempty])
          final (next :: rest)
      simpa [trimFinal, List.append_assoc] using remaining

def operationalNormalList
    (head : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  let order := firstOccurrenceSequence middle
  let block := initialBlock head final order
  block ++ trimFinal final (removeLetter head order) ++ [final]

/-- Render the exact semantic signature: complete first-occurrence order,
final variable, and whether the initial variable occurs again. -/
def renderInitialFinal
    (sequence : List Nat) (final : Nat) (repeatedInitial : Bool) :
    List Nat :=
  match sequence with
  | [] => []
  | head :: rest =>
      let core :=
        if repeatedInitial && decide (final ≠ head) then
          head :: head :: rest
        else
          head :: rest
      if final = head ∧ repeatedInitial = true ∧ rest = [] then
        core ++ [final]
      else if (head :: rest).getLastD head = final then
        core
      else
        core ++ [final]

def repeatedInitial (word : Word Nat) : Bool :=
  decide (word.head ∈ word.tail)

def normalList (word : Word Nat) : List Nat :=
  renderInitialFinal
    (firstOccurrenceSequence word.toList)
    word.final
    (repeatedInitial word)

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

private theorem renderInitialFinal_ne_nil
    (head : Nat) (rest : List Nat) (final : Nat)
    (repeated : Bool) :
    renderInitialFinal (head :: rest) final repeated ≠ [] := by
  simp only [renderInitialFinal]
  split
  · simp
  · split
    · split <;> simp
    · simp

private theorem firstOccurrenceSequence_cons_eq
    (letter : Nat) (rest : List Nat) :
    firstOccurrenceSequence (letter :: rest) =
      letter :: removeLetter letter
        (firstOccurrenceSequence rest) :=
  rfl

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

private theorem renderInitialFinal_of_ne
    (head final : Nat) (different : final ≠ head)
    (repeated : Bool) (rest : List Nat) :
    renderInitialFinal (head :: rest) final repeated =
      (if repeated then [head, head] else [head]) ++
        trimFinal final rest ++ [final] := by
  cases rest with
  | nil =>
      have reverse : head ≠ final := Ne.symm different
      cases repeated <;>
        simp [renderInitialFinal, trimFinal, different, reverse]
  | cons letter tail =>
      have trimmed :=
        trimFinal_append_final_of_ne_nil
          final (letter :: tail) (by simp)
      have lastIndependent :
          (letter :: tail).getLastD head =
            (letter :: tail).getLastD final := by
        simp only [List.getLastD_cons]
      have lastIndependentOption :
          (letter :: tail).getLast?.getD head =
            (letter :: tail).getLast?.getD final := by
        change
          (letter :: tail).getLastD head =
            (letter :: tail).getLastD final
        exact lastIndependent
      cases repeated <;>
        simp [renderInitialFinal, different, trimmed] <;>
        rw [lastIndependentOption] <;>
        split <;> rfl

private theorem renderInitialFinal_same
    (head : Nat) (rest : List Nat)
    (absent : head ∉ rest) :
    renderInitialFinal (head :: rest) head true =
      [head] ++ rest ++ [head] := by
  cases rest with
  | nil =>
      simp [renderInitialFinal]
  | cons letter tail =>
      have lastMember :
          tail.getLastD letter ∈ letter :: tail :=
        List.getLastD_mem_cons
      have lastDifferent :
          tail.getLastD letter ≠ head := by
        intro equal
        have member : head ∈ letter :: tail := by
          rw [← equal]
          exact lastMember
        exact absent member
      have lastValue :
          (letter :: tail).getLastD head =
            tail.getLastD letter := by
        simp only [List.getLastD_cons]
      have notFinal :
          ¬(letter :: tail).getLastD head = head := by
        rw [lastValue]
        exact lastDifferent
      have notFinalOption :
          ¬(letter :: tail).getLast?.getD head = head := by
        change ¬(letter :: tail).getLastD head = head
        exact notFinal
      simp [renderInitialFinal, notFinalOption]

private theorem operationalNormalList_eq_render
    (head : Nat) (middle : List Nat) (final : Nat) :
    operationalNormalList head middle final =
      renderInitialFinal
        (firstOccurrenceSequence (head :: middle ++ [final]))
        final
        (decide (head ∈ middle ∨ final = head)) := by
  by_cases finalHead : final = head
  · subst final
    have sequenceShape :
        firstOccurrenceSequence (head :: middle ++ [head]) =
          head :: removeLetter head
            (firstOccurrenceSequence middle) := by
      rw [List.cons_append,
        firstOccurrenceSequence_cons_eq,
        firstOccurrenceSequence_append_final]
      by_cases member : head ∈ middle
      · rw [if_pos member]
      · rw [if_neg member, removeLetter_append]
        simp [removeLetter]
    have restAbsent :
        head ∉ removeLetter head
          (firstOccurrenceSequence middle) := by
      simp [removeLetter]
    have restTrimmed :
        trimFinal head
            (removeLetter head
              (firstOccurrenceSequence middle)) =
          removeLetter head
            (firstOccurrenceSequence middle) :=
      trimFinal_eq_self_of_not_mem head _ restAbsent
    rw [sequenceShape]
    simp only [or_true, decide_true]
    rw [renderInitialFinal_same head _ restAbsent]
    simp [operationalNormalList, initialBlock,
      restTrimmed]
  · by_cases finalMember : final ∈ middle
    · have sequenceShape :
          firstOccurrenceSequence (head :: middle ++ [final]) =
            head :: removeLetter head
              (firstOccurrenceSequence middle) := by
        rw [List.cons_append,
          firstOccurrenceSequence_cons_eq,
          firstOccurrenceSequence_append_final,
          if_pos finalMember]
      rw [sequenceShape,
        renderInitialFinal_of_ne head final finalHead]
      by_cases headMember : head ∈ middle
      · have orderMember :
            head ∈ firstOccurrenceSequence middle :=
          (mem_firstOccurrenceSequence_iff head middle).2 headMember
        simp [operationalNormalList, initialBlock,
          finalHead, headMember, orderMember]
      · have orderAbsent :
            head ∉ firstOccurrenceSequence middle := by
          simpa [mem_firstOccurrenceSequence_iff] using headMember
        simp [operationalNormalList, initialBlock,
          finalHead, headMember, orderAbsent]
    · have sequenceShape :
          firstOccurrenceSequence (head :: middle ++ [final]) =
            head ::
              (removeLetter head
                (firstOccurrenceSequence middle) ++ [final]) := by
        rw [List.cons_append,
          firstOccurrenceSequence_cons_eq,
          firstOccurrenceSequence_append_final,
          if_neg finalMember, removeLetter_append]
        have reverse : final ≠ head := finalHead
        simp [removeLetter, reverse]
      have orderFinalAbsent :
          final ∉ firstOccurrenceSequence middle := by
        simpa [mem_firstOccurrenceSequence_iff] using finalMember
      have restFinalAbsent :
          final ∉ removeLetter head
            (firstOccurrenceSequence middle) := by
        intro member
        exact orderFinalAbsent (List.mem_filter.mp member).1
      have restTrimmed :
          trimFinal final
              (removeLetter head
                (firstOccurrenceSequence middle)) =
            removeLetter head
              (firstOccurrenceSequence middle) :=
        trimFinal_eq_self_of_not_mem final _ restFinalAbsent
      rw [sequenceShape,
        renderInitialFinal_of_ne head final finalHead,
        trimFinal_append_same]
      by_cases headMember : head ∈ middle
      · have orderMember :
            head ∈ firstOccurrenceSequence middle :=
          (mem_firstOccurrenceSequence_iff head middle).2 headMember
        simp [operationalNormalList, initialBlock,
          finalHead, headMember, orderMember, restTrimmed]
      · have orderAbsent :
            head ∉ firstOccurrenceSequence middle := by
          simpa [mem_firstOccurrenceSequence_iff] using headMember
        simp [operationalNormalList, initialBlock,
          finalHead, headMember, orderAbsent, restTrimmed]

theorem normalList_ne_nil (word : Word Nat) :
    normalList word ≠ [] := by
  cases word with
  | mk head tail =>
      simp only [normalList, Word.toList,
        firstOccurrenceSequence]
      exact renderInitialFinal_ne_nil head _ _ _

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

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem final_wordOfPrefixFinal
    (pre : List Nat) (final : Nat) :
    (wordOfPrefixFinal pre final).final = final := by
  induction pre with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

/-- Every word derives to the deterministic initial/final normal form. -/
theorem listDerivesNormal (word : Word Nat) :
    ListDerives word.toList (normalList word) := by
  generalize splitShape : splitPrefixFinal word = split
  rcases split with ⟨pre, final⟩
  have sourceShape :
      word.toList = pre ++ [final] := by
    have result := toList_eq_splitPrefixFinal word
    rw [splitShape] at result
    exact result
  cases pre with
  | nil =>
      have wordShape : word = Word.singleton final := by
        apply Word.toList_injective
        simp [sourceShape]
      subst word
      have singletonNormal :
          normalList (Word.singleton final) = [final] := by
        simp [normalList, renderInitialFinal, repeatedInitial,
          firstOccurrenceSequence, Word.toList, Word.final,
          Word.singleton]
      rw [singletonNormal]
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) [final])
  | cons head middle =>
      have normalizedInterior :=
        listDerivesNormalizeInterior
          [head] middle [final] (by simp) (by simp)
      have handledInitial :=
        listDerivesHandleInitial
          head final (firstOccurrenceSequence middle)
      have trimmedFinal :=
        listDerivesTrimFinal
          (initialBlock head final
            (firstOccurrenceSequence middle))
          (by
            simp only [initialBlock]
            split <;> simp)
          final
          (removeLetter head (firstOccurrenceSequence middle))
      have operational :
          ListDerives
            (head :: middle ++ [final])
            (operationalNormalList head middle final) := by
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          (middle :=
            [head] ++ firstOccurrenceSequence middle ++ [final])
        · simpa [List.append_assoc] using normalizedInterior
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          (middle :=
            initialBlock head final
                (firstOccurrenceSequence middle) ++
              removeLetter head
                (firstOccurrenceSequence middle) ++ [final])
        · exact handledInitial
        · simpa [operationalNormalList, List.append_assoc] using
            trimmedFinal
      have finalValue : word.final = final := by
        have finalCongruence :=
          congrArg Word.final (wordOfPrefixFinal_split word)
        rw [splitShape] at finalCongruence
        rw [final_wordOfPrefixFinal] at finalCongruence
        exact finalCongruence.symm
      have headValue : word.head = head := by
        cases word with
        | mk wordHead wordTail =>
            simp only [Word.toList] at sourceShape ⊢
            exact (List.cons.inj sourceShape).1
      have tailRepeated :
          repeatedInitial word =
            decide (head ∈ middle ∨ final = head) := by
        cases word with
        | mk wordHead wordTail =>
            simp only [Word.toList] at sourceShape
            have listEquality :
                wordHead :: wordTail =
                  head :: middle ++ [final] := sourceShape
            have heads : wordHead = head :=
              (List.cons.inj listEquality).1
            subst wordHead
            have tails :
                wordTail = middle ++ [final] :=
              (List.cons.inj listEquality).2
            subst wordTail
            simp [repeatedInitial, eq_comm]
      rw [sourceShape]
      rw [operationalNormalList_eq_render] at operational
      simpa [normalList, finalValue, headValue, tailRepeated,
        sourceShape] using operational

theorem derivesNormal (word : Word Nat) :
    Derives basis word (normalWord word) := by
  have normalized := listDerivesNormal word
  rw [← toList_normalWord word] at normalized
  generalize targetShape : normalWord word = target at normalized ⊢
  cases word with
  | mk sourceHead sourceTail =>
      cases target with
      | mk targetHead targetTail =>
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord normalized

structure SameInitialFinalSignature
    (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  final : left.final = right.final
  repeatedInitial :
    S5_855.repeatedInitial left =
      S5_855.repeatedInitial right

namespace SameInitialFinalSignature

theorem head_eq {left right : Word Nat}
    (same : SameInitialFinalSignature left right) :
    left.head = right.head := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have first := same.firstOccurrences
          simp only [Word.toList, firstOccurrenceSequence,
            List.cons.injEq] at first
          exact first.1

theorem normalList_eq {left right : Word Nat}
    (same : SameInitialFinalSignature left right) :
    normalList left = normalList right := by
  unfold normalList
  rw [same.firstOccurrences, same.final, same.repeatedInitial]

theorem normalWord_eq {left right : Word Nat}
    (same : SameInitialFinalSignature left right) :
    normalWord left = normalWord right := by
  apply Word.toList_injective
  simpa using same.normalList_eq

end SameInitialFinalSignature

/-- Syntactic completeness from equality of the exact three-coordinate
signature. -/
theorem derivesOfSignature
    {left right : Word Nat}
    (same : SameInitialFinalSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesNormal left
  have rightNormal := derivesNormal right
  rw [same.normalWord_eq] at leftNormal
  exact leftNormal.trans rightNormal.symm

/-- Generic exact-basis bridge for the S5_855 normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        SameInitialFinalSignature identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derivesOfSignature (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_855
