import SemigroupBasis.CoRoots.Order6SporadicSection12
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_345Normalization

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

namespace A2Normalization

private abbrev ListDerives :=
  S5_107.ListDerives a2Basis

private def instantiateFiveWords
    (x y z h k : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => h
  | 4 => k
  | n + 5 => Word.singleton (n + 5)

private theorem basisPowerContract :
    Derives a2Basis word_12_1a_left word_12_1a_right :=
  Derives.fromBasis (e := law_12_1a) <| by
    simp [a2Basis]

private theorem basisInitialGather :
    Derives a2Basis word_12_1b_left word_12_1b_right :=
  Derives.fromBasis (e := law_12_1b) <| by
    simp [a2Basis]

private theorem basisTerminalSwitchEmpty :
    Derives a2Basis
      (Word.mk 0 [0, 1, 1, 0])
      (Word.mk 0 [0, 1, 1, 1]) :=
  Derives.fromBasis (e := law_12_1c_empty) <| by
    simp [a2Basis]

private theorem basisTerminalSwitchH :
    Derives a2Basis
      (Word.mk 0 [0, 3, 1, 1, 0])
      (Word.mk 0 [0, 3, 1, 1, 1]) :=
  Derives.fromBasis (e := law_12_1c_H) <| by
    simp [a2Basis]

private theorem basisTerminalSwitchK :
    Derives a2Basis
      (Word.mk 0 [0, 1, 1, 4, 0])
      (Word.mk 0 [0, 1, 1, 4, 1]) :=
  Derives.fromBasis (e := law_12_1c_K) <| by
    simp [a2Basis]

private theorem basisTerminalSwitchHK :
    Derives a2Basis
      (Word.mk 0 [0, 3, 1, 1, 4, 0])
      (Word.mk 0 [0, 3, 1, 1, 4, 1]) :=
  Derives.fromBasis (e := law_12_1c_HK) <| by
    simp [a2Basis]

/-- The first A2 law contracts a leading cube whenever a nonempty suffix is
retained. -/
theorem derivesPowerContract (x suffix : Word Nat) :
    Derives a2Basis
      (((x ++ x) ++ x) ++ suffix)
      ((x ++ x) ++ suffix) := by
  have substituted :=
    Derives.subst basisPowerContract
      (instantiateFiveWords x suffix suffix suffix suffix)
  change Derives a2Basis
    (((x ++ x) ++ x) ++ suffix)
    ((x ++ x) ++ suffix) at substituted
  exact substituted

/-- The second A2 law gathers a repeated block at its first occurrence while
retaining a nonempty block on the right. -/
theorem derivesInitialGather (x middle suffix : Word Nat) :
    Derives a2Basis
      (((x ++ middle) ++ x) ++ suffix)
      (((x ++ x) ++ middle) ++ suffix) := by
  have substituted :=
    Derives.subst basisInitialGather
      (instantiateFiveWords x middle suffix middle suffix)
  change Derives a2Basis
    (((x ++ middle) ++ x) ++ suffix)
    (((x ++ x) ++ middle) ++ suffix) at substituted
  exact substituted

theorem derivesTerminalSwitchEmpty (x y : Word Nat) :
    Derives a2Basis
      (((x ++ x) ++ (y ++ y)) ++ x)
      (((x ++ x) ++ (y ++ y)) ++ y) := by
  have substituted :=
    Derives.subst basisTerminalSwitchEmpty
      (instantiateFiveWords x y y x y)
  simpa [word_12_1c_empty_left, word_12_1c_empty_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalSwitchH
    (x y left : Word Nat) :
    Derives a2Basis
      ((((x ++ x) ++ left) ++ (y ++ y)) ++ x)
      ((((x ++ x) ++ left) ++ (y ++ y)) ++ y) := by
  have substituted :=
    Derives.subst basisTerminalSwitchH
      (instantiateFiveWords x y y left y)
  simpa [word_12_1c_H_left, word_12_1c_H_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalSwitchK
    (x y right : Word Nat) :
    Derives a2Basis
      ((((x ++ x) ++ (y ++ y)) ++ right) ++ x)
      ((((x ++ x) ++ (y ++ y)) ++ right) ++ y) := by
  have substituted :=
    Derives.subst basisTerminalSwitchK
      (instantiateFiveWords x y y x right)
  simpa [word_12_1c_K_left, word_12_1c_K_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalSwitchHK
    (x y left right : Word Nat) :
    Derives a2Basis
      (((((x ++ x) ++ left) ++ (y ++ y)) ++ right) ++ x)
      (((((x ++ x) ++ left) ++ (y ++ y)) ++ right) ++ y) := by
  have substituted :=
    Derives.subst basisTerminalSwitchHK
      (instantiateFiveWords x y y left right)
  simpa [word_12_1c_HK_left, word_12_1c_HK_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- All four ordinary expansions of (12.1c) combine into one contextual
list rewrite. The middle contexts may independently be empty. -/
theorem listDerivesTerminalSwitch
    (pre suffix : List Nat) (x y : Nat)
    (left right : List Nat) :
    ListDerives
      (pre ++ [x, x] ++ left ++ [y, y] ++ right ++ [x] ++ suffix)
      (pre ++ [x, x] ++ left ++ [y, y] ++ right ++ [y] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesTerminalSwitchEmpty
              (Word.singleton x) (Word.singleton y)
          simpa [List.append_assoc, Word.append, Word.singleton] using
            core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesTerminalSwitchK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesTerminalSwitchH
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesTerminalSwitchHK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix

/-- Contextual three-to-two contraction. The explicit nonempty suffix is the
semigroup substitute for the variable `y` in (12.1a). -/
theorem listDerivesPowerContract
    (pre suffix : List Nat) (x : Nat)
    (suffixNonempty : suffix ≠ []) :
    ListDerives
      (pre ++ [x, x, x] ++ suffix)
      (pre ++ [x, x] ++ suffix) := by
  obtain ⟨suffixHead, suffixTail, rfl⟩ :=
    List.exists_cons_of_ne_nil suffixNonempty
  have core := S5_107.ListDerives.ofWord <|
    derivesPowerContract
      (Word.singleton x)
      (S5_107.listWordOfCons suffixHead suffixTail)
  simpa [S5_107.listWordOfCons, List.append_assoc,
    Word.append, Word.singleton] using core.prepend pre

/-- Gather a later `x` into a leading square while a nonempty suffix remains.
An empty middle is already in the requested form. -/
theorem listDerivesGatherNonfinal
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    ListDerives
      (pre ++ [x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := a2Basis) (pre ++ [x, x] ++ after ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨afterHead, afterTail, rfl⟩ :=
        List.exists_cons_of_ne_nil afterNonempty
      have core := S5_107.ListDerives.ofWord <|
        derivesInitialGather
          (Word.singleton x)
          (S5_107.listWordOfCons middleHead middleTail)
          (S5_107.listWordOfCons afterHead afterTail)
      simpa [S5_107.listWordOfCons, List.append_assoc,
        Word.append, Word.singleton] using core.context pre suffix

/-- Once the first two copies have been gathered, a later prefix copy can be
deleted by one gather step followed by (12.1a). -/
theorem listDerivesAbsorbAfterSquare
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    ListDerives
      (pre ++ [x, x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  have gathered :=
    listDerivesGatherNonfinal
      pre suffix x (x :: middle) after afterNonempty
  have contracted :=
    listDerivesPowerContract
      pre (middle ++ after ++ suffix) x (by simp [afterNonempty])
  have gatheredStep :
      ListDerives
        (pre ++ [x, x] ++ middle ++ [x] ++ after ++ suffix)
        (pre ++ [x, x, x] ++ middle ++ after ++ suffix) := by
    simpa [List.append_assoc] using gathered
  have contractedStep :
      ListDerives
        (pre ++ [x, x, x] ++ middle ++ after ++ suffix)
        (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
    simpa [List.append_assoc] using contracted
  exact gatheredStep.trans contractedStep

/-- Remove every selected occurrence after a leading square while retaining
the fixed nonempty suffix. -/
theorem listDerivesAbsorbAllAfterSquare
    (x : Nat) :
    forall (pre rest suffix : List Nat), suffix ≠ [] ->
      ListDerives
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
            [] [] x pre (rest ++ suffix) (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare x pre rest suffix suffixNonempty
        have firstStep :
            ListDerives
              ([x, x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have remaining :=
          listDerivesAbsorbAllAfterSquare
            x (pre ++ [letter]) rest suffix suffixNonempty
        simpa [equal, List.append_assoc] using remaining

/-- Gather the first later selected occurrence and delete all further ones.
This is the cap-two step used by the first-occurrence block recursion. -/
theorem listDerivesGatherAndDelete
    (x : Nat) :
    forall (pre rest suffix : List Nat), suffix ≠ [] -> x ∈ rest ->
      ListDerives
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
            [] [] x pre (rest ++ suffix) (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare
            x pre rest suffix suffixNonempty
        have firstStep :
            ListDerives
              ([x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have restMember : x ∈ rest := by
          simpa [equal, Ne.symm equal] using member
        have remaining :=
          listDerivesGatherAndDelete
            x (pre ++ [letter]) rest suffix suffixNonempty restMember
        simpa [equal, List.append_assoc] using remaining

/-- Normalize a prefix into first-occurrence single/double blocks. The final
letter supplies the nonempty right context required by both A2 rewrite laws. -/
theorem listDerivesDoubleCanonicalBeforeFinal
    (final : Nat) :
    forall letters : List Nat,
      ListDerives
        (letters ++ [final])
        (S5_345.doubleCanonicalList letters ++ [final])
  | [] =>
      S5_107.ListDerives.refl _
  | letter :: rest => by
      let reduced := S5_345.doubleCanonicalList rest
      have first :=
        (listDerivesDoubleCanonicalBeforeFinal final rest).prepend [letter]
      by_cases member : letter ∈ reduced
      · have gathered :=
          listDerivesGatherAndDelete
            letter [] reduced [final] (by simp) member
        exact first.trans <| by
          simpa [S5_345.doubleCanonicalList, reduced, member,
            List.append_assoc] using gathered
      · simpa [S5_345.doubleCanonicalList, reduced, member,
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

/-- The canonical block list before enforcing condition (II) of (12.2).
It already handles one-letter words: powers are capped at three because the
last copy is kept outside the cap-two prefix. -/
def precanonicalList : List Nat -> List Nat
  | [] => []
  | head :: tail =>
      let letters := head :: tail
      let final := tail.getLastD head
      S5_345.doubleCanonicalList letters.dropLast ++ [final]

/-- Every nonempty list derives to the first-occurrence cap-two prefix form. -/
theorem listDerivesPrecanonical :
    forall letters : List Nat,
      ListDerives letters (precanonicalList letters)
  | [] => S5_107.ListDerives.empty
  | head :: tail => by
      let letters := head :: tail
      let final := tail.getLastD head
      let beforeFinal := letters.dropLast
      have normalized :=
        listDerivesDoubleCanonicalBeforeFinal final beforeFinal
      have reconstruction : beforeFinal ++ [final] = letters := by
        simpa [beforeFinal, final, letters] using
          dropLast_append_final head tail
      rw [reconstruction] at normalized
      simpa [precanonicalList, letters, final, beforeFinal] using normalized

/-- Prefix multiplicity truncated at two. This is the exponent attached to a
first-occurrence block in (12.2). -/
def prefixMultiplicity (stem : List Nat) (letter : Nat) : Nat :=
  Nat.min 2 (stem.count letter)

theorem prefixMultiplicity_eq_two_iff
    (stem : List Nat) (letter : Nat) :
    prefixMultiplicity stem letter = 2 ↔
      2 ≤ stem.count letter := by
  unfold prefixMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-- If the old terminal has prefix exponent two, choose the earliest
prefix-double block. Otherwise retain the old terminal. This is exactly the
deterministic repair of condition (II) in (12.2). -/
def terminalOwner (stem : List Nat) (final : Nat) : Nat :=
  if prefixMultiplicity stem final = 2 then
    (S5_345.firstMultiple
      (prefixMultiplicity stem)
      (firstOccurrenceSequence stem)).getD final
  else
    final

def repairedList (stem : List Nat) (final : Nat) : List Nat :=
  S5_345.doubleCanonicalList stem ++
    [terminalOwner stem final]

/-- The cap-two prefix form derives to its condition-(II) repair. If an
earlier doubled block exists, (12.1c) is used in reverse to move terminal
ownership from the old final to the earliest such block. -/
theorem listDerivesRepair
    (stem : List Nat) (final : Nat) :
    ListDerives
      (S5_345.doubleCanonicalList stem ++ [final])
      (repairedList stem final) := by
  by_cases finalDouble : prefixMultiplicity stem final = 2
  · have finalMember : final ∈ stem := by
      apply List.count_pos_iff.mp
      have :=
        (prefixMultiplicity_eq_two_iff stem final).1 finalDouble
      omega
    have finalLabel : final ∈ firstOccurrenceSequence stem :=
      (S5_345.mem_firstOccurrenceSequence_iff final stem).2
        finalMember
    obtain
        ⟨marker, before, markerTail, firstShape, labelsShape,
          beforeNonmultiple, markerDouble⟩ :=
      S5_345.firstMultiple_split_of_exists
        (prefixMultiplicity stem)
        (firstOccurrenceSequence stem)
        ⟨final, finalLabel, finalDouble⟩
    have ownerShape : terminalOwner stem final = marker := by
      simp [terminalOwner, finalDouble, firstShape]
    by_cases markerFinal : marker = final
    · have ownerFinal : terminalOwner stem final = final :=
        ownerShape.trans markerFinal
      have formsEqual :
          repairedList stem final =
            S5_345.doubleCanonicalList stem ++ [final] := by
        simp [repairedList, ownerFinal]
      rw [formsEqual]
      exact S5_107.ListDerives.refl _
    · have finalInTail : final ∈ markerTail := by
        rw [labelsShape] at finalLabel
        rcases List.mem_append.mp finalLabel with
          finalBefore | finalAtOrAfter
        · exact False.elim <|
            (beforeNonmultiple final finalBefore) finalDouble
        · rcases List.mem_cons.mp finalAtOrAfter with
            finalIsMarker | finalTail
          · exact False.elim (markerFinal finalIsMarker.symm)
          · exact finalTail
      obtain ⟨finalSplit, finalSplitShape⟩ :=
        S5_345.splitFirst_some_of_mem final finalInTail
      have tailShape :
          markerTail =
            finalSplit.before ++ final :: finalSplit.after :=
        S5_345.splitFirst_reconstruction
          final markerTail finalSplit finalSplitShape
      have markerCount : 2 ≤ stem.count marker :=
        (prefixMultiplicity_eq_two_iff stem marker).1 markerDouble
      have finalCount : 2 ≤ stem.count final :=
        (prefixMultiplicity_eq_two_iff stem final).1 finalDouble
      have markerBlock :
          S5_345.saturatedBlock stem marker = [marker, marker] := by
        simp [S5_345.saturatedBlock, show stem.count marker ≠ 1 by omega]
      have finalBlock :
          S5_345.saturatedBlock stem final = [final, final] := by
        simp [S5_345.saturatedBlock, show stem.count final ≠ 1 by omega]
      have renderedShape :
          S5_345.doubleCanonicalList stem =
            before.flatMap (S5_345.saturatedBlock stem) ++
              [marker, marker] ++
              finalSplit.before.flatMap
                (S5_345.saturatedBlock stem) ++
              [final, final] ++
              finalSplit.after.flatMap
                (S5_345.saturatedBlock stem) := by
        rw [S5_345.doubleCanonicalList_eq_saturatedCanonicalList]
        unfold S5_345.saturatedCanonicalList
        rw [labelsShape, tailShape]
        simp only [List.flatMap_append, List.flatMap_cons]
        rw [markerBlock, finalBlock]
        simp [List.append_assoc]
      have sourceShape :
          S5_345.doubleCanonicalList stem ++ [final] =
            before.flatMap (S5_345.saturatedBlock stem) ++
              [marker, marker] ++
              finalSplit.before.flatMap
                (S5_345.saturatedBlock stem) ++
              [final, final] ++
              finalSplit.after.flatMap
                (S5_345.saturatedBlock stem) ++ [final] := by
        rw [renderedShape]
      have targetShape :
          repairedList stem final =
            before.flatMap (S5_345.saturatedBlock stem) ++
              [marker, marker] ++
              finalSplit.before.flatMap
                (S5_345.saturatedBlock stem) ++
              [final, final] ++
              finalSplit.after.flatMap
                (S5_345.saturatedBlock stem) ++ [marker] := by
        simp [repairedList, ownerShape, renderedShape]
      rw [sourceShape, targetShape]
      simpa [List.append_assoc] using
        (listDerivesTerminalSwitch
          (before.flatMap (S5_345.saturatedBlock stem)) []
          marker final
          (finalSplit.before.flatMap
            (S5_345.saturatedBlock stem))
          (finalSplit.after.flatMap
            (S5_345.saturatedBlock stem))).symm
  · have ownerShape : terminalOwner stem final = final := by
      simp [terminalOwner, finalDouble]
    have formsEqual :
        repairedList stem final =
          S5_345.doubleCanonicalList stem ++ [final] := by
      simp [repairedList, ownerShape]
    rw [formsEqual]
    exact S5_107.ListDerives.refl _

/-- The deterministic A2 canonical list, including one-letter powers and the
condition-(II) terminal repair. -/
def canonicalList : List Nat -> List Nat
  | [] => []
  | head :: tail =>
      let letters := head :: tail
      let final := tail.getLastD head
      repairedList letters.dropLast final

theorem listDerivesCanonical :
    forall letters : List Nat,
      ListDerives letters (canonicalList letters)
  | [] => S5_107.ListDerives.empty
  | head :: tail => by
      let letters := head :: tail
      let final := tail.getLastD head
      let beforeFinal := letters.dropLast
      have first := listDerivesPrecanonical letters
      have second := listDerivesRepair beforeFinal final
      have precanonicalShape :
          precanonicalList letters =
            S5_345.doubleCanonicalList beforeFinal ++ [final] := by
        simp [precanonicalList, letters, final, beforeFinal]
      have canonicalShape :
          canonicalList letters = repairedList beforeFinal final := by
        simp [canonicalList, letters, final, beforeFinal]
      rw [precanonicalShape] at first
      rw [canonicalShape]
      exact first.trans second

private def wordOfListOr
    (fallback : Nat) : List Nat -> Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

def precanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (precanonicalList word.toList)

def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (canonicalList word.toList)

theorem toList_canonicalWord (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word.toList := by
  have nonempty : canonicalList word.toList ≠ [] := by
    cases word with
    | mk head tail =>
        exact S5_107.ListDerives.target_ne_nil
          (listDerivesCanonical (head :: tail))
  unfold canonicalWord
  cases shape : canonicalList word.toList with
  | nil => exact False.elim (nonempty shape)
  | cons head tail => rfl

/-- Word-level normalization to the cap-two prefix form. The subsequent A2
condition-(II) repair changes only the terminal owner. -/
theorem derivesPrecanonical (word : Word Nat) :
    Derives a2Basis word (precanonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesPrecanonical (Word.mk head tail).toList
      obtain ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            precanonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        unfold precanonicalWord
        rw [targetListEq]
        rfl
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

/-- Every word derives to the deterministic A2 canonical representative. -/
theorem derivesCanonical (word : Word Nat) :
    Derives a2Basis word (canonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesCanonical (Word.mk head tail).toList
      obtain ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            canonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        unfold canonicalWord
        rw [targetListEq]
        rfl
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

/-- Being one of the deterministic representatives produced by
`canonicalWord`. This image predicate avoids requiring an idempotence theorem
in the generic `UnrestrictedCanonicalProof` interface. -/
def Canonical (word : Word Nat) : Prop :=
  ∃ source, word = canonicalWord source

theorem normalize (word : Word Nat) :
    ∃ target, Canonical target ∧ Derives a2Basis word target :=
  ⟨canonicalWord word, ⟨word, rfl⟩, derivesCanonical word⟩

/-- Once semantic uniqueness of the deterministic representatives is
supplied, the completed normalization fills the generic A2 proof package. -/
def unrestrictedCanonicalProofOfUnique
    (unique :
      ∀ left right,
        Canonical left -> Canonical right ->
        (Identity.mk left right).SatisfiedBy S6_5597.table.semigroup ->
        left = right) :
    UnrestrictedCanonicalProof S6_5597.table a2Basis where
  canonical := Canonical
  normalize := normalize
  uniqueOfValid := unique

end A2Normalization

end SemigroupBasis.CoRoots.Order6SporadicSection12
