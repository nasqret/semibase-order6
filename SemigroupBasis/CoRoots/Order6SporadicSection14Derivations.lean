import SemigroupBasis.CoRoots.Order6SporadicSection14
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

private def instantiateFiveWords
    (x y h k fallback : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => fallback
  | 3 => h
  | 4 => k
  | n + 5 => Word.singleton (n + 5)

/-- Retain only the final letter of a list. -/
def keepLast : List Nat → List Nat
  | [] => []
  | [letter] => [letter]
  | _ :: second :: rest => keepLast (second :: rest)
termination_by letters => letters.length

namespace Generic

/-- The four ordinary placements of `x H y K x y ≈ x H y K y`, with
arbitrary outer context. -/
theorem listDerivesDropCDisplayed
    {basisSet : List (Identity Nat)}
    (deriveEmpty : ∀ x y : Word Nat,
      Derives basisSet (((x ++ y) ++ x) ++ y) ((x ++ y) ++ y))
    (deriveH : ∀ x y h : Word Nat,
      Derives basisSet
        ((((x ++ h) ++ y) ++ x) ++ y)
        (((x ++ h) ++ y) ++ y))
    (deriveK : ∀ x y k : Word Nat,
      Derives basisSet
        ((((x ++ y) ++ k) ++ x) ++ y)
        (((x ++ y) ++ k) ++ y))
    (deriveHK : ∀ x y h k : Word Nat,
      Derives basisSet
        (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
        ((((x ++ h) ++ y) ++ k) ++ y))
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    S5_107.ListDerives basisSet
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord
            (deriveEmpty (Word.singleton first) (Word.singleton second))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons gapHead gapTail =>
          have base := S5_107.ListDerives.ofWord
            (deriveK (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
  | cons gapHead gapTail =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord
            (deriveH (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons secondHead secondTail =>
          have base := S5_107.ListDerives.ofWord
            (deriveHK (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail)
              (listWordOfCons secondHead secondTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base

/-- The four ordinary placements of `x H y K y x ≈ x H y K x`, with
arbitrary outer context. -/
theorem listDerivesDropDDisplayed
    {basisSet : List (Identity Nat)}
    (deriveEmpty : ∀ x y : Word Nat,
      Derives basisSet (((x ++ y) ++ y) ++ x) ((x ++ y) ++ x))
    (deriveH : ∀ x y h : Word Nat,
      Derives basisSet
        ((((x ++ h) ++ y) ++ y) ++ x)
        (((x ++ h) ++ y) ++ x))
    (deriveK : ∀ x y k : Word Nat,
      Derives basisSet
        ((((x ++ y) ++ k) ++ y) ++ x)
        (((x ++ y) ++ k) ++ x))
    (deriveHK : ∀ x y h k : Word Nat,
      Derives basisSet
        (((((x ++ h) ++ y) ++ k) ++ y) ++ x)
        ((((x ++ h) ++ y) ++ k) ++ x))
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    S5_107.ListDerives basisSet
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord
            (deriveEmpty (Word.singleton first) (Word.singleton second))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons gapHead gapTail =>
          have base := S5_107.ListDerives.ofWord
            (deriveK (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
  | cons gapHead gapTail =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord
            (deriveH (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons secondHead secondTail =>
          have base := S5_107.ListDerives.ofWord
            (deriveHK (Word.singleton first) (Word.singleton second)
              (listWordOfCons gapHead gapTail)
              (listWordOfCons secondHead secondTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
              S5_107.ListDerives.context before after base

/-- Delete the first of two adjacent later occurrences. The equal-letter case
uses contraction; the unequal case chooses (14.1c)/(14.3c) or
(14.1d)/(14.3d) according to first-occurrence order in the prefix. -/
theorem listDerivesDropFirstAfterSeen
    {basisSet : List (Identity Nat)}
    (contract : ∀ (stem suffix : List Nat) (letter : Nat),
      letter ∈ stem →
      S5_107.ListDerives basisSet
        (stem ++ [letter, letter] ++ suffix)
        (stem ++ [letter] ++ suffix))
    (dropC : ∀ (first second : Nat)
      (before firstGap secondGap after : List Nat),
      S5_107.ListDerives basisSet
        (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
          [first, second] ++ after)
        (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
          [second] ++ after))
    (dropD : ∀ (first second : Nat)
      (before firstGap secondGap after : List Nat),
      S5_107.ListDerives basisSet
        (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
          [second, first] ++ after)
        (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
          [first] ++ after))
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    S5_107.ListDerives basisSet
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact contract stem suffix left leftSeen
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit :
        right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        dropD right left before middle leftAfter suffix
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        dropC left right leftBefore middle tail suffix

/-- Reduce an arbitrary later-occurrence block to its final letter. -/
theorem listDerivesKeepLastAfterSeen
    {basisSet : List (Identity Nat)}
    (dropFirst : ∀ (stem suffix : List Nat) (left right : Nat),
      left ∈ stem → right ∈ stem →
      S5_107.ListDerives basisSet
        (stem ++ [left, right] ++ suffix)
        (stem ++ [right] ++ suffix))
    (stem suffix : List Nat) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters → letter ∈ stem) →
      S5_107.ListDerives basisSet
        (stem ++ letters ++ suffix)
        (stem ++ keepLast letters ++ suffix)
  | [], _ => by
      simpa [keepLast] using
        (S5_107.ListDerives.refl (basis := basisSet) (stem ++ suffix))
  | [letter], _ => by
      simpa [keepLast] using
        (S5_107.ListDerives.refl (basis := basisSet)
          (stem ++ [letter] ++ suffix))
  | left :: right :: rest, lettersSeen => by
      have leftSeen : left ∈ stem := lettersSeen left (by simp)
      have rightSeen : right ∈ stem := lettersSeen right (by simp)
      have dropped :=
        dropFirst stem (rest ++ suffix) left right leftSeen rightSeen
      have reduced :=
        listDerivesKeepLastAfterSeen dropFirst stem suffix
          (right :: rest) (by
            intro letter member
            exact lettersSeen letter (List.Mem.tail left member))
      have droppedAligned :
          S5_107.ListDerives basisSet
            (stem ++ (left :: right :: rest) ++ suffix)
            (stem ++ (right :: rest) ++ suffix) := by
        simpa [List.append_assoc] using dropped
      simpa [keepLast] using droppedAligned.trans reduced
termination_by letters => letters.length
decreasing_by simp

end Generic

namespace Alpha

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives alphaBasis

private theorem basisA :
    Derives alphaBasis
      (Word.mk 0 [0, 1])
      (Word.mk 0 [1]) :=
  Derives.fromBasis (e := law_14_1a) <| by simp [alphaBasis]

private theorem basisB :
    Derives alphaBasis
      (Word.mk 0 [1, 0, 0])
      (Word.mk 0 [1, 0]) :=
  Derives.fromBasis (e := law_14_1b) <| by simp [alphaBasis]

private theorem basisCEmpty :
    Derives alphaBasis
      (Word.mk 0 [1, 0, 1])
      (Word.mk 0 [1, 1]) :=
  Derives.fromBasis (e := law_14_1c_empty) <| by simp [alphaBasis]

private theorem basisCH :
    Derives alphaBasis
      (Word.mk 0 [3, 1, 0, 1])
      (Word.mk 0 [3, 1, 1]) :=
  Derives.fromBasis (e := law_14_1c_H) <| by simp [alphaBasis]

private theorem basisCK :
    Derives alphaBasis
      (Word.mk 0 [1, 4, 0, 1])
      (Word.mk 0 [1, 4, 1]) :=
  Derives.fromBasis (e := law_14_1c_K) <| by simp [alphaBasis]

private theorem basisCHK :
    Derives alphaBasis
      (Word.mk 0 [3, 1, 4, 0, 1])
      (Word.mk 0 [3, 1, 4, 1]) :=
  Derives.fromBasis (e := law_14_1c_HK) <| by simp [alphaBasis]

private theorem basisDEmpty :
    Derives alphaBasis
      (Word.mk 0 [1, 1, 0])
      (Word.mk 0 [1, 0]) :=
  Derives.fromBasis (e := law_14_1d_empty) <| by simp [alphaBasis]

private theorem basisDH :
    Derives alphaBasis
      (Word.mk 0 [3, 1, 1, 0])
      (Word.mk 0 [3, 1, 0]) :=
  Derives.fromBasis (e := law_14_1d_H) <| by simp [alphaBasis]

private theorem basisDK :
    Derives alphaBasis
      (Word.mk 0 [1, 4, 1, 0])
      (Word.mk 0 [1, 4, 0]) :=
  Derives.fromBasis (e := law_14_1d_K) <| by simp [alphaBasis]

private theorem basisDHK :
    Derives alphaBasis
      (Word.mk 0 [3, 1, 4, 1, 0])
      (Word.mk 0 [3, 1, 4, 0]) :=
  Derives.fromBasis (e := law_14_1d_HK) <| by simp [alphaBasis]

theorem derivesA (x y : Word Nat) :
    Derives alphaBasis ((x ++ x) ++ y) (x ++ y) := by
  have substituted :=
    Derives.subst basisA (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesB (x y : Word Nat) :
    Derives alphaBasis (((x ++ y) ++ x) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisB (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCEmpty (x y : Word Nat) :
    Derives alphaBasis (((x ++ y) ++ x) ++ y) ((x ++ y) ++ y) := by
  have substituted :=
    Derives.subst basisCEmpty (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCH (x y h : Word Nat) :
    Derives alphaBasis
      ((((x ++ h) ++ y) ++ x) ++ y)
      (((x ++ h) ++ y) ++ y) := by
  have substituted :=
    Derives.subst basisCH (instantiateFiveWords x y h x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCK (x y k : Word Nat) :
    Derives alphaBasis
      ((((x ++ y) ++ k) ++ x) ++ y)
      (((x ++ y) ++ k) ++ y) := by
  have substituted :=
    Derives.subst basisCK (instantiateFiveWords x y x k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCHK (x y h k : Word Nat) :
    Derives alphaBasis
      (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ k) ++ y) := by
  have substituted :=
    Derives.subst basisCHK (instantiateFiveWords x y h k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDEmpty (x y : Word Nat) :
    Derives alphaBasis (((x ++ y) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisDEmpty (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDH (x y h : Word Nat) :
    Derives alphaBasis
      ((((x ++ h) ++ y) ++ y) ++ x)
      (((x ++ h) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisDH (instantiateFiveWords x y h x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDK (x y k : Word Nat) :
    Derives alphaBasis
      ((((x ++ y) ++ k) ++ y) ++ x)
      (((x ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisDK (instantiateFiveWords x y x k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDHK (x y h k : Word Nat) :
    Derives alphaBasis
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x)
      ((((x ++ h) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisDHK (instantiateFiveWords x y h k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem listDerivesA
    (letter suffixHead : Nat) (suffixTail : List Nat) :
    ListDerives
      ([letter, letter] ++ (suffixHead :: suffixTail))
      ([letter] ++ (suffixHead :: suffixTail)) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (derivesA (Word.singleton letter)
          (listWordOfCons suffixHead suffixTail)))

private theorem listDerivesB
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (derivesB (Word.singleton letter)
          (listWordOfCons gapHead gapTail)))

theorem listDerivesContractAdjacentAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives
      (stem ++ [letter, letter] ++ suffix)
      (stem ++ [letter] ++ suffix) := by
  obtain ⟨before, gap, prefixShape⟩ :=
    List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [prefixShape, List.append_assoc] using
        (listDerivesA letter letter suffix).prepend before
  | cons gapHead gapTail =>
      simpa [prefixShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesB letter gapHead gapTail)

theorem listDerivesDropCDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second] ++ after) :=
  Generic.listDerivesDropCDisplayed
    derivesCEmpty derivesCH derivesCK derivesCHK
    first second before firstGap secondGap after

theorem listDerivesDropDDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first] ++ after) :=
  Generic.listDerivesDropDDisplayed
    derivesDEmpty derivesDH derivesDK derivesDHK
    first second before firstGap secondGap after

theorem listDerivesDropFirstAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right] ++ suffix) :=
  Generic.listDerivesDropFirstAfterSeen
    listDerivesContractAdjacentAfterSeen
    listDerivesDropCDisplayed listDerivesDropDDisplayed
    stem suffix left right leftSeen rightSeen

theorem listDerivesKeepLastAfterSeen
    (stem letters suffix : List Nat)
    (lettersSeen : ∀ letter, letter ∈ letters → letter ∈ stem) :
    ListDerives
      (stem ++ letters ++ suffix)
      (stem ++ keepLast letters ++ suffix) :=
  Generic.listDerivesKeepLastAfterSeen
    listDerivesDropFirstAfterSeen stem suffix letters lettersSeen

end Alpha

namespace Beta

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives betaBasis

private theorem basisA :
    Derives betaBasis
      (Word.mk 0 [0, 1])
      (Word.mk 0 [1]) :=
  Derives.fromBasis (e := law_14_3a) <| by simp [betaBasis]

private theorem basisB :
    Derives betaBasis
      (Word.mk 0 [1, 1])
      (Word.mk 0 [1]) :=
  Derives.fromBasis (e := law_14_3b) <| by simp [betaBasis]

private theorem basisCEmpty :
    Derives betaBasis
      (Word.mk 0 [1, 0, 1])
      (Word.mk 0 [1, 1]) :=
  Derives.fromBasis (e := law_14_3c_empty) <| by simp [betaBasis]

private theorem basisCH :
    Derives betaBasis
      (Word.mk 0 [3, 1, 0, 1])
      (Word.mk 0 [3, 1, 1]) :=
  Derives.fromBasis (e := law_14_3c_H) <| by simp [betaBasis]

private theorem basisCK :
    Derives betaBasis
      (Word.mk 0 [1, 4, 0, 1])
      (Word.mk 0 [1, 4, 1]) :=
  Derives.fromBasis (e := law_14_3c_K) <| by simp [betaBasis]

private theorem basisCHK :
    Derives betaBasis
      (Word.mk 0 [3, 1, 4, 0, 1])
      (Word.mk 0 [3, 1, 4, 1]) :=
  Derives.fromBasis (e := law_14_3c_HK) <| by simp [betaBasis]

private theorem basisDEmpty :
    Derives betaBasis
      (Word.mk 0 [1, 1, 0])
      (Word.mk 0 [1, 0]) :=
  Derives.fromBasis (e := law_14_3d_empty) <| by simp [betaBasis]

private theorem basisDH :
    Derives betaBasis
      (Word.mk 0 [3, 1, 1, 0])
      (Word.mk 0 [3, 1, 0]) :=
  Derives.fromBasis (e := law_14_3d_H) <| by simp [betaBasis]

private theorem basisDK :
    Derives betaBasis
      (Word.mk 0 [1, 4, 1, 0])
      (Word.mk 0 [1, 4, 0]) :=
  Derives.fromBasis (e := law_14_3d_K) <| by simp [betaBasis]

private theorem basisDHK :
    Derives betaBasis
      (Word.mk 0 [3, 1, 4, 1, 0])
      (Word.mk 0 [3, 1, 4, 0]) :=
  Derives.fromBasis (e := law_14_3d_HK) <| by simp [betaBasis]

theorem derivesA (x y : Word Nat) :
    Derives betaBasis ((x ++ x) ++ y) (x ++ y) := by
  have substituted :=
    Derives.subst basisA (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesB (x y : Word Nat) :
    Derives betaBasis ((x ++ y) ++ y) (x ++ y) := by
  have substituted :=
    Derives.subst basisB (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCEmpty (x y : Word Nat) :
    Derives betaBasis (((x ++ y) ++ x) ++ y) ((x ++ y) ++ y) := by
  have substituted :=
    Derives.subst basisCEmpty (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCH (x y h : Word Nat) :
    Derives betaBasis
      ((((x ++ h) ++ y) ++ x) ++ y)
      (((x ++ h) ++ y) ++ y) := by
  have substituted :=
    Derives.subst basisCH (instantiateFiveWords x y h x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCK (x y k : Word Nat) :
    Derives betaBasis
      ((((x ++ y) ++ k) ++ x) ++ y)
      (((x ++ y) ++ k) ++ y) := by
  have substituted :=
    Derives.subst basisCK (instantiateFiveWords x y x k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesCHK (x y h k : Word Nat) :
    Derives betaBasis
      (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ k) ++ y) := by
  have substituted :=
    Derives.subst basisCHK (instantiateFiveWords x y h k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDEmpty (x y : Word Nat) :
    Derives betaBasis (((x ++ y) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisDEmpty (instantiateFiveWords x y x x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDH (x y h : Word Nat) :
    Derives betaBasis
      ((((x ++ h) ++ y) ++ y) ++ x)
      (((x ++ h) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisDH (instantiateFiveWords x y h x x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDK (x y k : Word Nat) :
    Derives betaBasis
      ((((x ++ y) ++ k) ++ y) ++ x)
      (((x ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisDK (instantiateFiveWords x y x k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDHK (x y h k : Word Nat) :
    Derives betaBasis
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x)
      ((((x ++ h) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisDHK (instantiateFiveWords x y h k x)
  simpa [instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem listDerivesContractAdjacentAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives
      (stem ++ [letter, letter] ++ suffix)
      (stem ++ [letter] ++ suffix) := by
  cases stem with
  | nil => simp at seen
  | cons head tail =>
      have base := S5_107.ListDerives.ofWord
        (derivesB (listWordOfCons head tail) (Word.singleton letter))
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using base.append suffix

theorem listDerivesDropCDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second] ++ after) :=
  Generic.listDerivesDropCDisplayed
    derivesCEmpty derivesCH derivesCK derivesCHK
    first second before firstGap secondGap after

theorem listDerivesDropDDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first] ++ after) :=
  Generic.listDerivesDropDDisplayed
    derivesDEmpty derivesDH derivesDK derivesDHK
    first second before firstGap secondGap after

theorem listDerivesDropFirstAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right] ++ suffix) :=
  Generic.listDerivesDropFirstAfterSeen
    listDerivesContractAdjacentAfterSeen
    listDerivesDropCDisplayed listDerivesDropDDisplayed
    stem suffix left right leftSeen rightSeen

theorem listDerivesKeepLastAfterSeen
    (stem letters suffix : List Nat)
    (lettersSeen : ∀ letter, letter ∈ letters → letter ∈ stem) :
    ListDerives
      (stem ++ letters ++ suffix)
      (stem ++ keepLast letters ++ suffix) :=
  Generic.listDerivesKeepLastAfterSeen
    listDerivesDropFirstAfterSeen stem suffix letters lettersSeen

end Beta

end SemigroupBasis.CoRoots.Order6SporadicSection14
