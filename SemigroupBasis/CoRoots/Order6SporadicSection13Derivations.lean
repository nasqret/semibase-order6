import SemigroupBasis.CoRoots.Order6SporadicSection13Tables
import SemigroupBasis.CoRoots.S5_107ListDerives

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

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

private theorem basisPowerEmpty :
    Derives basis word_13_1a_empty_left word_13_1a_empty_right :=
  Derives.fromBasis (e := law_13_1a_empty) <| by simp [basis]

private theorem basisPowerH :
    Derives basis word_13_1a_H_left word_13_1a_H_right :=
  Derives.fromBasis (e := law_13_1a_H) <| by simp [basis]

private theorem basisTailEmpty :
    Derives basis word_13_1b_empty_left word_13_1b_empty_right :=
  Derives.fromBasis (e := law_13_1b_empty) <| by simp [basis]

private theorem basisTailH :
    Derives basis word_13_1b_H_left word_13_1b_H_right :=
  Derives.fromBasis (e := law_13_1b_H) <| by simp [basis]

private theorem basisSortEmpty :
    Derives basis word_13_1c_empty_left word_13_1c_empty_right :=
  Derives.fromBasis (e := law_13_1c_empty) <| by simp [basis]

private theorem basisSortH :
    Derives basis word_13_1c_H_left word_13_1c_H_right :=
  Derives.fromBasis (e := law_13_1c_H) <| by simp [basis]

private theorem basisSortK :
    Derives basis word_13_1c_K_left word_13_1c_K_right :=
  Derives.fromBasis (e := law_13_1c_K) <| by simp [basis]

private theorem basisSortHK :
    Derives basis word_13_1c_HK_left word_13_1c_HK_right :=
  Derives.fromBasis (e := law_13_1c_HK) <| by simp [basis]

theorem derivesPowerEmpty (x : Word Nat) :
    Derives basis
      (((x ++ x) ++ x) ++ x)
      (x ++ x) := by
  have substituted :=
    Derives.subst basisPowerEmpty
      (instantiateFiveWords x x x x x)
  simpa [word_13_1a_empty_left, word_13_1a_empty_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesPowerH (x h : Word Nat) :
    Derives basis
      ((((x ++ h) ++ x) ++ x) ++ x)
      ((x ++ h) ++ x) := by
  have substituted :=
    Derives.subst basisPowerH
      (instantiateFiveWords x x h x x)
  simpa [word_13_1a_H_left, word_13_1a_H_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem listDerivesPowerEmpty
    (letter : Nat) :
    ListDerives [letter, letter, letter, letter]
      [letter, letter] := by
  simpa [Word.singleton, Word.append] using
    (S5_107.ListDerives.ofWord (basis := basis)
      (derivesPowerEmpty (Word.singleton letter)))

private theorem listDerivesPowerH
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++
        [letter, letter, letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesPowerH
          (Word.singleton letter)
          (listWordOfCons gapHead gapTail)))

/-- Append two copies of the final letter when that final letter already
occurs in the displayed prefix.  This is the list form of (13.1a) used in
Lemma 13.3. -/
theorem listDerivesAppendFinalSquareOfSeen
    (stem : List Nat) (final : Nat)
    (seen : final ∈ stem) :
    ListDerives
      (stem ++ [final])
      (stem ++ [final, final, final]) := by
  obtain ⟨before, gap, prefixShape⟩ :=
    List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [prefixShape, List.append_assoc] using
        (listDerivesPowerEmpty final).symm.prepend before
  | cons gapHead gapTail =>
      simpa [prefixShape, List.append_assoc] using
        (listDerivesPowerH final gapHead gapTail).symm.prepend before

/-- Delete an adjacent pair after the first displayed copy when a nonempty
right context is present. -/
theorem derivesTailEmpty (x suffix : Word Nat) :
    Derives basis
      (((x ++ x) ++ x) ++ suffix)
      (x ++ suffix) := by
  have substituted :=
    Derives.subst basisTailEmpty
      (instantiateFiveWords x suffix x x x)
  simpa [word_13_1b_empty_left, word_13_1b_empty_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The nonempty-interior form of the parity-pair deletion. -/
theorem derivesTailH (x h suffix : Word Nat) :
    Derives basis
      ((((x ++ h) ++ x) ++ x) ++ suffix)
      ((x ++ h) ++ suffix) := by
  have substituted :=
    Derives.subst basisTailH
      (instantiateFiveWords x suffix h x x)
  simpa [word_13_1b_H_left, word_13_1b_H_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSortEmpty (x y : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortEmpty
      (instantiateFiveWords x y x y x)
  simpa [word_13_1c_empty_left, word_13_1c_empty_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSortH (x y h : Word Nat) :
    Derives basis
      ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortH
      (instantiateFiveWords x y h y x)
  simpa [word_13_1c_H_left, word_13_1c_H_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSortK (x y k : Word Nat) :
    Derives basis
      ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortK
      (instantiateFiveWords x y x k x)
  simpa [word_13_1c_K_left, word_13_1c_K_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSortHK (x y h k : Word Nat) :
    Derives basis
      (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortHK
      (instantiateFiveWords x y h k x)
  simpa [word_13_1c_HK_left, word_13_1c_HK_right, section13Word,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem listDerivesDeletePairEmpty
    (letter suffixHead : Nat) (suffixTail : List Nat) :
    ListDerives
      ([letter, letter, letter] ++ (suffixHead :: suffixTail))
      ([letter] ++ (suffixHead :: suffixTail)) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesTailEmpty
          (Word.singleton letter)
          (listWordOfCons suffixHead suffixTail)))

private theorem listDerivesDeletePairH
    (letter gapHead suffixHead : Nat)
    (gapTail suffixTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter] ++
        (suffixHead :: suffixTail))
      ([letter] ++ (gapHead :: gapTail) ++
        (suffixHead :: suffixTail)) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesTailH
          (Word.singleton letter)
          (listWordOfCons gapHead gapTail)
          (listWordOfCons suffixHead suffixTail)))

/-- Delete two adjacent later copies of a letter.  The earlier copy may be in
arbitrary left context; the supplied suffix is explicitly nonempty. -/
theorem listDerivesDeleteAdjacentPairAfterSeen
    (letter suffixHead : Nat)
    (before gap suffixTail : List Nat) :
    ListDerives
      (before ++ [letter] ++ gap ++ [letter, letter] ++
        (suffixHead :: suffixTail))
      (before ++ [letter] ++ gap ++
        (suffixHead :: suffixTail)) := by
  cases gap with
  | nil =>
      simpa [List.append_assoc] using
        (listDerivesDeletePairEmpty letter suffixHead suffixTail).prepend before
  | cons gapHead gapTail =>
      simpa [List.append_assoc] using
        (listDerivesDeletePairH
          letter gapHead suffixHead gapTail suffixTail).prepend before

/-- Context form of pair deletion.  Membership locates the protected earlier
copy in `prefix`; nonemptiness supplies the final semigroup-word context. -/
theorem listDerivesDeleteAdjacentPairAfterPrefix
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) (suffixNonempty : suffix ≠ []) :
    ListDerives
      (stem ++ [letter, letter] ++ suffix)
      (stem ++ suffix) := by
  obtain ⟨before, gap, prefixShape⟩ :=
    List.mem_iff_append.mp seen
  cases suffix with
  | nil => contradiction
  | cons suffixHead suffixTail =>
      simpa [prefixShape, List.append_assoc] using
        listDerivesDeleteAdjacentPairAfterSeen
          letter suffixHead before gap suffixTail

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives
      [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortFirstGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortK
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortSecondGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortH
          (Word.singleton first)
          (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortHK
          (Word.singleton first)
          (Word.singleton second)
          (listWordOfCons firstGapHead firstGapTail)
          (listWordOfCons secondGapHead secondGapTail)))

/-- The four ordinary placements of (13.1c), with arbitrary outer context. -/
theorem listDerivesSwapDisplayedLaterCopies
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFirstGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortSecondGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

/-- Once both letters have earlier occurrences, two adjacent later copies may
be swapped in either first-occurrence order. -/
theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives
      (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
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
      have displayed :=
        listDerivesSwapDisplayedLaterCopies
          right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedLaterCopies
          left right leftBefore middle tail suffix

/-- Any permutation of a later block is derivable when every block letter has
already appeared in the fixed prefix. -/
theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives
      (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        have inPrefix : letter ∈ stem :=
          sourceSeen letter (List.Mem.tail head member)
        exact List.mem_append.mpr (Or.inl inPrefix))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem := sourceSeen first (by simp)
      have secondSeen : second ∈ stem := sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen
          stem (rest ++ suffix) second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

end SemigroupBasis.CoRoots.Order6SporadicSection13
