import SemigroupBasis.CoRoots.Order6SporadicSection27F10Basis

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat := ⟨head, tail⟩

private def instantiateFiveWords
    (x y h k t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => h
  | 3 => k
  | 4 => t
  | n + 5 => Word.singleton (n + 5)

private theorem basisAEmpty :
    Derives basis (w 0 [0, 0]) (w 0 [0]) :=
  Derives.fromBasis (e := lawA_empty) (by simp [basis])

private theorem basisAH :
    Derives basis (w 0 [2, 0, 0]) (w 0 [2, 0]) :=
  Derives.fromBasis (e := lawA_H) (by simp [basis])

private theorem basisBEmpty :
    Derives basis (w 0 [1, 0, 1]) (w 0 [1, 1, 0]) :=
  Derives.fromBasis (e := lawB_empty) (by simp [basis])

private theorem basisBH :
    Derives basis (w 0 [2, 1, 0, 1]) (w 0 [2, 1, 1, 0]) :=
  Derives.fromBasis (e := lawB_H) (by simp [basis])

private theorem basisBK :
    Derives basis (w 0 [1, 3, 0, 1]) (w 0 [1, 3, 1, 0]) :=
  Derives.fromBasis (e := lawB_K) (by simp [basis])

private theorem basisBHK :
    Derives basis (w 0 [2, 1, 3, 0, 1])
      (w 0 [2, 1, 3, 1, 0]) :=
  Derives.fromBasis (e := lawB_HK) (by simp [basis])

private theorem basisCEmpty :
    Derives basis (w 0 [1, 1, 0]) (w 0 [1, 0]) :=
  Derives.fromBasis (e := lawC_empty) (by simp [basis])

private theorem basisCH :
    Derives basis (w 0 [2, 1, 1, 0]) (w 0 [2, 1, 0]) :=
  Derives.fromBasis (e := lawC_H) (by simp [basis])

private theorem basisCK :
    Derives basis (w 0 [1, 3, 1, 0]) (w 0 [1, 3, 0]) :=
  Derives.fromBasis (e := lawC_K) (by simp [basis])

private theorem basisCHK :
    Derives basis (w 0 [2, 1, 3, 1, 0]) (w 0 [2, 1, 3, 0]) :=
  Derives.fromBasis (e := lawC_HK) (by simp [basis])

private theorem basisDEmpty :
    Derives basis (w 0 [1, 0, 1]) (w 0 [1, 0, 0]) :=
  Derives.fromBasis (e := lawD_empty) (by simp [basis])

private theorem basisDH :
    Derives basis (w 0 [2, 1, 0, 1]) (w 0 [2, 1, 0, 0]) :=
  Derives.fromBasis (e := lawD_H) (by simp [basis])

private theorem basisDK :
    Derives basis (w 0 [1, 3, 0, 1]) (w 0 [1, 3, 0, 0]) :=
  Derives.fromBasis (e := lawD_K) (by simp [basis])

private theorem basisDHK :
    Derives basis (w 0 [2, 1, 3, 0, 1]) (w 0 [2, 1, 3, 0, 0]) :=
  Derives.fromBasis (e := lawD_HK) (by simp [basis])

private theorem basisDT :
    Derives basis (w 0 [1, 0, 4, 1]) (w 0 [1, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_T) (by simp [basis])

private theorem basisDHT :
    Derives basis (w 0 [2, 1, 0, 4, 1]) (w 0 [2, 1, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_HT) (by simp [basis])

private theorem basisDKT :
    Derives basis (w 0 [1, 3, 0, 4, 1]) (w 0 [1, 3, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_KT) (by simp [basis])

private theorem basisDHKT :
    Derives basis (w 0 [2, 1, 3, 0, 4, 1])
      (w 0 [2, 1, 3, 0, 4, 0]) :=
  Derives.fromBasis (e := lawD_HKT) (by simp [basis])

theorem derivesAEmpty (x : Word Nat) :
    Derives basis ((x ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisAEmpty (instantiateFiveWords x x x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesAH (x h : Word Nat) :
    Derives basis (((x ++ h) ++ x) ++ x) ((x ++ h) ++ x) := by
  have substituted :=
    Derives.subst basisAH (instantiateFiveWords x x h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesBHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisBHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisCEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ y) ++ x)
      (((x ++ h) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisCH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ y) ++ x)
      (((x ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisCK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesCHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ y) ++ x)
      ((((x ++ h) ++ y) ++ k) ++ x) := by
  have substituted :=
    Derives.subst basisCHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDEmpty (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDEmpty (instantiateFiveWords x y x x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDH (x y h : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDH (instantiateFiveWords x y h x x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDK (x y k : Word Nat) :
    Derives basis ((((x ++ y) ++ k) ++ x) ++ y)
      ((((x ++ y) ++ k) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDK (instantiateFiveWords x y x k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHK (x y h k : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ k) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ k) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisDHK (instantiateFiveWords x y h k x)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDT (x y t : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ t) ++ y)
      ((((x ++ y) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDT (instantiateFiveWords x y x x t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHT (x y h t : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ x) ++ t) ++ y)
      (((((x ++ h) ++ y) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDHT (instantiateFiveWords x y h x t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDKT (x y k t : Word Nat) :
    Derives basis (((((x ++ y) ++ k) ++ x) ++ t) ++ y)
      (((((x ++ y) ++ k) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDKT (instantiateFiveWords x y x k t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

theorem derivesDHKT (x y h k t : Word Nat) :
    Derives basis ((((((x ++ h) ++ y) ++ k) ++ x) ++ t) ++ y)
      ((((((x ++ h) ++ y) ++ k) ++ x) ++ t) ++ x) := by
  have substituted :=
    Derives.subst basisDHKT (instantiateFiveWords x y h k t)
  simpa [w, instantiateFiveWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons

/-! ### Arbitrary-gap sorting from (27.1b) -/

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBEmpty (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBK (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesBH (Word.singleton first) (Word.singleton second)
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
        (derivesBHK (Word.singleton first) (Word.singleton second)
          (listWordOfCons firstGapHead firstGapTail)
          (listWordOfCons secondGapHead secondGapTail)))

theorem listDerivesSwapDisplayedSeconds
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
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral
                first firstGapHead second secondGapHead
                firstGapTail secondGapTail)

theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives (stem ++ [left, right] ++ suffix)
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
      have displayed := listDerivesSwapDisplayedSeconds
        right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen letter (List.Mem.tail head member))
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

/-! ### Letter removal and retargeting from (27.1c--d) -/

theorem listDerivesCDisplayed
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCEmpty (Word.singleton first) (Word.singleton second))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCK (Word.singleton first) (Word.singleton second)
              (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
  | cons hHead hTail =>
      cases secondGap with
      | nil =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCH (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          have base := S5_107.ListDerives.ofWord (basis := basis)
            (derivesCHK (Word.singleton first) (Word.singleton second)
              (listWordOfCons hHead hTail) (listWordOfCons kHead kTail))
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after base

theorem listDerivesDDisplayed
    (first second : Nat)
    (before hGap kGap tGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ hGap ++ [second] ++ kGap ++
        [first] ++ tGap ++ [second] ++ after)
      (before ++ [first] ++ hGap ++ [second] ++ kGap ++
        [first] ++ tGap ++ [first] ++ after) := by
  cases hGap with
  | nil =>
      cases kGap with
      | nil =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDEmpty
                  (Word.singleton first) (Word.singleton second))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDK
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons kHead kTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDKT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons kHead kTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
  | cons hHead hTail =>
      cases kGap with
      | nil =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDH
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
      | cons kHead kTail =>
          cases tGap with
          | nil =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHK
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons kHead kTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base
          | cons tHead tTail =>
              have base := S5_107.ListDerives.ofWord (basis := basis)
                (derivesDHKT
                  (Word.singleton first) (Word.singleton second)
                  (listWordOfCons hHead hTail)
                  (listWordOfCons kHead kTail)
                  (listWordOfCons tHead tTail))
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using
                  S5_107.ListDerives.context before after base

/-! ### Duplicate contraction from (27.1a) -/

private theorem listDerivesPowerContraction (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter] := by
  simpa [listWordOfCons, Word.singleton, Word.append, Word.append_assoc] using
    (S5_107.ListDerives.ofWord (basis := basis)
      (derivesAEmpty (Word.singleton letter)))

private theorem listDerivesGapContraction
    (letter bridgeHead : Nat) (bridgeTail : List Nat) :
    ListDerives
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter, letter])
      ([letter] ++ (bridgeHead :: bridgeTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesAH (Word.singleton letter)
          (listWordOfCons bridgeHead bridgeTail)))

theorem listDerivesContractAdjacentAfterSeen
    (stem suffix : List Nat) (letter : Nat)
    (seen : letter ∈ stem) :
    ListDerives (stem ++ [letter, letter] ++ suffix)
      (stem ++ [letter] ++ suffix) := by
  obtain ⟨before, after, stemShape⟩ := List.mem_iff_append.mp seen
  cases after with
  | nil =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesPowerContraction letter)
  | cons bridgeHead bridgeTail =>
      simpa [stemShape, List.append_assoc] using
        S5_107.ListDerives.context before suffix
          (listDerivesGapContraction letter bridgeHead bridgeTail)

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesAEmpty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesAH
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesBEmpty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesBH
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesBK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesBHK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesCEmpty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesCH
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesCK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesCHK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDEmpty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDH
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDHK
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDT
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDHT
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDKT
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.derivesDHKT
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSwapDisplayedSeconds
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSwapAfterSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesPermuteAfterSeen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesCDisplayed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesDDisplayed
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesContractAdjacentAfterSeen
