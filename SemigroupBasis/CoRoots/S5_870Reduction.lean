import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_870

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Deleting an explicitly displayed third occurrence -/

private theorem listDerivesCapBothEmpty (letter : Nat) :
    ListDerives [letter, letter, letter] [letter, letter] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesCapBothEmpty (Word.singleton letter)))

private theorem listDerivesCapInitialGapEmpty
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter, letter] ++ (gapHead :: gapTail) ++ [letter])
      ([letter, letter] ++ (gapHead :: gapTail)) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesCapInitialGapEmpty
          (Word.singleton letter)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesCapFinalGapEmpty
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesCapFinalGapEmpty
          (Word.singleton letter)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesCapGeneral
    (letter firstHead secondHead : Nat)
    (firstTail secondTail : List Nat) :
    ListDerives
      ([letter] ++ (firstHead :: firstTail) ++ [letter] ++
        (secondHead :: secondTail) ++ [letter])
      ([letter] ++ (firstHead :: firstTail) ++ [letter] ++
        (secondHead :: secondTail)) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesCapGeneral
          (Word.singleton letter)
          (listWordOfCons firstHead firstTail)
          (listWordOfCons secondHead secondTail)))

/-- Delete a displayed third occurrence of `letter` in arbitrary list
context. The four branches are exactly the empty/nonempty cases for the two
intervening gaps, and use the corresponding four cap laws from `S5_870`. -/
theorem listDerivesDeleteThirdOccurrence
    (letter : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesCapBothEmpty letter)
      | cons secondHead secondTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesCapInitialGapEmpty
                letter secondHead secondTail)
  | cons firstHead firstTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesCapFinalGapEmpty
                letter firstHead firstTail)
      | cons secondHead secondTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesCapGeneral letter firstHead secondHead
                firstTail secondTail)

private theorem exists_two_occurrence_split_of_count_ge_two
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : letter ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact
          ⟨[], middle, after,
            by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter restCount
        exact
          ⟨first :: before, middle, after,
            by simp [split, List.append_assoc]⟩

/-! ## Left-to-right occurrence cap -/

/-- Append `letter` exactly when the retained prefix contains fewer than two
copies. -/
def capStep (kept : List Nat) (letter : Nat) : List Nat :=
  if kept.count letter < 2 then kept ++ [letter] else kept

/-- Scan from left to right, retaining the first two occurrences of every
letter and deleting every later occurrence. -/
def capScan (letters : List Nat) : List Nat :=
  letters.foldl capStep []

private theorem foldl_capStep_count
    (tested : Nat) :
    ∀ (letters kept : List Nat),
      kept.count tested ≤ 2 →
      (letters.foldl capStep kept).count tested =
        min (kept.count tested + letters.count tested) 2
  | [], kept, keptBound => by
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact (Nat.min_eq_left keptBound).symm
  | letter :: rest, kept, keptBound => by
      simp only [List.foldl_cons]
      by_cases room : kept.count letter < 2
      · have nextBound :
            (kept ++ [letter]).count tested ≤ 2 := by
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptBound
        rw [show capStep kept letter = kept ++ [letter] by
          simp [capStep, room]]
        rw [foldl_capStep_count tested rest
          (kept ++ [letter]) nextBound]
        rw [List.count_append]
        by_cases equality : letter = tested
        · subst letter
          simp only [List.count_cons_self, List.count_nil]
          omega
        · have singletonZero : [letter].count tested = 0 := by
            simp [equality]
          rw [singletonZero, Nat.add_zero,
            List.count_cons_of_ne equality]
      · rw [show capStep kept letter = kept by
          simp [capStep, room]]
        rw [foldl_capStep_count tested rest kept keptBound]
        by_cases equality : letter = tested
        · subst letter
          have full : kept.count tested = 2 := by
            omega
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne equality]

/-- The scan implements pointwise multiplicity capping at two. -/
theorem capScan_count (tested : Nat) (letters : List Nat) :
    (capScan letters).count tested = min (letters.count tested) 2 := by
  simpa [capScan] using
    foldl_capStep_count tested letters [] (by simp)

/-- Every output multiplicity is at most two. -/
theorem capScan_count_le_two (tested : Nat) (letters : List Nat) :
    (capScan letters).count tested ≤ 2 := by
  rw [capScan_count]
  exact Nat.min_le_right _ _

/-- The scan preserves variable support. -/
theorem mem_capScan_iff (tested : Nat) (letters : List Nat) :
    tested ∈ capScan letters ↔ tested ∈ letters := by
  rw [← List.count_pos_iff, ← List.count_pos_iff,
    capScan_count]
  omega

/-- A nonempty source has a nonempty scan result. -/
theorem capScan_ne_nil {letters : List Nat}
    (nonempty : letters ≠ []) : capScan letters ≠ [] := by
  cases letters with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      exact List.ne_nil_of_mem <|
        (mem_capScan_iff head (head :: tail)).mpr (by simp)

private theorem listDerivesCapScanFrom :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 2) →
      ListDerives
        (kept ++ remaining)
        (remaining.foldl capStep kept)
  | [], kept, _ => by
      simpa using
        (S5_107.ListDerives.refl (basis := basis) kept)
  | letter :: rest, kept, keptLimited => by
      by_cases room : kept.count letter < 2
      · have nextLimited :
            ∀ tested, (kept ++ [letter]).count tested ≤ 2 := by
          intro tested
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptLimited tested
        have recurse :=
          listDerivesCapScanFrom rest (kept ++ [letter])
            nextLimited
        simpa [capStep, room, List.append_assoc] using recurse
      · have full : kept.count letter = 2 := by
          have bound := keptLimited letter
          omega
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            letter (letters := kept) (by omega)
        have deleteCurrent :
            ListDerives
              (kept ++ letter :: rest)
              (kept ++ rest) := by
          rw [split]
          simpa [List.append_assoc] using
            listDerivesDeleteThirdOccurrence
              letter before middle after rest
        have recurse :=
          listDerivesCapScanFrom rest kept keptLimited
        have combined := deleteCurrent.trans recurse
        simpa [capStep, room] using combined

/-- Every list derives to its left-to-right two-occurrence cap. -/
theorem listDerivesCapScan (letters : List Nat) :
    ListDerives letters (capScan letters) := by
  simpa [capScan] using
    listDerivesCapScanFrom letters [] (by simp)

/-! ## Word-level reduction -/

private theorem word_toList_ne_nil (word : Word Nat) :
    word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      simp [Word.toList]

private def wordOfNonemptyList :
    (letters : List Nat) → letters ≠ [] → Word Nat
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => listWordOfCons head tail

private theorem toList_wordOfNonemptyList
    (letters : List Nat) (nonempty : letters ≠ []) :
    (wordOfNonemptyList letters nonempty).toList = letters := by
  cases letters with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      rfl

private theorem listDerives_toWordOfNonemptyList
    {left right : List Nat}
    (derivation : ListDerives left right)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    Derives basis
      (wordOfNonemptyList left leftNonempty)
      (wordOfNonemptyList right rightNonempty) := by
  cases derivation with
  | empty =>
      exact False.elim (leftNonempty rfl)
  | words wordDerivation =>
      simpa [wordOfNonemptyList] using wordDerivation

/-- The nonempty semigroup word represented by the scan result. -/
def capScanWord (word : Word Nat) : Word Nat :=
  wordOfNonemptyList (capScan word.toList)
    (capScan_ne_nil (word_toList_ne_nil word))

@[simp]
theorem capScanWord_toList (word : Word Nat) :
    (capScanWord word).toList = capScan word.toList := by
  exact toList_wordOfNonemptyList _ _

/-- Every word derives to its scanned word. -/
theorem derivesCapScanWord (word : Word Nat) :
    Derives basis word (capScanWord word) := by
  have sourceNonempty := word_toList_ne_nil word
  have targetNonempty := capScan_ne_nil sourceNonempty
  have listDerivation := listDerivesCapScan word.toList
  have wordDerivation :=
    listDerives_toWordOfNonemptyList listDerivation
      sourceNonempty targetNonempty
  have sourceEq :
      wordOfNonemptyList word.toList sourceNonempty = word := by
    apply Word.toList_injective
    exact toList_wordOfNonemptyList _ _
  have targetEq :
      wordOfNonemptyList (capScan word.toList) targetNonempty =
        capScanWord word := by
    apply Word.toList_injective
    rw [toList_wordOfNonemptyList, capScanWord_toList]
  rw [sourceEq, targetEq] at wordDerivation
  exact wordDerivation

/-- Word-level form of exact multiplicity capping. -/
theorem capScanWord_count (tested : Nat) (word : Word Nat) :
    (capScanWord word).toList.count tested =
      min (word.toList.count tested) 2 := by
  rw [capScanWord_toList]
  exact capScan_count tested word.toList

/-- The scanned word is two-limited. -/
theorem capScanWord_isTwoLimited (word : Word Nat) :
    IsTwoLimited (capScanWord word) := by
  intro tested
  rw [capScanWord_toList]
  exact capScan_count_le_two tested word.toList

/-- Word-level support preservation. -/
theorem mem_capScanWord_iff (tested : Nat) (word : Word Nat) :
    tested ∈ (capScanWord word).toList ↔ tested ∈ word.toList := by
  rw [capScanWord_toList]
  exact mem_capScan_iff tested word.toList

end SemigroupBasis.CoRoots.S5_870
