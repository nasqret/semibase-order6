import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.CoRoots.S5_254Canonical
import SemigroupBasis.CoRoots.S6_3944Normalization

namespace SemigroupBasis.CoRoots.S6_3944

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## Nonempty deletion projections -/

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => S5_107.listWordOfCons head tail

@[simp]
private theorem toList_wordOfListOr_of_ne_nil
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfListOr fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

private theorem valid_filtered_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (keep : Nat → Bool)
    (leftNonempty : identity.lhs.toList.filter keep ≠ [])
    (rightNonempty : identity.rhs.toList.filter keep ≠ []) :
    S5_107.SameSimpleAdjacencySignature
      (wordOfListOr identity.lhs.head
        (identity.lhs.toList.filter keep))
      (wordOfListOr identity.rhs.head
        (identity.rhs.toList.filter keep)) := by
  obtain ⟨leftHead, leftTail, leftShape⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rightShape⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  simpa [wordOfListOr, leftShape, rightShape] using
    valid_filtered_sameSimpleAdjacencySignature identity valid keep
      leftHead rightHead leftTail rightTail leftShape rightShape

/-! ## Literal simple-variable sequence -/

def simpleKeep (letters : List Nat) (letter : Nat) : Bool :=
  decide (letters.count letter = 1)

def simpleProjection (letters : List Nat) : List Nat :=
  letters.filter (simpleKeep letters)

private theorem simpleKeep_eq_of_sameSignature
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right) :
    simpleKeep left.toList = simpleKeep right.toList := by
  funext letter
  have equivalence :
      left.toList.count letter = 1 ↔
        right.toList.count letter = 1 := by
    simpa [S5_107.SimpleIn] using same.simple letter
  by_cases leftSimple : left.toList.count letter = 1
  · have rightSimple := equivalence.mp leftSimple
    simp [simpleKeep, leftSimple, rightSimple]
  · have rightNotSimple : right.toList.count letter ≠ 1 :=
      fun rightSimple => leftSimple (equivalence.mpr rightSimple)
    simp [simpleKeep, leftSimple, rightNotSimple]

private theorem simpleProjection_nonempty_of_sameSignature
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right) :
    simpleProjection left.toList ≠ [] →
      simpleProjection right.toList ≠ [] := by
  intro leftNonempty rightEmpty
  obtain ⟨letter, leftMember⟩ :=
    List.exists_mem_of_ne_nil _ leftNonempty
  have leftData := List.mem_filter.mp leftMember
  have leftSimple : left.toList.count letter = 1 := by
    simpa [simpleKeep] using leftData.2
  have rightSimple : right.toList.count letter = 1 := by
    exact (same.simple letter).mp leftSimple
  have rightMember : letter ∈ simpleProjection right.toList := by
    apply List.mem_filter.mpr
    exact ⟨List.count_pos_iff.mp (by omega), by
      simp [simpleKeep, rightSimple]⟩
  rw [rightEmpty] at rightMember
  simp at rightMember

private theorem simpleProjection_nonempty_iff
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right) :
    simpleProjection left.toList ≠ [] ↔
      simpleProjection right.toList ≠ [] :=
  ⟨simpleProjection_nonempty_of_sameSignature same,
    simpleProjection_nonempty_of_sameSignature same.symm⟩

private theorem sortedMultipleLetters_filter_simple_eq_nil
    (letters : List Nat) :
    S5_107.sortedMultipleLetters (simpleProjection letters) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter listed
  have multiple :=
    (S5_107.sortedMultipleLetters_mem_iff
      letter (simpleProjection letters)).mp listed
  have projectedMember : letter ∈ simpleProjection letters :=
    List.count_pos_iff.mp (by omega)
  have data := List.mem_filter.mp projectedMember
  have sourceSimple : letters.count letter = 1 := by
    simpa [simpleKeep] using data.2
  have countBound :
      (simpleProjection letters).count letter ≤
        letters.count letter :=
    List.filter_sublist.count_le letter
  omega

/-- Deleting every globally multiple variable leaves exactly the same
ordered sequence of globally simple variables on both sides of a valid Q1
identity. This is the first half of Lee--Li's block alignment argument. -/
theorem valid_simpleProjection_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    simpleProjection identity.lhs.toList =
      simpleProjection identity.rhs.toList := by
  let same := valid_sameSimpleAdjacencySignature identity valid
  have keepEq :
      simpleKeep identity.lhs.toList =
        simpleKeep identity.rhs.toList :=
    simpleKeep_eq_of_sameSignature same
  by_cases leftEmpty : simpleProjection identity.lhs.toList = []
  · have rightEmpty : simpleProjection identity.rhs.toList = [] := by
      apply Decidable.byContradiction
      exact fun rightNonempty =>
        (simpleProjection_nonempty_iff same).mpr rightNonempty
          leftEmpty
    rw [leftEmpty, rightEmpty]
  · have rightNonempty :
        simpleProjection identity.rhs.toList ≠ [] :=
      (simpleProjection_nonempty_iff same).mp leftEmpty
    have leftFiltered :
        identity.lhs.toList.filter
            (simpleKeep identity.lhs.toList) =
          simpleProjection identity.lhs.toList := rfl
    have rightFiltered :
        identity.rhs.toList.filter
            (simpleKeep identity.lhs.toList) =
          simpleProjection identity.rhs.toList := by
      rw [keepEq]
      rfl
    have filteredSame :=
      valid_filtered_signature identity valid
        (simpleKeep identity.lhs.toList)
        (by simpa [leftFiltered] using leftEmpty)
        (by simpa [rightFiltered] using rightNonempty)
    have canonicalEqual := filteredSame.canonicalList_eq
    have leftNoMultiples :=
      sortedMultipleLetters_filter_simple_eq_nil
        identity.lhs.toList
    have rightNoMultiples :=
      sortedMultipleLetters_filter_simple_eq_nil
        identity.rhs.toList
    rw [toList_wordOfListOr_of_ne_nil _
          (by simpa [leftFiltered] using leftEmpty),
      toList_wordOfListOr_of_ne_nil _
          (by simpa [rightFiltered] using rightNonempty),
      leftFiltered, rightFiltered] at canonicalEqual
    simpa [S5_107.simpleAdjacencyCanonicalList,
      leftNoMultiples, rightNoMultiples] using canonicalEqual

/-! ## Separator lists carried by the public decomposition -/

private theorem repeatedGap_filter_simple_nil
    (whole gap : List Nat)
    (repeated : ∀ letter, letter ∈ gap →
      2 ≤ whole.count letter) :
    gap.filter (simpleKeep whole) = [] := by
  induction gap with
  | nil => rfl
  | cons letter rest induction =>
      have letterRepeated := repeated letter (by simp)
      have letterNotSimple : whole.count letter ≠ 1 := by omega
      simp [simpleKeep, letterNotSimple,
        induction (by
          intro tested member
          exact repeated tested (List.Mem.tail letter member))]

theorem separatorSequence_eq_simpleProjection
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole source segments finalGap) :
    segments.map Prod.snd =
      source.filter (simpleKeep whole) := by
  induction decomposition with
  | final gap gapRepeated =>
      simpa using
        repeatedGap_filter_simple_nil whole gap gapRepeated
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail induction =>
      have gapEmpty :=
        repeatedGap_filter_simple_nil whole gap gapRepeated
      simp [List.filter_append, gapEmpty, simpleKeep,
        separatorSimple, induction]

/-! ## Canonical gap support -/

private theorem sortedDistinctLetters_nodup (letters : List Nat) :
    (sortedDistinctLetters letters).Nodup :=
  (sortedDistinctLetters_perm letters).nodup_iff.mpr
    (S5_107.distinctLetters_nodup letters)

private theorem sortedDistinctLetters_pairwise (letters : List Nat) :
    (sortedDistinctLetters letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted :=
    List.pairwise_mergeSort transitive total
      (S5_107.distinctLetters letters)
  exact sorted.imp fun relation => of_decide_eq_true relation

theorem canonicalGap_eq_of_support
    (left right : List Nat)
    (support : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    canonicalGap left = canonicalGap right := by
  have permutation :
      (sortedDistinctLetters left).Perm
        (sortedDistinctLetters right) := by
    rw [List.perm_iff_count]
    intro tested
    rw [(sortedDistinctLetters_nodup left).count,
      (sortedDistinctLetters_nodup right).count]
    simp only [sortedDistinctLetters_mem_iff, support tested]
  have sortedEqual :
      sortedDistinctLetters left = sortedDistinctLetters right :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
      (sortedDistinctLetters_pairwise left)
      (sortedDistinctLetters_pairwise right)
      permutation
  simp [canonicalGap, sortedEqual]

/-! ## Boundary projections -/

def supportKeep
    (reference : List Nat) (tested letter : Nat) : Bool :=
  decide (letter = tested ∨ reference.count letter = 1)

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equal : first = letter
      · subst first
        simp [kept, induction]
      · by_cases firstKept : keep first
        · simp [firstKept, equal, induction]
        · simp [firstKept, equal, induction]

private theorem repeatedGap_filter_support_eq_nil_iff
    (reference whole gap : List Nat) (tested : Nat)
    (simpleAgreement : ∀ letter,
      reference.count letter = 1 ↔ whole.count letter = 1)
    (repeated : ∀ letter, letter ∈ gap →
      2 ≤ whole.count letter) :
    gap.filter (supportKeep reference tested) = [] ↔
      tested ∉ gap := by
  induction gap with
  | nil => simp
  | cons letter rest induction =>
      have letterRepeated := repeated letter (by simp)
      have wholeNotSimple : whole.count letter ≠ 1 := by omega
      have referenceNotSimple : reference.count letter ≠ 1 :=
        fun referenceSimple =>
          wholeNotSimple ((simpleAgreement letter).mp referenceSimple)
      by_cases equal : letter = tested
      · subst letter
        simp [supportKeep]
      · have tailRepeated :
            ∀ candidate, candidate ∈ rest →
              2 ≤ whole.count candidate := by
          intro candidate member
          exact repeated candidate (List.Mem.tail letter member)
        have reverseEqual : tested ≠ letter := Ne.symm equal
        simpa [supportKeep, equal, reverseEqual,
          referenceNotSimple] using
          induction tailRepeated

private theorem simpleInitial_iff_prefix_nil
    (word : Word Nat) (separator : Nat)
    (before after : List Nat)
    (shape : word.toList = before ++ separator :: after)
    (simple : word.toList.count separator = 1) :
    S5_107.SimpleInitial word separator ↔ before = [] := by
  constructor
  · intro initial
    have scanned :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := separator)
        (by simpa [S5_254.GloballySimple] using simple)
        before after shape
    have emptyScan :
        S5_254.simplePrefixBefore separator word.toList = [] := by
      cases word with
      | mk head tail =>
          simpa [Word.toList, S5_254.simplePrefixBefore]
            using initial.2
    rw [emptyScan] at scanned
    exact scanned.symm
  · intro empty
    subst before
    refine ⟨by simpa [S5_107.SimpleIn] using simple, ?_⟩
    cases word with
    | mk head tail =>
        simp only [Word.toList, List.nil_append] at shape
        injection shape

private theorem reverseAux_head_eq_getLastD (head : Nat) :
    ∀ tail : List Nat,
      (Word.reverseAux head tail).head = tail.getLastD head
  | [] => rfl
  | next :: rest => by
      change
        (Word.reverseAux next rest).head =
          (next :: rest).getLastD head
      rw [List.getLastD_cons]
      exact reverseAux_head_eq_getLastD next rest

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  cases word with
  | mk head tail =>
      exact reverseAux_head_eq_getLastD head tail

private theorem simpleInitial_reverse_iff_simpleFinal
    (word : Word Nat) (separator : Nat) :
    S5_107.SimpleInitial word.reverse separator ↔
      S5_107.SimpleFinal word separator := by
  simp [S5_107.SimpleInitial, S5_107.SimpleFinal,
    S5_107.SimpleIn, reverse_head_eq_final]

private theorem simpleFinal_iff_suffix_nil
    (word : Word Nat) (separator : Nat)
    (before after : List Nat)
    (shape : word.toList = before ++ separator :: after)
    (simple : word.toList.count separator = 1) :
    S5_107.SimpleFinal word separator ↔ after = [] := by
  have reversedShape :
      word.reverse.toList =
        after.reverse ++ separator :: before.reverse := by
    rw [Word.toList_reverse, shape]
    simp [List.reverse_append]
  have reversedSimple :
      word.reverse.toList.count separator = 1 := by
    simpa using simple
  calc
    S5_107.SimpleFinal word separator ↔
        S5_107.SimpleInitial word.reverse separator :=
      (simpleInitial_reverse_iff_simpleFinal word separator).symm
    _ ↔ after.reverse = [] :=
      simpleInitial_iff_prefix_nil word.reverse separator
        after.reverse before.reverse reversedShape reversedSimple
    _ ↔ after = [] := by simp

private theorem adjacentPair_iff_middle_nil
    (word : Word Nat) (source target : Nat)
    (before middle after : List Nat)
    (shape :
      word.toList =
        before ++ source :: (middle ++ target :: after))
    (sourceSimple : word.toList.count source = 1)
    (targetSimple : word.toList.count target = 1) :
    (source, target) ∈ word.adjacentPairs ↔ middle = [] := by
  constructor
  · intro adjacent
    obtain ⟨adjacentBefore, adjacentAfter, adjacentShape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word).mp adjacent
    have sourcePrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := source)
        (by simpa [S5_254.GloballySimple] using sourceSimple)
        before (middle ++ target :: after) shape
    have adjacentSourcePrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := source)
        (by simpa [S5_254.GloballySimple] using sourceSimple)
        adjacentBefore (target :: adjacentAfter) adjacentShape
    have beforeEq : before = adjacentBefore :=
      sourcePrefix.symm.trans adjacentSourcePrefix
    have targetShape :
        word.toList =
          (before ++ source :: middle) ++ target :: after := by
      simpa [List.append_assoc] using shape
    have adjacentTargetShape :
        word.toList =
          (adjacentBefore ++ [source]) ++ target :: adjacentAfter := by
      simpa [List.append_assoc] using adjacentShape
    have targetPrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := target)
        (by simpa [S5_254.GloballySimple] using targetSimple)
        (before ++ source :: middle) after targetShape
    have adjacentTargetPrefix :=
      S5_254.simplePrefixBefore_eq_of_split
        (word := word) (separator := target)
        (by simpa [S5_254.GloballySimple] using targetSimple)
        (adjacentBefore ++ [source]) adjacentAfter adjacentTargetShape
    have prefixEq :
        before ++ source :: middle =
          adjacentBefore ++ [source] :=
      targetPrefix.symm.trans adjacentTargetPrefix
    rw [← beforeEq] at prefixEq
    have tailEq : source :: middle = [source] :=
      List.append_cancel_left prefixEq
    simpa using tailEq
  · intro empty
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word).mpr
    exact ⟨before, after, by simpa [empty] using shape⟩

private theorem simple_count_agreement
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (letter : Nat) :
    left.toList.count letter = 1 ↔
      right.toList.count letter = 1 := by
  simpa [S5_107.SimpleIn] using same.simple letter

/-- Deletion to one repeated variable and the simple separators detects
whether that variable occurs before the first simple separator. -/
theorem valid_initialGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftGap rightGap leftRemainder rightRemainder : List Nat}
    {separator : Nat}
    (leftShape :
      identity.lhs.toList = leftGap ++ separator :: leftRemainder)
    (rightShape :
      identity.rhs.toList = rightGap ++ separator :: rightRemainder)
    (leftSeparatorSimple :
      identity.lhs.toList.count separator = 1)
    (rightSeparatorSimple :
      identity.rhs.toList.count separator = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  intro tested
  let same := valid_sameSimpleAdjacencySignature identity valid
  let keep := supportKeep identity.lhs.toList tested
  have agreement : ∀ letter,
      identity.lhs.toList.count letter = 1 ↔
        identity.rhs.toList.count letter = 1 :=
    simple_count_agreement same
  have separatorKept : keep separator = true := by
    simp [keep, supportKeep, leftSeparatorSimple]
  have leftSeparatorMember :
      separator ∈ identity.lhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), separatorKept⟩
  have rightSeparatorMember :
      separator ∈ identity.rhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), separatorKept⟩
  have leftNonempty : identity.lhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem leftSeparatorMember
  have rightNonempty : identity.rhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem rightSeparatorMember
  let leftWord :=
    wordOfListOr identity.lhs.head
      (identity.lhs.toList.filter keep)
  let rightWord :=
    wordOfListOr identity.rhs.head
      (identity.rhs.toList.filter keep)
  have leftWordList :
      leftWord.toList = identity.lhs.toList.filter keep := by
    simpa [leftWord] using
      toList_wordOfListOr_of_ne_nil identity.lhs.head leftNonempty
  have rightWordList :
      rightWord.toList = identity.rhs.toList.filter keep := by
    simpa [rightWord] using
      toList_wordOfListOr_of_ne_nil identity.rhs.head rightNonempty
  have filteredSame :
      S5_107.SameSimpleAdjacencySignature leftWord rightWord := by
    simpa [leftWord, rightWord] using
      valid_filtered_signature identity valid keep
        leftNonempty rightNonempty
  have leftWordSeparatorSimple :
      leftWord.toList.count separator = 1 := by
    calc
      leftWord.toList.count separator =
          (identity.lhs.toList.filter keep).count separator := by
        rw [leftWordList]
      _ = identity.lhs.toList.count separator :=
        count_filter_of_kept _ keep separator separatorKept
      _ = 1 := leftSeparatorSimple
  have rightWordSeparatorSimple :
      rightWord.toList.count separator = 1 := by
    calc
      rightWord.toList.count separator =
          (identity.rhs.toList.filter keep).count separator := by
        rw [rightWordList]
      _ = identity.rhs.toList.count separator :=
        count_filter_of_kept _ keep separator separatorKept
      _ = 1 := rightSeparatorSimple
  have leftProjectionShape :
      leftWord.toList =
        leftGap.filter keep ++ separator :: leftRemainder.filter keep := by
    rw [leftWordList, leftShape]
    simp [List.filter_append, separatorKept]
  have rightProjectionShape :
      rightWord.toList =
        rightGap.filter keep ++ separator :: rightRemainder.filter keep := by
    rw [rightWordList, rightShape]
    simp [List.filter_append, separatorKept]
  have leftInitial :
      S5_107.SimpleInitial leftWord separator ↔
        leftGap.filter keep = [] :=
    simpleInitial_iff_prefix_nil leftWord separator
      (leftGap.filter keep) (leftRemainder.filter keep)
      leftProjectionShape leftWordSeparatorSimple
  have rightInitial :
      S5_107.SimpleInitial rightWord separator ↔
        rightGap.filter keep = [] :=
    simpleInitial_iff_prefix_nil rightWord separator
      (rightGap.filter keep) (rightRemainder.filter keep)
      rightProjectionShape rightWordSeparatorSimple
  have leftNil :
      leftGap.filter keep = [] ↔ tested ∉ leftGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.lhs.toList leftGap tested
        (fun _ => Iff.rfl) leftRepeated
  have rightNil :
      rightGap.filter keep = [] ↔ tested ∉ rightGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.rhs.toList rightGap tested
        agreement rightRepeated
  have absence : tested ∉ leftGap ↔ tested ∉ rightGap := by
    calc
      tested ∉ leftGap ↔ leftGap.filter keep = [] := leftNil.symm
      _ ↔ S5_107.SimpleInitial leftWord separator := leftInitial.symm
      _ ↔ S5_107.SimpleInitial rightWord separator :=
        filteredSame.initial separator
      _ ↔ rightGap.filter keep = [] := rightInitial
      _ ↔ tested ∉ rightGap := rightNil
  simpa using not_congr absence

/-- Between two consecutive simple separators, deletion detects absence of a
repeated variable exactly as adjacency of those separators. -/
theorem valid_interiorGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftBefore rightBefore leftGap rightGap leftAfter rightAfter : List Nat}
    {previous current : Nat}
    (leftShape :
      identity.lhs.toList =
        leftBefore ++ previous :: (leftGap ++ current :: leftAfter))
    (rightShape :
      identity.rhs.toList =
        rightBefore ++ previous :: (rightGap ++ current :: rightAfter))
    (leftPreviousSimple :
      identity.lhs.toList.count previous = 1)
    (rightPreviousSimple :
      identity.rhs.toList.count previous = 1)
    (leftCurrentSimple :
      identity.lhs.toList.count current = 1)
    (rightCurrentSimple :
      identity.rhs.toList.count current = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  intro tested
  let same := valid_sameSimpleAdjacencySignature identity valid
  let keep := supportKeep identity.lhs.toList tested
  have agreement : ∀ letter,
      identity.lhs.toList.count letter = 1 ↔
        identity.rhs.toList.count letter = 1 :=
    simple_count_agreement same
  have previousKept : keep previous = true := by
    simp [keep, supportKeep, leftPreviousSimple]
  have currentKept : keep current = true := by
    simp [keep, supportKeep, leftCurrentSimple]
  have leftPreviousMember :
      previous ∈ identity.lhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), previousKept⟩
  have rightPreviousMember :
      previous ∈ identity.rhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), previousKept⟩
  have leftNonempty : identity.lhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem leftPreviousMember
  have rightNonempty : identity.rhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem rightPreviousMember
  let leftWord :=
    wordOfListOr identity.lhs.head
      (identity.lhs.toList.filter keep)
  let rightWord :=
    wordOfListOr identity.rhs.head
      (identity.rhs.toList.filter keep)
  have leftWordList :
      leftWord.toList = identity.lhs.toList.filter keep := by
    simpa [leftWord] using
      toList_wordOfListOr_of_ne_nil identity.lhs.head leftNonempty
  have rightWordList :
      rightWord.toList = identity.rhs.toList.filter keep := by
    simpa [rightWord] using
      toList_wordOfListOr_of_ne_nil identity.rhs.head rightNonempty
  have filteredSame :
      S5_107.SameSimpleAdjacencySignature leftWord rightWord := by
    simpa [leftWord, rightWord] using
      valid_filtered_signature identity valid keep
        leftNonempty rightNonempty
  have leftWordPreviousSimple :
      leftWord.toList.count previous = 1 := by
    calc
      leftWord.toList.count previous =
          (identity.lhs.toList.filter keep).count previous := by
        rw [leftWordList]
      _ = identity.lhs.toList.count previous :=
        count_filter_of_kept _ keep previous previousKept
      _ = 1 := leftPreviousSimple
  have rightWordPreviousSimple :
      rightWord.toList.count previous = 1 := by
    calc
      rightWord.toList.count previous =
          (identity.rhs.toList.filter keep).count previous := by
        rw [rightWordList]
      _ = identity.rhs.toList.count previous :=
        count_filter_of_kept _ keep previous previousKept
      _ = 1 := rightPreviousSimple
  have leftWordCurrentSimple :
      leftWord.toList.count current = 1 := by
    calc
      leftWord.toList.count current =
          (identity.lhs.toList.filter keep).count current := by
        rw [leftWordList]
      _ = identity.lhs.toList.count current :=
        count_filter_of_kept _ keep current currentKept
      _ = 1 := leftCurrentSimple
  have rightWordCurrentSimple :
      rightWord.toList.count current = 1 := by
    calc
      rightWord.toList.count current =
          (identity.rhs.toList.filter keep).count current := by
        rw [rightWordList]
      _ = identity.rhs.toList.count current :=
        count_filter_of_kept _ keep current currentKept
      _ = 1 := rightCurrentSimple
  have leftProjectionShape :
      leftWord.toList =
        leftBefore.filter keep ++ previous ::
          (leftGap.filter keep ++ current :: leftAfter.filter keep) := by
    rw [leftWordList, leftShape]
    simp [List.filter_append, previousKept, currentKept]
  have rightProjectionShape :
      rightWord.toList =
        rightBefore.filter keep ++ previous ::
          (rightGap.filter keep ++ current :: rightAfter.filter keep) := by
    rw [rightWordList, rightShape]
    simp [List.filter_append, previousKept, currentKept]
  have leftPair :
      (previous, current) ∈ leftWord.adjacentPairs ↔
        leftGap.filter keep = [] :=
    adjacentPair_iff_middle_nil leftWord previous current
      (leftBefore.filter keep) (leftGap.filter keep)
      (leftAfter.filter keep) leftProjectionShape
      leftWordPreviousSimple leftWordCurrentSimple
  have rightPair :
      (previous, current) ∈ rightWord.adjacentPairs ↔
        rightGap.filter keep = [] :=
    adjacentPair_iff_middle_nil rightWord previous current
      (rightBefore.filter keep) (rightGap.filter keep)
      (rightAfter.filter keep) rightProjectionShape
      rightWordPreviousSimple rightWordCurrentSimple
  have leftAdjacent :
      S5_107.SimpleAdjacent leftWord previous current ↔
        leftGap.filter keep = [] := by
    simpa [S5_107.SimpleAdjacent, S5_107.SimpleIn,
      leftWordPreviousSimple, leftWordCurrentSimple] using leftPair
  have rightAdjacent :
      S5_107.SimpleAdjacent rightWord previous current ↔
        rightGap.filter keep = [] := by
    simpa [S5_107.SimpleAdjacent, S5_107.SimpleIn,
      rightWordPreviousSimple, rightWordCurrentSimple] using rightPair
  have leftNil :
      leftGap.filter keep = [] ↔ tested ∉ leftGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.lhs.toList leftGap tested
        (fun _ => Iff.rfl) leftRepeated
  have rightNil :
      rightGap.filter keep = [] ↔ tested ∉ rightGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.rhs.toList rightGap tested
        agreement rightRepeated
  have absence : tested ∉ leftGap ↔ tested ∉ rightGap := by
    calc
      tested ∉ leftGap ↔ leftGap.filter keep = [] := leftNil.symm
      _ ↔ S5_107.SimpleAdjacent leftWord previous current :=
        leftAdjacent.symm
      _ ↔ S5_107.SimpleAdjacent rightWord previous current :=
        filteredSame.adjacent previous current
      _ ↔ rightGap.filter keep = [] := rightAdjacent
      _ ↔ tested ∉ rightGap := rightNil
  simpa using not_congr absence

/-- Deletion detects whether a repeated variable occurs after the final
globally simple separator. -/
theorem valid_finalGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftBefore rightBefore leftGap rightGap : List Nat}
    {separator : Nat}
    (leftShape :
      identity.lhs.toList = leftBefore ++ separator :: leftGap)
    (rightShape :
      identity.rhs.toList = rightBefore ++ separator :: rightGap)
    (leftSeparatorSimple :
      identity.lhs.toList.count separator = 1)
    (rightSeparatorSimple :
      identity.rhs.toList.count separator = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  intro tested
  let same := valid_sameSimpleAdjacencySignature identity valid
  let keep := supportKeep identity.lhs.toList tested
  have agreement : ∀ letter,
      identity.lhs.toList.count letter = 1 ↔
        identity.rhs.toList.count letter = 1 :=
    simple_count_agreement same
  have separatorKept : keep separator = true := by
    simp [keep, supportKeep, leftSeparatorSimple]
  have leftSeparatorMember :
      separator ∈ identity.lhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), separatorKept⟩
  have rightSeparatorMember :
      separator ∈ identity.rhs.toList.filter keep :=
    List.mem_filter.mpr
      ⟨List.count_pos_iff.mp (by omega), separatorKept⟩
  have leftNonempty : identity.lhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem leftSeparatorMember
  have rightNonempty : identity.rhs.toList.filter keep ≠ [] :=
    List.ne_nil_of_mem rightSeparatorMember
  let leftWord :=
    wordOfListOr identity.lhs.head
      (identity.lhs.toList.filter keep)
  let rightWord :=
    wordOfListOr identity.rhs.head
      (identity.rhs.toList.filter keep)
  have leftWordList :
      leftWord.toList = identity.lhs.toList.filter keep := by
    simpa [leftWord] using
      toList_wordOfListOr_of_ne_nil identity.lhs.head leftNonempty
  have rightWordList :
      rightWord.toList = identity.rhs.toList.filter keep := by
    simpa [rightWord] using
      toList_wordOfListOr_of_ne_nil identity.rhs.head rightNonempty
  have filteredSame :
      S5_107.SameSimpleAdjacencySignature leftWord rightWord := by
    simpa [leftWord, rightWord] using
      valid_filtered_signature identity valid keep
        leftNonempty rightNonempty
  have leftWordSeparatorSimple :
      leftWord.toList.count separator = 1 := by
    calc
      leftWord.toList.count separator =
          (identity.lhs.toList.filter keep).count separator := by
        rw [leftWordList]
      _ = identity.lhs.toList.count separator :=
        count_filter_of_kept _ keep separator separatorKept
      _ = 1 := leftSeparatorSimple
  have rightWordSeparatorSimple :
      rightWord.toList.count separator = 1 := by
    calc
      rightWord.toList.count separator =
          (identity.rhs.toList.filter keep).count separator := by
        rw [rightWordList]
      _ = identity.rhs.toList.count separator :=
        count_filter_of_kept _ keep separator separatorKept
      _ = 1 := rightSeparatorSimple
  have leftProjectionShape :
      leftWord.toList =
        leftBefore.filter keep ++ separator :: leftGap.filter keep := by
    rw [leftWordList, leftShape]
    simp [List.filter_append, separatorKept]
  have rightProjectionShape :
      rightWord.toList =
        rightBefore.filter keep ++ separator :: rightGap.filter keep := by
    rw [rightWordList, rightShape]
    simp [List.filter_append, separatorKept]
  have leftFinal :
      S5_107.SimpleFinal leftWord separator ↔
        leftGap.filter keep = [] :=
    simpleFinal_iff_suffix_nil leftWord separator
      (leftBefore.filter keep) (leftGap.filter keep)
      leftProjectionShape leftWordSeparatorSimple
  have rightFinal :
      S5_107.SimpleFinal rightWord separator ↔
        rightGap.filter keep = [] :=
    simpleFinal_iff_suffix_nil rightWord separator
      (rightBefore.filter keep) (rightGap.filter keep)
      rightProjectionShape rightWordSeparatorSimple
  have leftNil :
      leftGap.filter keep = [] ↔ tested ∉ leftGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.lhs.toList leftGap tested
        (fun _ => Iff.rfl) leftRepeated
  have rightNil :
      rightGap.filter keep = [] ↔ tested ∉ rightGap := by
    simpa [keep] using
      repeatedGap_filter_support_eq_nil_iff
        identity.lhs.toList identity.rhs.toList rightGap tested
        agreement rightRepeated
  have absence : tested ∉ leftGap ↔ tested ∉ rightGap := by
    calc
      tested ∉ leftGap ↔ leftGap.filter keep = [] := leftNil.symm
      _ ↔ S5_107.SimpleFinal leftWord separator := leftFinal.symm
      _ ↔ S5_107.SimpleFinal rightWord separator :=
        filteredSame.final separator
      _ ↔ rightGap.filter keep = [] := rightFinal
      _ ↔ tested ∉ rightGap := rightNil
  simpa using not_congr absence

/-! ## Alignment of normalized separator decompositions -/

private theorem renderCanonicalSeparatorDecomposition_eq_after
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.lhs.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.rhs.toList rightSource rightSegments rightFinal)
    (previous : Nat)
    (leftPreviousSimple :
      identity.lhs.toList.count previous = 1)
    (rightPreviousSimple :
      identity.rhs.toList.count previous = 1)
    (leftBefore rightBefore : List Nat)
    (leftShape :
      identity.lhs.toList = leftBefore ++ previous :: leftSource)
    (rightShape :
      identity.rhs.toList = rightBefore ++ previous :: rightSource)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderCanonicalSeparatorDecomposition leftSegments leftFinal =
      renderCanonicalSeparatorDecomposition rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal previous leftBefore rightBefore with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          have support :=
            valid_finalGap_support_iff identity valid
              leftShape rightShape
              leftPreviousSimple rightPreviousSimple
              leftRepeated rightRepeated
          have gapEq :=
            canonicalGap_eq_of_support leftGap rightSource support
          simpa [renderCanonicalSeparatorDecomposition, gapEq]
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail leftInduction =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have support :=
            valid_interiorGap_support_iff identity valid
              leftShape rightShape
              leftPreviousSimple rightPreviousSimple
              leftSeparatorSimple rightSeparatorSimple
              leftRepeated rightRepeated
          have gapEq :=
            canonicalGap_eq_of_support leftGap rightGap support
          have leftTailShape :
              identity.lhs.toList =
                (leftBefore ++ previous :: leftGap) ++
                  leftSeparator :: leftRemainder := by
            simpa [List.append_assoc] using leftShape
          have rightTailShape :
              identity.rhs.toList =
                (rightBefore ++ previous :: rightGap) ++
                  leftSeparator :: rightRemainder := by
            simpa [List.append_assoc] using rightShape
          have tailEq :=
            leftInduction rightTail leftSeparator
              leftSeparatorSimple rightSeparatorSimple
              (leftBefore ++ previous :: leftGap)
              (rightBefore ++ previous :: rightGap)
              leftTailShape rightTailShape separatorTailEq
          simp [renderCanonicalSeparatorDecomposition, gapEq, tailEq]

private theorem renderCanonicalSeparatorDecomposition_eq_from_start
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.lhs.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.rhs.toList rightSource rightSegments rightFinal)
    (leftShape : identity.lhs.toList = leftSource)
    (rightShape : identity.rhs.toList = rightSource)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderCanonicalSeparatorDecomposition leftSegments leftFinal =
      renderCanonicalSeparatorDecomposition rightSegments rightFinal := by
  cases leftDecomposition with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          have same := valid_sameSimpleAdjacencySignature identity valid
          have support :
              ∀ tested, tested ∈ leftSource ↔ tested ∈ rightSource := by
            intro tested
            rw [← leftShape, ← rightShape]
            exact same.support tested
          have gapEq :=
            canonicalGap_eq_of_support leftSource rightSource support
          simpa [renderCanonicalSeparatorDecomposition, gapEq]
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          obtain ⟨separatorHeadEq, separatorTailEq⟩ := separatorEq
          subst rightSeparator
          have support :=
            valid_initialGap_support_iff identity valid
              leftShape rightShape
              leftSeparatorSimple rightSeparatorSimple
              leftRepeated rightRepeated
          have gapEq :=
            canonicalGap_eq_of_support leftGap rightGap support
          have leftTailShape :
              identity.lhs.toList =
                leftGap ++ leftSeparator :: leftRemainder :=
            leftShape
          have rightTailShape :
              identity.rhs.toList =
                rightGap ++ leftSeparator :: rightRemainder :=
            rightShape
          have tailEq :=
            renderCanonicalSeparatorDecomposition_eq_after
              identity valid leftTail rightTail leftSeparator
              leftSeparatorSimple rightSeparatorSimple
              leftGap rightGap leftTailShape rightTailShape
              separatorTailEq
          simp [renderCanonicalSeparatorDecomposition, gapEq, tailEq]

/-- The semantic deletion certificates align every repeated-variable gap in
two separator decompositions of a valid Q1 identity. -/
theorem valid_canonicalSeparatorDecomposition_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.lhs.toList identity.lhs.toList
          leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.rhs.toList identity.rhs.toList
          rightSegments rightFinal) :
    renderCanonicalSeparatorDecomposition leftSegments leftFinal =
      renderCanonicalSeparatorDecomposition rightSegments rightFinal := by
  have separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd =
          simpleProjection identity.lhs.toList := by
        simpa [simpleProjection] using
          separatorSequence_eq_simpleProjection leftDecomposition
      _ = simpleProjection identity.rhs.toList :=
        valid_simpleProjection_eq identity valid
      _ = rightSegments.map Prod.snd := by
        simpa [simpleProjection] using
          (separatorSequence_eq_simpleProjection rightDecomposition).symm
  exact renderCanonicalSeparatorDecomposition_eq_from_start
    identity valid leftDecomposition rightDecomposition
      rfl rfl separatorEq

/-! ## Unconditional completeness -/

/-- Every identity valid in the exact six-element Q1 table follows from the
four Lee--Li identities. -/
theorem derives_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftSegments, leftFinal, leftDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition
      identity.lhs.toList
  obtain ⟨rightSegments, rightFinal, rightDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition
      identity.rhs.toList
  have leftNormal :=
    listDerivesNormalizeSeparatorDecomposition
      identity.lhs.toList leftDecomposition
  have rightNormal :=
    listDerivesNormalizeSeparatorDecomposition
      identity.rhs.toList rightDecomposition
  have canonicalEq :=
    valid_canonicalSeparatorDecomposition_eq identity valid
      leftDecomposition rightDecomposition
  have middle :
      ListDerives
        (renderCanonicalSeparatorDecomposition
          leftSegments leftFinal)
        (renderCanonicalSeparatorDecomposition
          rightSegments rightFinal) := by
    rw [canonicalEq]
    exact S5_107.ListDerives.refl _
  have combined :
      ListDerives identity.lhs.toList identity.rhs.toList :=
    leftNormal.trans (middle.trans rightNormal.symm)
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              exact S5_107.ListDerives.toWord combined

/-- Catalogue-facing unconditional Lee--Li Proposition 4.3 basis theorem
for the exact direct `S6_3944` table. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_valid identity valid

end SemigroupBasis.CoRoots.S6_3944
