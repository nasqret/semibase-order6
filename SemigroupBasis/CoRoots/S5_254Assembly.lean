import SemigroupBasis.CoRoots.S5_107BlockCombinatorics
import SemigroupBasis.CoRoots.S5_254PairExtraction

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## Deterministic gap residues -/

private def parityResidueInput (gap : List Nat) : List Nat :=
  (S5_107.distinctLetters gap).filter
    (fun letter => decide (gap.count letter % 2 = 1))

/-- The sorted set of letters occurring oddly often in one separator gap. -/
def canonicalGapParityResidue (gap : List Nat) : List Nat :=
  (parityResidueInput gap).mergeSort
    (fun left right => decide (left ≤ right))

private theorem parityResidueInput_nodup (gap : List Nat) :
    (parityResidueInput gap).Nodup := by
  exact
    (S5_107.distinctLetters_nodup gap).filter
      (fun letter => decide (gap.count letter % 2 = 1))

private theorem parityResidueInput_mem_iff
    (gap : List Nat) (letter : Nat) :
    letter ∈ parityResidueInput gap ↔ gap.count letter % 2 = 1 := by
  simp [parityResidueInput, S5_107.distinctLetters_mem_iff]
  intro odd
  exact List.count_pos_iff.mp (by omega)

private theorem parityResidueInput_count
    (gap : List Nat) (letter : Nat) :
    (parityResidueInput gap).count letter = gap.count letter % 2 := by
  have nodup := parityResidueInput_nodup gap
  rw [nodup.count]
  simp only [parityResidueInput_mem_iff]
  by_cases odd : gap.count letter % 2 = 1
  · simp [odd]
  · have even : gap.count letter % 2 = 0 := by omega
    simp [odd, even]

private theorem natMergeSort_pairwise (letters : List Nat) :
    (letters.mergeSort
      (fun left right => decide (left ≤ right))).Pairwise (· ≤ ·) := by
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
  have sorted := List.pairwise_mergeSort transitive total letters
  exact sorted.imp fun relation => of_decide_eq_true relation

theorem canonicalGapParityResidue_pairwise (gap : List Nat) :
    (canonicalGapParityResidue gap).Pairwise (· ≤ ·) := by
  exact natMergeSort_pairwise (parityResidueInput gap)

/-- Gap parity profiles determine the deterministic residue literally. -/
theorem canonicalGapParityResidue_eq_of_parity
    (left right : List Nat)
    (sameParity : ∀ tested,
      left.count tested % 2 = right.count tested % 2) :
    canonicalGapParityResidue left =
      canonicalGapParityResidue right := by
  have permutation :
      (canonicalGapParityResidue left).Perm
        (canonicalGapParityResidue right) := by
    rw [List.perm_iff_count]
    intro tested
    have leftCount :=
      (List.mergeSort_perm
        (parityResidueInput left)
        (fun first second : Nat => decide (first ≤ second))).count tested
    have rightCount :=
      (List.mergeSort_perm
        (parityResidueInput right)
        (fun first second : Nat => decide (first ≤ second))).count tested
    change
      List.count tested
          ((parityResidueInput left).mergeSort
            (fun first second => decide (first ≤ second))) =
        List.count tested
          ((parityResidueInput right).mergeSort
            (fun first second => decide (first ≤ second)))
    rw [leftCount, rightCount, parityResidueInput_count,
      parityResidueInput_count, sameParity tested]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (canonicalGapParityResidue_pairwise left)
    (canonicalGapParityResidue_pairwise right)
    permutation

theorem canonicalGapResidue_pairwise (residue : List Nat) :
    (canonicalGapResidue residue).Pairwise (· ≤ ·) := by
  exact natMergeSort_pairwise residue

/-- Any one-limited residue with the correct parity sorts to the deterministic
gap residue. -/
theorem canonicalGapResidue_eq_parityResidue
    (gap residue : List Nat)
    (parity :
      ∀ tested, residue.count tested = gap.count tested % 2) :
    canonicalGapResidue residue = canonicalGapParityResidue gap := by
  have permutation :
      (canonicalGapResidue residue).Perm
        (canonicalGapParityResidue gap) := by
    rw [List.perm_iff_count]
    intro tested
    have leftCount :=
      (List.mergeSort_perm
        residue (fun left right : Nat => decide (left ≤ right))).count tested
    have rightCount :=
      (List.mergeSort_perm
        (parityResidueInput gap)
        (fun left right : Nat => decide (left ≤ right))).count tested
    change
      List.count tested
          (residue.mergeSort
            (fun left right => decide (left ≤ right))) =
        List.count tested
          ((parityResidueInput gap).mergeSort
            (fun left right => decide (left ≤ right)))
    rw [leftCount, rightCount, parity tested,
      parityResidueInput_count]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (canonicalGapResidue_pairwise residue)
    (canonicalGapParityResidue_pairwise gap)
    permutation

@[simp]
theorem count_renderSquareBank (labels : List Nat) (tested : Nat) :
    (renderSquareBank labels).count tested = 2 * labels.count tested := by
  induction labels with
  | nil => simp [renderSquareBank]
  | cons letter labels induction =>
      rw [show renderSquareBank (letter :: labels) =
        [letter, letter] ++ renderSquareBank labels by rfl]
      rw [List.count_append, induction]
      by_cases equal : tested = letter
      · subst tested
        simp
        omega
      · have reverse : letter ≠ tested := Ne.symm equal
        simp [equal, reverse]

/-- Normalize one gap to its deterministic sorted parity residue while
retaining the raw, multiplicity-exact square bank. Delaying bank
deduplication preserves the count invariant needed by later gaps. This is the
exact-count refinement of `listDerivesCanonicalSeparatorGap`: after invoking
that theorem, it reverses only the local bank canonicalization. -/
theorem listDerivesSortedSeparatorGapRawBank
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ labels,
      ListDerives
        (prefixWords ++ gap ++ suffix)
        (prefixWords ++ canonicalGapParityResidue gap ++
          renderSquareBank labels ++ suffix) ∧
        ∀ tested,
          gap.count tested =
            (canonicalGapParityResidue gap).count tested +
              2 * labels.count tested := by
  obtain ⟨residue, labels, normalized, counts, _residueLimited,
      residueParity⟩ :=
    listDerivesCanonicalSeparatorGap
      prefixWords gap suffix globallyRepeated
  have canonicalEq :=
    canonicalGapResidue_eq_parityResidue gap residue residueParity
  have expandedBank :=
    S5_107.ListDerives.context
      (basis := basis)
      (prefixWords ++ canonicalGapParityResidue gap) suffix
      (listDerivesCanonicalSquareBank labels).symm
  refine ⟨labels, normalized.trans ?_, ?_⟩
  · simpa [canonicalEq, List.append_assoc] using expandedBank
  · intro tested
    have sortedCount :
        (canonicalGapParityResidue gap).count tested =
          residue.count tested := by
        rw [← canonicalEq]
        exact
          (List.mergeSort_perm
            residue
            (fun left right : Nat => decide (left ≤ right))).count tested
    rw [sortedCount]
    exact counts tested

/-! ## Multi-gap assembly with exact counts -/

/-- Render deterministic parity residues in the separator order carried by a
whole-word decomposition. -/
def renderCanonicalSeparatorSkeleton :
    List (List Nat × Nat) → List Nat → List Nat
  | [], finalGap => canonicalGapParityResidue finalGap
  | (gap, separator) :: segments, finalGap =>
      canonicalGapParityResidue gap ++
        separator :: renderCanonicalSeparatorSkeleton segments finalGap

private theorem listDerivesRawSeparatorAssemblyContext
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      GloballySimpleSeparatorDecomposition
        whole source segments finalGap)
    (prefixWords suffix : List Nat)
    (countInvariant : ∀ tested,
      (prefixWords ++ source ++ suffix).count tested = whole.count tested) :
    ∃ labels,
      ListDerives
        (prefixWords ++ source ++ suffix)
        (prefixWords ++
          renderCanonicalSeparatorSkeleton segments finalGap ++
          renderSquareBank labels ++ suffix) ∧
        ∀ tested,
          (prefixWords ++
            renderCanonicalSeparatorSkeleton segments finalGap ++
            renderSquareBank labels ++ suffix).count tested =
              whole.count tested := by
  induction decomposition generalizing prefixWords suffix with
  | final gap gapRepeated =>
      have globallyRepeated : ∀ letter, letter ∈ gap →
          2 ≤ (prefixWords ++ gap ++ suffix).count letter := by
        intro letter member
        rw [countInvariant letter]
        exact gapRepeated letter member
      obtain ⟨labels, normalized, gapCounts⟩ :=
        listDerivesSortedSeparatorGapRawBank
          prefixWords gap suffix globallyRepeated
      refine ⟨labels, ?_, ?_⟩
      · simpa [renderCanonicalSeparatorSkeleton,
          List.append_assoc] using normalized
      · intro tested
        have originalCount := countInvariant tested
        have gapCount := gapCounts tested
        simp only [renderCanonicalSeparatorSkeleton,
          List.count_append, count_renderSquareBank] at originalCount ⊢
        omega
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail tailInduction =>
      have globallyRepeated : ∀ letter, letter ∈ gap →
          2 ≤
            (prefixWords ++ gap ++
              ((separator :: remainder) ++ suffix)).count letter := by
        intro letter member
        have original :
            (prefixWords ++ gap ++
              ((separator :: remainder) ++ suffix)).count letter =
                whole.count letter := by
          simpa [List.append_assoc] using countInvariant letter
        have repeated := gapRepeated letter member
        rw [original]
        exact repeated
      obtain ⟨headLabels, headNormalized, headCounts⟩ :=
        listDerivesSortedSeparatorGapRawBank
          prefixWords gap ((separator :: remainder) ++ suffix)
            globallyRepeated
      have movedHeadBank :=
        listDerivesSquareBankAcrossContext
          (prefixWords ++ canonicalGapParityResidue gap)
          headLabels (separator :: remainder) suffix
      have headStep :
          ListDerives
            (prefixWords ++ (gap ++ separator :: remainder) ++ suffix)
            ((prefixWords ++ canonicalGapParityResidue gap ++ [separator]) ++
              remainder ++ renderSquareBank headLabels ++ suffix) := by
        have normalizedHead :
            ListDerives
              (prefixWords ++ (gap ++ separator :: remainder) ++ suffix)
              (prefixWords ++ canonicalGapParityResidue gap ++
                renderSquareBank headLabels ++
                  ((separator :: remainder) ++ suffix)) := by
          simpa [List.append_assoc] using headNormalized
        have movedHeadBank' :
            ListDerives
              (prefixWords ++ canonicalGapParityResidue gap ++
                renderSquareBank headLabels ++
                  ((separator :: remainder) ++ suffix))
              ((prefixWords ++ canonicalGapParityResidue gap ++ [separator]) ++
                remainder ++ renderSquareBank headLabels ++ suffix) := by
          simpa [List.append_assoc] using movedHeadBank
        exact normalizedHead.trans movedHeadBank'
      have nextCountInvariant : ∀ tested,
          (((prefixWords ++ canonicalGapParityResidue gap ++ [separator]) ++
              remainder) ++
              (renderSquareBank headLabels ++ suffix)).count tested =
            whole.count tested := by
        intro tested
        have originalCount := countInvariant tested
        have gapCount := headCounts tested
        simp only [List.count_append, List.count_cons,
          List.count_nil, count_renderSquareBank] at originalCount ⊢
        omega
      obtain ⟨tailLabels, tailStep, tailCounts⟩ :=
        tailInduction
          (prefixWords ++ canonicalGapParityResidue gap ++ [separator])
          (renderSquareBank headLabels ++ suffix)
          nextCountInvariant
      have tailStep' :
          ListDerives
            ((prefixWords ++ canonicalGapParityResidue gap ++ [separator]) ++
              remainder ++ renderSquareBank headLabels ++ suffix)
            (prefixWords ++
              renderCanonicalSeparatorSkeleton
                ((gap, separator) :: segments) finalGap ++
              renderSquareBank (tailLabels ++ headLabels) ++ suffix) := by
        simpa [renderCanonicalSeparatorSkeleton, renderSquareBank,
          List.flatMap_append, List.append_assoc] using tailStep
      refine ⟨tailLabels ++ headLabels, headStep.trans tailStep', ?_⟩
      intro tested
      simpa [renderCanonicalSeparatorSkeleton, renderSquareBank,
        List.flatMap_append, List.append_assoc] using tailCounts tested

/-- Normalize every gap in one whole-word decomposition, move every raw local
bank to the global right boundary, and preserve exact occurrence counts. -/
theorem listDerivesRawSeparatorAssembly
    {whole : List Nat} {segments : List (List Nat × Nat)}
    {finalGap : List Nat}
    (decomposition :
      GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ∃ labels,
      ListDerives whole
        (renderCanonicalSeparatorSkeleton segments finalGap ++
          renderSquareBank labels) ∧
        ∀ tested,
          (renderCanonicalSeparatorSkeleton segments finalGap ++
            renderSquareBank labels).count tested = whole.count tested := by
  simpa using
    listDerivesRawSeparatorAssemblyContext
      decomposition [] [] (by simp)

/-! ## Global square ownership -/

private def instantiatePairInsertion
    (letter middle : Word Nat) : Nat → Word Nat
  | 0 => letter
  | 1 => middle
  | n + 2 => Word.singleton (n + 2)

private theorem existsRepeatedLetterSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equal : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, shape⟩ :=
          List.mem_iff_append.mp (List.count_pos_iff.mp restPositive)
        exact ⟨[], middle, after, by simp [shape, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equal] using count
        obtain ⟨before, middle, after, shape⟩ :=
          existsRepeatedLetterSplit letter restCount
        exact
          ⟨first :: before, middle, after,
            by simp [shape, List.append_assoc]⟩

private theorem listDerivesExpandRepeatedInterval
    (letter : Nat) (middle : List Nat) :
    ListDerives
      (letter :: middle ++ [letter])
      ([letter, letter] ++ letter :: middle ++ [letter]) := by
  cases middle with
  | nil =>
      simpa using
        (listDerivesDuplicatePairContraction letter).symm
  | cons middleHead middleTail =>
      exact S5_107.ListDerives.words <| by
        have expanded :=
          (derivesSandwichContractionSubstitution
            (instantiatePairInsertion
              (Word.singleton letter)
              (S5_107.listWordOfCons middleHead middleTail))).symm
        simpa [xyx, xxxyx, instantiatePairInsertion,
          S5_107.listWordOfCons, Word.bind, Word.append,
          Word.singleton, Word.append_assoc, List.append_assoc] using
            expanded

/-- Any displayed word with two occurrences of `letter` derives to itself
with one new adjacent square appended at the global right boundary. -/
theorem listDerivesAppendPairOfCountGeTwo
    (letters : List Nat) (letter : Nat)
    (repeated : 2 ≤ letters.count letter) :
    ListDerives letters (letters ++ [letter, letter]) := by
  obtain ⟨before, middle, after, shape⟩ :=
    existsRepeatedLetterSplit letter repeated
  have expanded :=
    S5_107.ListDerives.context
      (basis := basis) before after
      (listDerivesExpandRepeatedInterval letter middle)
  have moved :=
    listDerivesPairAcrossContext before letter
      (letter :: middle ++ letter :: after) []
  rw [shape]
  have expandedStep :
      ListDerives
        (before ++ letter :: middle ++ letter :: after)
        (before ++ [letter, letter] ++
          (letter :: middle ++ letter :: after)) := by
    simpa [List.append_assoc] using expanded
  have movedStep :
      ListDerives
        (before ++ [letter, letter] ++
          (letter :: middle ++ letter :: after))
        ((before ++ letter :: middle ++ letter :: after) ++
          [letter, letter]) := by
    simpa [List.append_assoc] using moved
  exact expandedStep.trans movedStep

/-- Append one movable square for every requested label. The hypothesis is
measured in the original source; earlier insertions only increase counts. -/
theorem listDerivesAppendSquareBank
    (source labels : List Nat)
    (repeated : ∀ letter, letter ∈ labels →
      2 ≤ source.count letter) :
    ListDerives source (source ++ renderSquareBank labels) := by
  induction labels generalizing source with
  | nil =>
      simpa [renderSquareBank] using
        S5_107.ListDerives.refl (basis := basis) source
  | cons letter labels induction =>
      have letterRepeated : 2 ≤ source.count letter :=
        repeated letter (by simp)
      have inserted :=
        listDerivesAppendPairOfCountGeTwo
          source letter letterRepeated
      have tailRepeated : ∀ tested, tested ∈ labels →
          2 ≤ (source ++ [letter, letter]).count tested := by
        intro tested member
        have original := repeated tested (List.Mem.tail letter member)
        simp only [List.count_append]
        omega
      have tail :=
        induction (source ++ [letter, letter]) tailRepeated
      exact inserted.trans <| by
        simpa [renderSquareBank, List.append_assoc] using tail

/-! ## Canonical global bank -/

theorem mem_deduplicateSquareBank_iff
    (tested : Nat) : ∀ labels : List Nat,
      tested ∈ deduplicateSquareBank labels ↔ tested ∈ labels
  | [] => by simp [deduplicateSquareBank]
  | letter :: labels => by
      by_cases present : letter ∈ labels
      · simp [deduplicateSquareBank, present,
          mem_deduplicateSquareBank_iff tested labels]
        intro equal
        subst tested
        exact present
      · simp [deduplicateSquareBank, present,
          mem_deduplicateSquareBank_iff tested labels]

theorem deduplicateSquareBank_nodup :
    ∀ labels : List Nat, (deduplicateSquareBank labels).Nodup
  | [] => by simp [deduplicateSquareBank]
  | letter :: labels => by
      by_cases present : letter ∈ labels
      · simpa [deduplicateSquareBank, present] using
          deduplicateSquareBank_nodup labels
      · have absent : letter ∉ deduplicateSquareBank labels := by
          rw [mem_deduplicateSquareBank_iff]
          exact present
        simp [deduplicateSquareBank, present, absent,
          deduplicateSquareBank_nodup labels]

theorem mem_canonicalSquareBank_iff
    (tested : Nat) (labels : List Nat) :
    tested ∈ canonicalSquareBank labels ↔ tested ∈ labels := by
  simp [canonicalSquareBank, mem_deduplicateSquareBank_iff]

theorem canonicalSquareBank_nodup (labels : List Nat) :
    (canonicalSquareBank labels).Nodup := by
  exact
    (List.mergeSort_perm
      (deduplicateSquareBank labels)
      (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr
        (deduplicateSquareBank_nodup labels)

theorem canonicalSquareBank_pairwise (labels : List Nat) :
    (canonicalSquareBank labels).Pairwise (· ≤ ·) := by
  exact natMergeSort_pairwise (deduplicateSquareBank labels)

private theorem sortedMultipleLetters_nodup (letters : List Nat) :
    (S5_107.sortedMultipleLetters letters).Nodup := by
  unfold S5_107.sortedMultipleLetters
  exact
    (List.mergeSort_perm
      ((S5_107.distinctLetters letters).filter
        (fun letter => decide (2 ≤ letters.count letter)))
      (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr <|
      (S5_107.distinctLetters_nodup letters).filter
        (fun letter => decide (2 ≤ letters.count letter))

/-- A canonical square bank whose support is exactly the globally repeated
support is the deterministic sorted repeated-letter list. -/
theorem canonicalSquareBank_eq_sortedMultipleLetters
    (labels whole : List Nat)
    (support : ∀ tested,
      tested ∈ labels ↔ 2 ≤ whole.count tested) :
    canonicalSquareBank labels =
      S5_107.sortedMultipleLetters whole := by
  have permutation :
      (canonicalSquareBank labels).Perm
        (S5_107.sortedMultipleLetters whole) := by
    rw [List.perm_iff_count]
    intro tested
    rw [(canonicalSquareBank_nodup labels).count,
      (sortedMultipleLetters_nodup whole).count]
    simp only [mem_canonicalSquareBank_iff,
      S5_107.sortedMultipleLetters_mem_iff, support tested]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    (canonicalSquareBank_pairwise labels)
    (S5_107.sortedMultipleLetters_pairwise whole)
    permutation

/-- Full multi-gap derivational assembly. Every gap has its deterministic
parity residue, every separator stays in its unique position, and all local
and globally inserted squares collapse to one deterministic bank. -/
theorem listDerivesCanonicalSeparatorAssembly
    {whole : List Nat} {segments : List (List Nat × Nat)}
    {finalGap : List Nat}
    (decomposition :
      GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ListDerives whole
      (renderCanonicalSeparatorSkeleton segments finalGap ++
        renderSquareBank (S5_107.sortedMultipleLetters whole)) := by
  obtain ⟨localLabels, rawAssembly, exactCounts⟩ :=
    listDerivesRawSeparatorAssembly decomposition
  let skeleton :=
    renderCanonicalSeparatorSkeleton segments finalGap
  let repeatedLabels := S5_107.sortedMultipleLetters whole
  have repeatedInRawTarget : ∀ tested, tested ∈ repeatedLabels →
      2 ≤ (skeleton ++ renderSquareBank localLabels).count tested := by
    intro tested member
    have repeated : 2 ≤ whole.count tested :=
      (S5_107.sortedMultipleLetters_mem_iff tested whole).mp member
    rw [exactCounts tested]
    exact repeated
  have inserted :=
    listDerivesAppendSquareBank
      (skeleton ++ renderSquareBank localLabels)
      repeatedLabels repeatedInRawTarget
  have combinedSupport : ∀ tested,
      tested ∈ localLabels ++ repeatedLabels ↔
        2 ≤ whole.count tested := by
    intro tested
    constructor
    · intro member
      rcases List.mem_append.mp member with localMember | repeatedMember
      · have localPositive : 0 < localLabels.count tested :=
          List.count_pos_iff.mpr localMember
        have rawAtLeastTwo :
            2 ≤ (skeleton ++ renderSquareBank localLabels).count tested := by
          simp only [List.count_append, count_renderSquareBank]
          omega
        rw [exactCounts tested] at rawAtLeastTwo
        exact rawAtLeastTwo
      · exact
          (S5_107.sortedMultipleLetters_mem_iff tested whole).mp
            repeatedMember
    · intro repeated
      exact List.mem_append_right localLabels <|
        (S5_107.sortedMultipleLetters_mem_iff tested whole).mpr repeated
  have bankEq :=
    canonicalSquareBank_eq_sortedMultipleLetters
      (localLabels ++ repeatedLabels) whole combinedSupport
  have canonicalized :=
    S5_107.ListDerives.prepend
      (basis := basis) skeleton
      (listDerivesCanonicalSquareBank
        (localLabels ++ repeatedLabels))
  have assembledWithInsertedBank :
      ListDerives whole
        (skeleton ++
          renderSquareBank (localLabels ++ repeatedLabels)) :=
    rawAssembly.trans <| by
      simpa [skeleton, repeatedLabels, renderSquareBank,
        List.flatMap_append, List.append_assoc] using inserted
  exact assembledWithInsertedBank.trans <| by
    rw [bankEq] at canonicalized
    simpa [skeleton, repeatedLabels, List.append_assoc] using canonicalized

end SemigroupBasis.CoRoots.S5_254
