import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilGapNormalization

/-! The amended, deterministic gap render: sorted parity copies of old
letters, then new introductions in first-occurrence order. A new even bit
is rendered by TWO copies, not zero or one. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

theorem freshOrder_nodup (seen letters : List Nat) : (freshOrder seen letters).Nodup :=
  (Examples.firstOccurrenceSequence_nodup letters).filter _

theorem freshOrder_idempotent (seen letters : List Nat) :
    freshOrder seen (freshOrder seen letters) = freshOrder seen letters := by
  change (Examples.firstOccurrenceSequence (freshOrder seen letters)).filter
    (fun tested => decide (tested ∉ seen)) = freshOrder seen letters
  rw [Examples.firstOccurrenceSequence_eq_self_of_nodup (freshOrder_nodup seen letters)]
  apply List.filter_eq_self.mpr
  intro tested member
  exact decide_eq_true ((mem_freshOrder_iff seen letters tested).mp member).2

theorem parityResidue_count (gap : List Nat) (tested : Nat) :
    (S5_254.canonicalGapParityResidue gap).count tested = gap.count tested % 2 := by
  let input := (S5_107.distinctLetters gap).filter (fun letter => decide (gap.count letter % 2 = 1))
  change (input.mergeSort (fun left right : Nat => decide (left ≤ right))).count tested = _
  rw [(List.mergeSort_perm input (fun left right : Nat => decide (left ≤ right))).count tested]
  have nodup : input.Nodup := (S5_107.distinctLetters_nodup gap).filter _
  have membership : tested ∈ input ↔ gap.count tested % 2 = 1 := by
    simp only [input, List.mem_filter, S5_107.distinctLetters_mem_iff, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro odd
      exact ⟨List.count_pos_iff.mp (by omega), odd⟩
  rw [nodup.count]
  simp only [membership]
  by_cases odd : gap.count tested % 2 = 1
  · simp [odd]
  · have even : gap.count tested % 2 = 0 := by omega
    simp [even]

def oldGapPart (seen gap : List Nat) : List Nat :=
  (S5_254.canonicalGapParityResidue gap).filter (fun letter => decide (letter ∈ seen))

def introductionBlock (gap : List Nat) (letter : Nat) : List Nat :=
  if gap.count letter % 2 = 0 then [letter, letter] else [letter]

def introductionBlocks (gap : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest => introductionBlock gap letter ++ introductionBlocks gap rest

def canonicalGap (seen gap : List Nat) : List Nat :=
  oldGapPart seen gap ++ introductionBlocks gap (freshOrder seen gap)

theorem oldGapPart_count (seen gap : List Nat) (tested : Nat) :
    (oldGapPart seen gap).count tested = if tested ∈ seen then gap.count tested % 2 else 0 := by
  by_cases old : tested ∈ seen
  · rw [if_pos old]
    change ((S5_254.canonicalGapParityResidue gap).filter
      (fun letter => decide (letter ∈ seen))).count tested = _
    rw [List.count_filter (by simp [old]), parityResidue_count]
  · rw [if_neg old]
    apply List.count_eq_zero.mpr
    simp [oldGapPart, old]

theorem introductionBlock_count (gap : List Nat) (letter tested : Nat) :
    (introductionBlock gap letter).count tested =
      if tested = letter then Msg0446TailBudget.firstCopies (gap.count tested % 2) else 0 := by
  by_cases equal : tested = letter
  · subst tested
    by_cases even : gap.count letter % 2 = 0 <;>
      simp [introductionBlock, Msg0446TailBudget.firstCopies, even]
  · by_cases even : gap.count letter % 2 = 0 <;>
      simp [introductionBlock, even, equal, Ne.symm equal]

theorem introductionBlocks_count (gap labels : List Nat) (nodup : labels.Nodup) (tested : Nat) :
    (introductionBlocks gap labels).count tested =
      if tested ∈ labels then Msg0446TailBudget.firstCopies (gap.count tested % 2) else 0 := by
  induction labels with
  | nil => simp [introductionBlocks]
  | cons letter rest induction =>
      have absent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      change (introductionBlock gap letter ++ introductionBlocks gap rest).count tested = _
      rw [List.count_append, introductionBlock_count, induction tailNodup]
      by_cases equal : tested = letter
      · subst tested
        simp [absent]
      · simp [equal]

theorem freshOrder_double_head (seen rest : List Nat) (letter : Nat) :
    freshOrder seen (letter :: letter :: rest) = freshOrder seen (letter :: rest) := by
  by_cases old : letter ∈ seen <;> simp [freshOrder_cons, old]

theorem freshOrder_introductionBlocks (seen gap labels : List Nat) :
    freshOrder seen (introductionBlocks gap labels) = freshOrder seen labels := by
  induction labels generalizing seen with
  | nil => rfl
  | cons letter rest induction =>
      have head : freshOrder seen (introductionBlocks gap (letter :: rest)) =
          freshOrder seen (letter :: introductionBlocks gap rest) := by
        by_cases even : gap.count letter % 2 = 0
        · simpa [introductionBlocks, introductionBlock, even] using
            freshOrder_double_head seen (introductionBlocks gap rest) letter
        · simp [introductionBlocks, introductionBlock, even]
      rw [head, freshOrder_cons seen letter (introductionBlocks gap rest),
        freshOrder_cons seen letter rest, induction seen, induction (letter :: seen)]

theorem canonicalGap_order (seen gap : List Nat) :
    freshOrder seen (canonicalGap seen gap) = freshOrder seen gap := by
  unfold canonicalGap
  rw [freshOrder_append_seen seen (oldGapPart seen gap)
      (introductionBlocks gap (freshOrder seen gap))
      (fun tested member => of_decide_eq_true (List.mem_filter.mp member).2),
    freshOrder_introductionBlocks, freshOrder_idempotent]

theorem canonicalGap_count (seen gap : List Nat) (tested : Nat) :
    (canonicalGap seen gap).count tested =
      if tested ∈ seen then gap.count tested % 2
      else if tested ∈ gap then Msg0446TailBudget.firstCopies (gap.count tested % 2) else 0 := by
  rw [canonicalGap, List.count_append, oldGapPart_count,
    introductionBlocks_count gap (freshOrder seen gap) (freshOrder_nodup seen gap)]
  simp only [mem_freshOrder_iff]
  by_cases old : tested ∈ seen <;> simp [old]

theorem canonicalGap_reduced (seen gap : List Nat) : GapReduced seen (canonicalGap seen gap) := by
  intro tested
  rw [canonicalGap_count]
  by_cases old : tested ∈ seen
  · simp only [if_pos old]
    omega
  · simp only [if_neg old]
    by_cases present : tested ∈ gap
    · simp only [if_pos present, Msg0446TailBudget.firstCopies]
      split <;> omega
    · simp [present]

theorem canonicalGap_parity (seen gap : List Nat) (tested : Nat) :
    (canonicalGap seen gap).count tested % 2 = gap.count tested % 2 := by
  rw [canonicalGap_count]
  by_cases old : tested ∈ seen
  · simp [old]
  · rw [if_neg old]
    by_cases present : tested ∈ gap
    · rw [if_pos present]
      exact Msg0446TailBudget.firstCopies_parity _ (by omega)
    · simp [present, List.count_eq_zero.mpr present]

theorem introductionBlocks_eq_of_parity (left right labels : List Nat)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    introductionBlocks left labels = introductionBlocks right labels := by
  induction labels with
  | nil => rfl
  | cons letter rest induction =>
      simp only [introductionBlocks, introductionBlock, parity letter, induction]

theorem canonicalGap_eq (leftSeen rightSeen left right : List Nat)
    (seen : ∀ tested, tested ∈ leftSeen ↔ tested ∈ rightSeen)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2)
    (order : freshOrder leftSeen left = freshOrder rightSeen right) :
    canonicalGap leftSeen left = canonicalGap rightSeen right := by
  have old : oldGapPart leftSeen left = oldGapPart rightSeen right := by
    unfold oldGapPart
    rw [S5_254.canonicalGapParityResidue_eq_of_parity left right parity]
    apply List.filter_congr
    intro tested _
    simp only [seen tested]
  rw [canonicalGap, canonicalGap, old, order,
    introductionBlocks_eq_of_parity left right (freshOrder rightSeen right) parity]

/-- The actual B23 reach theorem for the amended deterministic gap render.
All removed copies remain in an anchored, multiplicity-exact raw bank. -/
theorem normalizeRepeatedGap (prefixWords gap suffix : List Nat)
    (repeated : AllRepeated prefixWords gap suffix) :
    ∃ labels,
      S5_107.ListDerives basis (prefixWords ++ gap ++ suffix)
        (prefixWords ++ canonicalGap prefixWords gap ++ suffix ++ S5_254.renderSquareBank labels) ∧
      (∀ tested, gap.count tested =
        (canonicalGap prefixWords gap).count tested + 2 * labels.count tested) ∧
      (∀ tested ∈ labels, tested ∈ prefixWords ++ canonicalGap prefixWords gap) := by
  obtain ⟨residue, labels, derived, counts, order, reduced, seen⟩ :=
    reduceRepeatedGap prefixWords gap suffix repeated
  have parity : ∀ tested, residue.count tested % 2 =
      (canonicalGap prefixWords gap).count tested % 2 := by
    intro tested
    rw [canonicalGap_parity]
    have countEq := counts tested
    omega
  have residueOrder : freshOrder prefixWords residue =
      freshOrder prefixWords (canonicalGap prefixWords gap) :=
    order.symm.trans (canonicalGap_order prefixWords gap).symm
  have equalCounts := reducedGap_counts_eq prefixWords residue (canonicalGap prefixWords gap)
    reduced (canonicalGap_reduced prefixWords gap) parity residueOrder
  have stillRepeated : AllRepeated prefixWords residue (suffix ++ S5_254.renderSquareBank labels) := by
    intro tested member
    have residuePositive := List.count_pos_iff.mpr member
    have countEq := counts tested
    have original := repeated tested (List.count_pos_iff.mp (by omega))
    simp only [List.count_append, S5_254.count_renderSquareBank] at original ⊢
    omega
  have sorted := compareRepeatedGaps prefixWords residue (canonicalGap prefixWords gap)
    (suffix ++ S5_254.renderSquareBank labels) equalCounts residueOrder stillRepeated
  refine ⟨labels, derived.trans ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using sorted
  · intro tested
    rw [← equalCounts tested]
    exact counts tested
  · intro tested member
    exact (mem_prefix_gap_iff_of_freshOrder residueOrder tested).mp (seen tested member)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
