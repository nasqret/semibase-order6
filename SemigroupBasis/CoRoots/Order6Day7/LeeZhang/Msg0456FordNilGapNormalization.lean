import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilGapComparison
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilPower
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456CapTwoGuardedBank

/-! Unrestricted, exact-count gap reduction. An old letter retains its
parity bit; a new letter retains one or two copies. Every removed square
has an actual retained first-occurrence anchor and is carried at the global
tail. No square is deleted and no first occurrence crosses another. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

private abbrev LD := S5_107.ListDerives basis
private abbrev bank := S5_254.renderSquareBank

theorem freshOrder_remove_seen (seen before after : List Nat) (letter : Nat)
    (old : letter ∈ seen) :
    freshOrder seen (before ++ letter :: after) = freshOrder seen (before ++ after) := by
  rw [freshOrder_move_seen_head seen before after letter (Or.inl old),
    freshOrder_cons seen letter (before ++ after), if_pos old]

theorem mem_prefix_gap_iff_of_freshOrder {prefixWords left right : List Nat}
    (order : freshOrder prefixWords left = freshOrder prefixWords right) (tested : Nat) :
    tested ∈ prefixWords ++ left ↔ tested ∈ prefixWords ++ right := by
  by_cases old : tested ∈ prefixWords
  · simp [old]
  · have same : tested ∈ freshOrder prefixWords left ↔ tested ∈ freshOrder prefixWords right := by
      rw [order]
    simpa [mem_freshOrder_iff, old] using same

/-- Remove two occurrences of an already-seen letter from the gap, keeping
both copies in an anchored square at the global tail. -/
theorem extractSeenGapPair (prefixWords gap suffix : List Nat) (letter : Nat)
    (old : letter ∈ prefixWords) (two : 2 ≤ gap.count letter)
    (repeated : AllRepeated prefixWords gap suffix) :
    ∃ reduced,
      LD (prefixWords ++ gap ++ suffix)
        (prefixWords ++ reduced ++ suffix ++ [letter, letter]) ∧
      (∀ tested, gap.count tested = reduced.count tested + [letter, letter].count tested) ∧
      freshOrder prefixWords gap = freshOrder prefixWords reduced ∧
      letter ∈ prefixWords ++ reduced ∧ reduced.length + 2 = gap.length := by
  obtain ⟨before, middle, after, shape⟩ :=
    Msg0463NilZ2.exists_two_occurrence_split letter two
  let reduced := before ++ middle ++ after
  have counts : ∀ tested, gap.count tested = reduced.count tested + [letter, letter].count tested := by
    intro tested
    rw [shape]
    simp only [reduced, List.count_append, List.count_cons, List.count_nil]
    omega
  have order : freshOrder prefixWords gap = freshOrder prefixWords reduced := by
    rw [shape]
    simp only [List.append_assoc, List.cons_append]
    rw [freshOrder_remove_seen prefixWords before (middle ++ letter :: after) letter old]
    rw [← List.append_assoc,
      freshOrder_remove_seen prefixWords (before ++ middle) after letter old]
  have gathered : LD (prefixWords ++ gap ++ suffix)
      (prefixWords ++ [letter, letter] ++ reduced ++ suffix) := by
    have compared := compareRepeatedGaps prefixWords gap ([letter, letter] ++ reduced) suffix
      (fun tested => by
        have equal := counts tested
        simp only [List.count_append, List.count_cons, List.count_nil] at equal ⊢
        omega)
      (by simpa [freshOrder_cons, old] using order) repeated
    simpa [List.append_assoc] using compared
  have moved := listDerivesPairAcrossSeen prefixWords (reduced ++ suffix) letter old
  refine ⟨reduced, gathered.trans ?_, counts, order,
    List.mem_append_left reduced old, ?_⟩
  · simpa [List.append_assoc] using moved
  · rw [shape]
    simp [reduced]
    omega

/-- A new letter can shed a square only after retaining an actual earlier
copy. Three local occurrences therefore suffice, whereas two do not. -/
theorem extractAnchoredGapPair (prefixWords gap suffix : List Nat) (letter : Nat)
    (three : 3 ≤ gap.count letter) (repeated : AllRepeated prefixWords gap suffix) :
    ∃ reduced,
      LD (prefixWords ++ gap ++ suffix)
        (prefixWords ++ reduced ++ suffix ++ [letter, letter]) ∧
      (∀ tested, gap.count tested = reduced.count tested + [letter, letter].count tested) ∧
      freshOrder prefixWords gap = freshOrder prefixWords reduced ∧
      letter ∈ prefixWords ++ reduced ∧ reduced.length + 2 = gap.length := by
  obtain ⟨before, firstGap, secondGap, after, shape⟩ :=
    Msg0463NilZ2.exists_three_occurrence_split letter three
  let initial := before ++ [letter]
  let remainder := firstGap ++ [letter] ++ secondGap ++ [letter] ++ after
  have gapShape : gap = initial ++ remainder := by
    simp [shape, initial, remainder, List.append_assoc]
  have two : 2 ≤ remainder.count letter := by simp [remainder]; omega
  have repeatedTail : AllRepeated (prefixWords ++ initial) remainder suffix := by
    intro tested member
    have original := repeated tested (by rw [gapShape]; exact List.mem_append_right initial member)
    simpa [gapShape, List.append_assoc] using original
  obtain ⟨reducedTail, derived, tailCounts, tailOrder, _, tailLength⟩ :=
    extractSeenGapPair (prefixWords ++ initial) remainder suffix letter
      (by simp [initial]) two repeatedTail
  let reduced := initial ++ reducedTail
  refine ⟨reduced, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gapShape, reduced, List.append_assoc] using derived
  · intro tested
    have counts := tailCounts tested
    simp only [gapShape, reduced, List.count_append]
    omega
  · rw [gapShape, show reduced = initial ++ reducedTail from rfl,
      freshOrder_append prefixWords initial remainder,
      freshOrder_append prefixWords initial reducedTail, tailOrder]
  · simp [reduced, initial]
  · simp only [gapShape, reduced, List.length_append]
    omega

def GapReduced (prefixWords gap : List Nat) : Prop :=
  ∀ tested, gap.count tested ≤ if tested ∈ prefixWords then 1 else 2

/-- All local excess pairs are extracted without losing a first occurrence.
The count equation accounts for every removed copy, including duplicate
bank labels; the proof is not a finite alphabet or length check. -/
theorem reduceRepeatedGap (prefixWords gap suffix : List Nat)
    (repeated : AllRepeated prefixWords gap suffix) :
    ∃ residue labels,
      LD (prefixWords ++ gap ++ suffix)
        (prefixWords ++ residue ++ suffix ++ bank labels) ∧
      (∀ tested, gap.count tested = residue.count tested + 2 * labels.count tested) ∧
      freshOrder prefixWords gap = freshOrder prefixWords residue ∧
      GapReduced prefixWords residue ∧
      (∀ tested ∈ labels, tested ∈ prefixWords ++ residue) := by
  by_cases excess : ∃ letter, (if letter ∈ prefixWords then 1 else 2) < gap.count letter
  · obtain ⟨letter, tooMany⟩ := excess
    have extraction : ∃ reduced,
        LD (prefixWords ++ gap ++ suffix)
          (prefixWords ++ reduced ++ suffix ++ [letter, letter]) ∧
        (∀ tested, gap.count tested = reduced.count tested + [letter, letter].count tested) ∧
        freshOrder prefixWords gap = freshOrder prefixWords reduced ∧
        letter ∈ prefixWords ++ reduced ∧ reduced.length + 2 = gap.length := by
      by_cases old : letter ∈ prefixWords
      · simp only [if_pos old] at tooMany
        exact extractSeenGapPair prefixWords gap suffix letter old (by omega) repeated
      · simp only [if_neg old] at tooMany
        exact extractAnchoredGapPair prefixWords gap suffix letter (by omega) repeated
    obtain ⟨reduced, extracted, removedCounts, removedOrder, anchor, shorter⟩ := extraction
    have reducedRepeated : AllRepeated prefixWords reduced (suffix ++ [letter, letter]) := by
      intro tested member
      have positive := List.count_pos_iff.mpr member
      have countEq := removedCounts tested
      have original := repeated tested (List.count_pos_iff.mp (by omega))
      simp only [List.count_append] at original ⊢
      omega
    obtain ⟨residue, labels, derived, counts, order, limited, seen⟩ :=
      reduceRepeatedGap prefixWords reduced (suffix ++ [letter, letter]) reducedRepeated
    refine ⟨residue, letter :: labels, extracted.trans ?_, ?_,
      removedOrder.trans order, limited, ?_⟩
    · simpa [bank, S5_254.renderSquareBank, List.append_assoc] using derived
    · intro tested
      have firstCounts := removedCounts tested
      have restCounts := counts tested
      simp only [List.count_cons, List.count_nil] at firstCounts ⊢
      omega
    · intro tested member
      rcases List.mem_cons.mp member with equal | member
      · subst tested
        exact (mem_prefix_gap_iff_of_freshOrder order letter).mp anchor
      · exact seen tested member
  · refine ⟨gap, [], ?_, ?_, rfl, ?_, ?_⟩
    · simpa [bank, S5_254.renderSquareBank] using
        S5_107.ListDerives.refl (basis := basis) (prefixWords ++ gap ++ suffix)
    · intro tested
      simp
    · intro tested
      have bounded : ¬ (if tested ∈ prefixWords then 1 else 2) < gap.count tested :=
        fun tooMany => excess ⟨tested, tooMany⟩
      omega
    · simp
termination_by gap.length
decreasing_by omega

/-- Two reduced gaps with the same parity profile and new introductions
have exactly the same multiplicities. New even-parity letters retain two
copies, as required by msg0452, rather than being removed. -/
theorem reducedGap_counts_eq (prefixWords left right : List Nat)
    (leftReduced : GapReduced prefixWords left)
    (rightReduced : GapReduced prefixWords right)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2)
    (order : freshOrder prefixWords left = freshOrder prefixWords right) :
    ∀ tested, left.count tested = right.count tested := by
  intro tested
  have leftBound := leftReduced tested
  have rightBound := rightReduced tested
  have parityEq := parity tested
  by_cases old : tested ∈ prefixWords
  · simp only [if_pos old] at leftBound rightBound
    omega
  · simp only [if_neg old] at leftBound rightBound
    have sameSupport : tested ∈ left ↔ tested ∈ right := by
      have support := mem_prefix_gap_iff_of_freshOrder order tested
      simpa [old] using support
    by_cases present : tested ∈ left
    · have leftPositive := List.count_pos_iff.mpr present
      have rightPositive := List.count_pos_iff.mpr (sameSupport.mp present)
      omega
    · have rightAbsent : tested ∉ right := fun member => present (sameSupport.mpr member)
      rw [List.count_eq_zero.mpr present, List.count_eq_zero.mpr rightAbsent]

theorem compareReducedGaps (prefixWords left right suffix : List Nat)
    (leftReduced : GapReduced prefixWords left)
    (rightReduced : GapReduced prefixWords right)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2)
    (order : freshOrder prefixWords left = freshOrder prefixWords right)
    (repeated : AllRepeated prefixWords left suffix) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) :=
  compareRepeatedGaps prefixWords left right suffix
    (reducedGap_counts_eq prefixWords left right leftReduced rightReduced parity order)
    order repeated

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
