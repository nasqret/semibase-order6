import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilGapRender
import SemigroupBasis.CoRoots.S5_254Canonical

/-! Pure first-order cancellation at globally simple separators. These
lemmas recover the exact new introductions in each separator gap from
the full first-occurrence sequence; no semigroup converse is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis
open SemigroupBasis.Examples

theorem firstOccurrenceSequence_append (left right : List Nat) :
    firstOccurrenceSequence (left ++ right) =
      firstOccurrenceSequence left ++ freshOrder left right := by
  have emptySeen (letters : List Nat) : freshOrder [] letters = firstOccurrenceSequence letters := by
    unfold freshOrder
    apply List.filter_eq_self.mpr
    intro tested _
    simp
  have split := freshOrder_append [] left right
  rw [emptySeen (left ++ right), emptySeen left] at split
  simpa using split

theorem firstOrder_before_separator (leftPrefix rightPrefix leftTail rightTail : List Nat)
    (separator : Nat) (leftAbsent : separator ∉ leftPrefix) (rightAbsent : separator ∉ rightPrefix)
    (order : firstOccurrenceSequence (leftPrefix ++ separator :: leftTail) =
      firstOccurrenceSequence (rightPrefix ++ separator :: rightTail)) :
    firstOccurrenceSequence leftPrefix = firstOccurrenceSequence rightPrefix := by
  rw [firstOccurrenceSequence_append leftPrefix (separator :: leftTail),
    firstOccurrenceSequence_append rightPrefix (separator :: rightTail),
    freshOrder_cons leftPrefix separator leftTail, if_neg leftAbsent,
    freshOrder_cons rightPrefix separator rightTail, if_neg rightAbsent] at order
  have scanned := congrArg (S5_254.simplePrefixBefore separator) order
  have leftFirstAbsent : separator ∉ firstOccurrenceSequence leftPrefix := by
    simpa only [mem_firstOccurrenceSequence_iff] using leftAbsent
  have rightFirstAbsent : separator ∉ firstOccurrenceSequence rightPrefix := by
    simpa only [mem_firstOccurrenceSequence_iff] using rightAbsent
  rw [S5_254.simplePrefixBefore_split separator (firstOccurrenceSequence leftPrefix)
      (freshOrder (separator :: leftPrefix) leftTail) leftFirstAbsent,
    S5_254.simplePrefixBefore_split separator (firstOccurrenceSequence rightPrefix)
      (freshOrder (separator :: rightPrefix) rightTail) rightFirstAbsent] at scanned
  exact scanned

theorem firstOrder_append_fresh_separator (prefixWords : List Nat) (separator : Nat)
    (absent : separator ∉ prefixWords) :
    firstOccurrenceSequence (prefixWords ++ [separator]) =
      firstOccurrenceSequence prefixWords ++ [separator] := by
  rw [firstOccurrenceSequence_append, freshOrder_cons, if_neg absent]
  rfl

theorem freshGap_order_of_prefixes (seen leftPrefix rightPrefix leftGap rightGap : List Nat)
    (leftSeen : ∀ tested, tested ∈ seen ↔ tested ∈ leftPrefix)
    (rightSeen : ∀ tested, tested ∈ seen ↔ tested ∈ rightPrefix)
    (prefixOrder : firstOccurrenceSequence leftPrefix = firstOccurrenceSequence rightPrefix)
    (extendedOrder : firstOccurrenceSequence (leftPrefix ++ leftGap) =
      firstOccurrenceSequence (rightPrefix ++ rightGap)) :
    freshOrder seen leftGap = freshOrder seen rightGap := by
  rw [firstOccurrenceSequence_append, firstOccurrenceSequence_append, prefixOrder] at extendedOrder
  have tailOrder : freshOrder leftPrefix leftGap = freshOrder rightPrefix rightGap :=
    List.append_cancel_left extendedOrder
  exact (freshOrder_seen_congr leftSeen leftGap).trans
    (tailOrder.trans (freshOrder_seen_congr rightSeen rightGap).symm)

theorem seen_after_canonicalGap (seen prefixWords gap : List Nat) (separator : Nat)
    (same : ∀ tested, tested ∈ seen ↔ tested ∈ prefixWords) :
    ∀ tested,
      tested ∈ seen ++ canonicalGap seen gap ++ [separator] ↔
        tested ∈ prefixWords ++ gap ++ [separator] := by
  intro tested
  have gapSupport := mem_prefix_gap_iff_of_freshOrder (canonicalGap_order seen gap) tested
  simp only [List.mem_append] at gapSupport ⊢
  rw [gapSupport, same tested]

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
