import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484Recursive6447Intervals

/-! Every globally repeated pair can cross in B12. The proof accounts for
both past witnesses, both future witnesses and either mixed orientation.
The only pending inputs are the two exact finite derivations in FixedSwaps. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis

theorem listDerivesSwapBothSeen (prefixWords suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ prefixWords) (rightSeen : right ∈ prefixWords) :
    LD (prefixWords ++ left :: right :: suffix) (prefixWords ++ right :: left :: suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp leftSeen
  by_cases earlier : right ∈ before
  · obtain ⟨start, gap, beforeShape⟩ := List.mem_iff_append.mp earlier
    have swap := (listDerivesSwapPastInterval right left gap after).symm.context start suffix
    simpa [shape, beforeShape, List.append_assoc] using swap
  · have later : right ∈ after := by
      simpa [shape, earlier, Ne.symm equal] using rightSeen
    obtain ⟨gap, rest, afterShape⟩ := List.mem_iff_append.mp later
    have swap := (listDerivesSwapPastInterval left right gap rest).context before suffix
    simpa [shape, afterShape, List.append_assoc] using swap

theorem listDerivesSwapMixed (fixed : FixedSwaps) (prefixWords suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ prefixWords) (rightFuture : right ∈ suffix) :
    LD (prefixWords ++ left :: right :: suffix) (prefixWords ++ right :: left :: suffix) := by
  obtain ⟨before, firstGap, prefixShape⟩ := List.mem_iff_append.mp leftSeen
  obtain ⟨secondGap, after, suffixShape⟩ := List.mem_iff_append.mp rightFuture
  have swap := (listDerivesSwapMixedInterval fixed left right firstGap secondGap).context before after
  simpa [prefixShape, suffixShape, List.append_assoc] using swap

theorem listDerivesSwapBothFuture (fixed : FixedSwaps) (prefixWords suffix : List Nat) (left right : Nat)
    (leftFuture : left ∈ suffix) (rightFuture : right ∈ suffix) :
    LD (prefixWords ++ left :: right :: suffix) (prefixWords ++ right :: left :: suffix) := by
  have rightGrow := (listDerivesHeadExpansion right suffix rightFuture).prepend [left]
  have leftFuture' : left ∈ right :: right :: suffix := by simp [leftFuture]
  have leftGrow := listDerivesHeadExpansion left (right :: right :: suffix) leftFuture'
  have commute := (listDerivesSquareCommute fixed left right).append suffix
  have rightFuture' : right ∈ left :: left :: suffix := by simp [rightFuture]
  have rightShrink := (listDerivesHeadExpansion right (left :: left :: suffix) rightFuture').symm
  have leftShrink := (listDerivesHeadExpansion left suffix leftFuture).symm.prepend [right]
  have combined := rightGrow.trans (leftGrow.trans (commute.trans (rightShrink.trans leftShrink)))
  exact combined.prepend prefixWords

theorem globalSwaps (fixed : FixedSwaps) : SimplePrefix.GlobalSwaps basis := by
  intro prefixWords left right suffix leftHeavy rightHeavy
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  have leftPlace : left ∈ prefixWords ∨ left ∈ suffix := by
    by_cases prior : left ∈ prefixWords
    · exact Or.inl prior
    have zero := List.count_eq_zero_of_not_mem prior
    have positive : 0 < suffix.count left := by
      simp only [List.count_append, List.count_cons_self, List.count_cons_of_ne (Ne.symm equal), zero] at leftHeavy
      omega
    exact Or.inr (List.count_pos_iff.mp positive)
  have rightPlace : right ∈ prefixWords ∨ right ∈ suffix := by
    by_cases prior : right ∈ prefixWords
    · exact Or.inl prior
    have zero := List.count_eq_zero_of_not_mem prior
    have positive : 0 < suffix.count right := by
      simp only [List.count_append, List.count_cons_self, List.count_cons_of_ne equal, zero] at rightHeavy
      omega
    exact Or.inr (List.count_pos_iff.mp positive)
  rcases leftPlace with leftSeen | leftFuture
  · rcases rightPlace with rightSeen | rightFuture
    · exact listDerivesSwapBothSeen prefixWords suffix left right leftSeen rightSeen
    · exact listDerivesSwapMixed fixed prefixWords suffix left right leftSeen rightFuture
  · rcases rightPlace with rightSeen | rightFuture
    · exact (listDerivesSwapMixed fixed prefixWords suffix right left rightSeen leftFuture).symm
    · exact listDerivesSwapBothFuture fixed prefixWords suffix left right leftFuture rightFuture

/-- Full unbounded reach from the capped simple-suffix signature. -/
theorem derivesOfSameSignature (fixed : FixedSwaps) {left right : Word Nat}
    (same : SimplePrefix.CappedSignature left.toList.reverse right.toList.reverse) :
    Derives basis left right := by
  have reversed := SimplePrefix.compare_capped (globalSwaps fixed).reversed growOpposite
    left.toList.reverse right.toList.reverse same
  have original := SimplePrefix.reverse_listDerives reversed
  have listed : LD left.toList right.toList := by
    simpa only [List.reverse_reverse, reversedBasis_reversedBasis] using original
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord listed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447
