import SemigroupBasis.Generated.Order6LeeA2LatticeNodes
import SemigroupBasis.CoRoots.S5_804Canonical
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesBarrierFinal

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## A barrier detector for the final letter before an exact cut -/

/-- Six distinguished values witnessing that the final letter before a
separator can be read semantically.

`low` and `high` form a right-zero pair.  The selected predecessor letter is
sent to `high`, every other predecessor letter to `low`, and the separator to
`barrier`.  Multiplication by the barrier records the predecessor state as
`hit` or `miss`; a tail value then preserves that record. -/
structure BarrierFinalMarker {S : Type} (candidate : Semigroup S) where
  low : S
  high : S
  barrier : S
  miss : S
  hit : S
  tail : S
  rightZero :
    ∀ current next,
      (current = low ∨ current = high) →
      (next = low ∨ next = high) →
      candidate.mul current next = next
  low_barrier : candidate.mul low barrier = miss
  high_barrier : candidate.mul high barrier = hit
  miss_tail : candidate.mul miss tail = miss
  hit_tail : candidate.mul hit tail = hit
  hit_ne_miss : hit ≠ miss

namespace BarrierFinalMarker

variable {S : Type} {candidate : Semigroup S}

/-- The selected predecessor letter, the separator, the after-support, and
all remaining letters receive the four values used by the detector. -/
def valuation (marker : BarrierFinalMarker candidate)
    (selected separator : Nat) (afterSupport : List Nat) :
    Nat → S :=
  fun letter =>
    if letter = selected then marker.high
    else if letter = separator then marker.barrier
    else if letter ∈ afterSupport then marker.tail
    else marker.low

@[simp]
theorem valuation_selected (marker : BarrierFinalMarker candidate)
    (selected separator : Nat) (afterSupport : List Nat) :
    marker.valuation selected separator afterSupport selected =
      marker.high := by
  simp [valuation]

@[simp]
theorem valuation_separator (marker : BarrierFinalMarker candidate)
    {selected separator : Nat} {afterSupport : List Nat}
    (different : separator ≠ selected) :
    marker.valuation selected separator afterSupport separator =
      marker.barrier := by
  simp [valuation, different]

theorem valuation_tail (marker : BarrierFinalMarker candidate)
    {selected separator letter : Nat} {afterSupport : List Nat}
    (notSelected : letter ≠ selected)
    (notSeparator : letter ≠ separator)
    (member : letter ∈ afterSupport) :
    marker.valuation selected separator afterSupport letter =
      marker.tail := by
  simp [valuation, notSelected, notSeparator, member]

theorem valuation_low (marker : BarrierFinalMarker candidate)
    {selected separator letter : Nat} {afterSupport : List Nat}
    (notSelected : letter ≠ selected)
    (notSeparator : letter ≠ separator)
    (absent : letter ∉ afterSupport) :
    marker.valuation selected separator afterSupport letter =
      marker.low := by
  simp [valuation, notSelected, notSeparator, absent]

/-- A fold whose values stay in the marker's right-zero pair returns the
value of the literal final letter. -/
theorem fold_rightZero_componentFinal
    (marker : BarrierFinalMarker candidate) (assigned : Nat → S)
    (head : Nat) (tail : List Nat)
    (phase :
      ∀ letter, letter ∈ head :: tail →
        assigned letter = marker.low ∨
          assigned letter = marker.high) :
    tail.foldl
        (fun current letter =>
          candidate.mul current (assigned letter))
        (assigned head) =
      assigned (S5_804.componentFinal (head :: tail)) := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest inductionHypothesis =>
      have headPhase :
          assigned head = marker.low ∨
            assigned head = marker.high :=
        phase head (List.Mem.head (next :: rest))
      have nextPhase :
          assigned next = marker.low ∨
            assigned next = marker.high :=
        phase next
          (List.Mem.tail head (List.Mem.head rest))
      have restPhase :
          ∀ letter, letter ∈ next :: rest →
            assigned letter = marker.low ∨
              assigned letter = marker.high := by
        intro letter member
        exact phase letter (List.Mem.tail head member)
      rw [List.foldl_cons,
        marker.rightZero (assigned head) (assigned next)
          headPhase nextPhase]
      simpa only [S5_804.componentFinal, List.getLastD_cons] using
        inductionHypothesis next restPhase

/-- Once the detector reaches `hit`, a suffix valued uniformly at `tail`
preserves it. -/
theorem fold_hit_tail
    (marker : BarrierFinalMarker candidate) (assigned : Nat → S) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        assigned letter = marker.tail) →
      letters.foldl
          (fun current letter =>
            candidate.mul current (assigned letter))
          marker.hit =
        marker.hit
  | [], _ => rfl
  | letter :: rest, allTail => by
      have firstTail :
          assigned letter = marker.tail :=
        allTail letter (List.Mem.head rest)
      have restTail :
          ∀ tested, tested ∈ rest →
            assigned tested = marker.tail := by
        intro tested member
        exact allTail tested (List.Mem.tail letter member)
      rw [List.foldl_cons, firstTail, marker.hit_tail]
      exact fold_hit_tail marker assigned rest restTail

/-- Once the detector reaches `miss`, a suffix valued uniformly at `tail`
preserves it. -/
theorem fold_miss_tail
    (marker : BarrierFinalMarker candidate) (assigned : Nat → S) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        assigned letter = marker.tail) →
      letters.foldl
          (fun current letter =>
            candidate.mul current (assigned letter))
          marker.miss =
        marker.miss
  | [], _ => rfl
  | letter :: rest, allTail => by
      have firstTail :
          assigned letter = marker.tail :=
        allTail letter (List.Mem.head rest)
      have restTail :
          ∀ tested, tested ∈ rest →
            assigned tested = marker.tail := by
        intro tested member
        exact allTail tested (List.Mem.tail letter member)
      rw [List.foldl_cons, firstTail, marker.miss_tail]
      exact fold_miss_tail marker assigned rest restTail

/-- Rewrite word evaluation as a list fold when the complete list shape is
known. -/
theorem eval_eq_foldl_of_toList_eq
    (assigned : Nat → S) (word : Word Nat)
    (head : Nat) (tail : List Nat)
    (shape : word.toList = head :: tail) :
    candidate.eval assigned word =
      tail.foldl
        (fun current letter =>
          candidate.mul current (assigned letter))
        (assigned head) := by
  have wordEquality : word = Word.mk head tail := by
    apply Word.toList_injective
    simpa [Word.toList] using shape
  subst word
  rfl

theorem exactCut_separator_not_mem_before
    {letters before after : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters before separator after) :
    separator ∉ before := by
  intro member
  have positive : 0 < before.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

theorem exactCut_separator_not_mem_after
    {letters before after : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        letters before separator after) :
    separator ∉ after := by
  intro member
  have positive : 0 < after.count separator :=
    List.count_pos_iff.mpr member
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

/-- On a nonempty predecessor, the barrier valuation returns `hit` exactly
when the selected letter is the predecessor's literal final letter. -/
theorem eval_exactCut_componentFinal
    (marker : BarrierFinalMarker candidate) (word : Word Nat)
    {before after referenceAfter : List Nat}
    {separator selected : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        word.toList before separator after)
    (beforeNonempty : before ≠ [])
    (sameAfter :
      ∀ letter, letter ∈ after ↔ letter ∈ referenceAfter)
    (selectedMember : selected ∈ before) :
    candidate.eval
        (marker.valuation selected separator referenceAfter) word =
      if S5_804.componentFinal before = selected
      then marker.hit
      else marker.miss := by
  have separatorAbsentBefore :
      separator ∉ before :=
    exactCut_separator_not_mem_before cut
  have separatorAbsentAfter :
      separator ∉ after :=
    exactCut_separator_not_mem_after cut
  have selectedNeSeparator : selected ≠ separator := by
    intro equality
    subst selected
    exact separatorAbsentBefore selectedMember
  have separatorAbsentReference :
      separator ∉ referenceAfter := by
    intro member
    exact separatorAbsentAfter ((sameAfter separator).mpr member)
  have afterTail :
      ∀ letter, letter ∈ after →
        marker.valuation selected separator referenceAfter letter =
          marker.tail := by
    intro letter member
    have notSelected : letter ≠ selected := by
      intro equality
      subst letter
      exact cut.2.2 selected selectedMember member
    have notSeparator : letter ≠ separator := by
      intro equality
      subst letter
      exact separatorAbsentAfter member
    exact marker.valuation_tail notSelected notSeparator
      ((sameAfter letter).mp member)
  cases before with
  | nil =>
      exact False.elim (beforeNonempty rfl)
  | cons head beforeTail =>
      have beforePhase :
          ∀ letter, letter ∈ head :: beforeTail →
            marker.valuation selected separator referenceAfter letter =
                marker.low ∨
              marker.valuation selected separator referenceAfter letter =
                marker.high := by
        intro letter member
        by_cases isSelected : letter = selected
        · subst letter
          exact Or.inr
            (marker.valuation_selected
              selected separator referenceAfter)
        · have notSeparator : letter ≠ separator := by
            intro equality
            subst letter
            exact separatorAbsentBefore member
          have absentReference : letter ∉ referenceAfter := by
            intro referenceMember
            exact cut.2.2 letter member
              ((sameAfter letter).mpr referenceMember)
          exact Or.inl
            (marker.valuation_low
              isSelected notSeparator absentReference)
      have finalMember :
          S5_804.componentFinal (head :: beforeTail) ∈
            head :: beforeTail :=
        S5_804.componentFinal_mem head beforeTail
      have finalNeSeparator :
          S5_804.componentFinal (head :: beforeTail) ≠ separator := by
        intro equality
        rw [equality] at finalMember
        exact separatorAbsentBefore finalMember
      have finalAbsentReference :
          S5_804.componentFinal (head :: beforeTail) ∉
            referenceAfter := by
        intro referenceMember
        exact cut.2.2
          (S5_804.componentFinal (head :: beforeTail))
          finalMember
          ((sameAfter
            (S5_804.componentFinal (head :: beforeTail))).mpr
              referenceMember)
      have listShape :
          word.toList =
            head :: (beforeTail ++ separator :: after) := by
        simpa using cut.1
      rw [eval_eq_foldl_of_toList_eq
        (candidate := candidate)
        (marker.valuation selected separator referenceAfter)
        word head (beforeTail ++ separator :: after) listShape,
        List.foldl_append,
        marker.fold_rightZero_componentFinal
          (marker.valuation selected separator referenceAfter)
          head beforeTail beforePhase,
        List.foldl_cons,
        marker.valuation_separator (Ne.symm selectedNeSeparator)]
      by_cases finalSelected :
          S5_804.componentFinal (head :: beforeTail) = selected
      · rw [if_pos finalSelected, finalSelected,
          marker.valuation_selected, marker.high_barrier]
        exact marker.fold_hit_tail
          (marker.valuation selected separator referenceAfter)
          after afterTail
      · rw [if_neg finalSelected,
          marker.valuation_low
            finalSelected finalNeSeparator finalAbsentReference,
          marker.low_barrier]
        exact marker.fold_miss_tail
          (marker.valuation selected separator referenceAfter)
          after afterTail

end BarrierFinalMarker

/-! ## The predecessor-final invariant -/

/-- Matching exact cuts with equal predecessor and successor supports have
the same literal final letter in their nonempty predecessors. -/
def SamePredecessorFinals (left right : Word Nat) : Prop :=
  ∀ {separator : Nat}
      {leftBefore leftAfter rightBefore rightAfter : List Nat},
    UniqueSeparatorFourExactCut
        left.toList leftBefore separator leftAfter →
      UniqueSeparatorFourExactCut
        right.toList rightBefore separator rightAfter →
      (∀ letter, letter ∈ leftBefore ↔ letter ∈ rightBefore) →
      (∀ letter, letter ∈ leftAfter ↔ letter ∈ rightAfter) →
      leftBefore ≠ [] →
      rightBefore ≠ [] →
      S5_804.componentFinal leftBefore =
        S5_804.componentFinal rightBefore

/-- A valid identity preserves the literal predecessor final at every pair of
matching nonempty exact cuts. -/
theorem samePredecessorFinals_of_valid
    {S : Type} {candidate : Semigroup S}
    (marker : BarrierFinalMarker candidate)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate) :
    SamePredecessorFinals identity.lhs identity.rhs := by
  intro separator leftBefore leftAfter rightBefore rightAfter
    leftCut rightCut sameBefore sameAfter
    leftBeforeNonempty rightBeforeNonempty
  cases leftBefore with
  | nil =>
      exact False.elim (leftBeforeNonempty rfl)
  | cons leftHead leftTail =>
      let selected :=
        S5_804.componentFinal (leftHead :: leftTail)
      have selectedLeftMember :
          selected ∈ leftHead :: leftTail := by
        exact S5_804.componentFinal_mem leftHead leftTail
      have selectedRightMember :
          selected ∈ rightBefore :=
        (sameBefore selected).mp selectedLeftMember
      have leftEvaluation :=
        marker.eval_exactCut_componentFinal identity.lhs
          (referenceAfter := leftAfter)
          leftCut leftBeforeNonempty
          (fun _ => Iff.rfl) selectedLeftMember
      have rightEvaluation :=
        marker.eval_exactCut_componentFinal identity.rhs
          (referenceAfter := leftAfter)
          rightCut rightBeforeNonempty
          (fun letter => (sameAfter letter).symm)
          selectedRightMember
      by_cases sameFinal :
          S5_804.componentFinal (leftHead :: leftTail) =
            S5_804.componentFinal rightBefore
      · exact sameFinal
      · have rightFinalNeSelected :
            S5_804.componentFinal rightBefore ≠ selected := by
          intro equality
          apply sameFinal
          simpa [selected] using equality.symm
        have leftHit :
            candidate.eval
                (marker.valuation selected separator leftAfter)
                identity.lhs =
              marker.hit := by
          simpa [selected] using leftEvaluation
        have rightMiss :
            candidate.eval
                (marker.valuation selected separator leftAfter)
                identity.rhs =
              marker.miss := by
          simpa [rightFinalNeSelected] using rightEvaluation
        have evaluated :=
          valid (marker.valuation selected separator leftAfter)
        rw [leftHit, rightMiss] at evaluated
        exact False.elim (marker.hit_ne_miss evaluated)

/-! ## Concrete Lee-A2 lattice-node markers -/

namespace S6_7976

def marker :
    BarrierFinalMarker
      Generated.Order6LeeA2LatticeNodes.S6_7976.table.semigroup where
  low := ⟨3, by decide⟩
  high := ⟨4, by decide⟩
  barrier := ⟨1, by decide⟩
  miss := ⟨0, by decide⟩
  hit := ⟨2, by decide⟩
  tail := ⟨5, by decide⟩
  rightZero := by
    intro current next currentPhase nextPhase
    rcases currentPhase with rfl | rfl <;>
      rcases nextPhase with rfl | rfl <;> decide
  low_barrier := by decide
  high_barrier := by decide
  miss_tail := by decide
  hit_tail := by decide
  hit_ne_miss := by decide

end S6_7976

namespace S6_7982

def marker :
    BarrierFinalMarker
      Generated.Order6LeeA2LatticeNodes.S6_7982.table.semigroup where
  low := ⟨3, by decide⟩
  high := ⟨4, by decide⟩
  barrier := ⟨1, by decide⟩
  miss := ⟨0, by decide⟩
  hit := ⟨2, by decide⟩
  tail := ⟨5, by decide⟩
  rightZero := by
    intro current next currentPhase nextPhase
    rcases currentPhase with rfl | rfl <;>
      rcases nextPhase with rfl | rfl <;> decide
  low_barrier := by decide
  high_barrier := by decide
  miss_tail := by decide
  hit_tail := by decide
  hit_ne_miss := by decide

end S6_7982

end SemigroupBasis.CoRoots.Order6LeeA2LatticeNodesBarrierFinal
