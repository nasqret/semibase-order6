import SemigroupBasis.CoRoots.S5_441CanonicalGap

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

private theorem sortedNodupNat_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have := (sameSupport head).2 (by simp)
          contradiction
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have := (sameSupport leftHead).1 (by simp)
          contradiction
      | cons rightHead rightTail =>
          have leftHeadInRight :=
            (sameSupport leftHead).1 (by simp)
          have rightHeadInLeft :=
            (sameSupport rightHead).2 (by simp)
          have rightHeadLeLeftHead : rightHead ≤ leftHead := by
            by_cases equal : leftHead = rightHead
            · omega
            · have tailMember : leftHead ∈ rightTail := by
                simpa [equal] using leftHeadInRight
              exact List.rel_of_pairwise_cons rightSorted tailMember
          have leftHeadLeRightHead : leftHead ≤ rightHead := by
            by_cases equal : rightHead = leftHead
            · omega
            · have tailMember : rightHead ∈ leftTail := by
                simpa [equal] using rightHeadInLeft
              exact List.rel_of_pairwise_cons leftSorted tailMember
          have headsEqual : leftHead = rightHead := by omega
          subst rightHead
          congr 1
          apply ih leftSorted.tail rightSorted.tail
            leftNodup.tail rightNodup.tail
          intro letter
          by_cases equal : letter = leftHead
          · subst letter
            have leftAbsent : leftHead ∉ leftTail := by
              simpa using (List.nodup_cons.mp leftNodup).1
            have rightAbsent : leftHead ∉ rightTail := by
              simpa using (List.nodup_cons.mp rightNodup).1
            simp [leftAbsent, rightAbsent]
          · simpa [equal] using sameSupport letter

/-- Lists with the same support have the same deterministic ascending support
list. -/
theorem connectedComponentSortedSupport_eq_of_support
    {left right : List Nat}
    (supportEq : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    connectedComponentSortedSupport left =
      connectedComponentSortedSupport right := by
  apply sortedNodupNat_eq_of_mem_iff
    (connectedComponentSortedSupport_sorted left)
    (connectedComponentSortedSupport_sorted right)
    (connectedComponentSortedSupport_nodup left)
    (connectedComponentSortedSupport_nodup right)
  intro letter
  exact
    (connectedComponentSortedSupport_mem_iff letter left).trans <|
      (supportEq letter).trans
        (connectedComponentSortedSupport_mem_iff letter right).symm

/-- One canonical payload block depends on its source only through the parity
of the block letter. -/
theorem canonicalGapPayloadBlock_eq_of_parity
    {left right : List Nat} (letter : Nat)
    (parityEq :
      left.count letter % 2 = right.count letter % 2) :
    canonicalGapPayloadBlock left letter =
      canonicalGapPayloadBlock right letter := by
  unfold canonicalGapPayloadBlock
  rw [parityEq]

/-- For a fixed ordered support, coordinate parity determines the complete
canonical payload. -/
theorem canonicalGapPayload_eq_of_parity
    {left right support : List Nat}
    (parityEq :
      ∀ letter, left.count letter % 2 = right.count letter % 2) :
    canonicalGapPayload left support =
      canonicalGapPayload right support := by
  induction support with
  | nil =>
      rfl
  | cons letter remaining ih =>
      simp only [canonicalGapPayload]
      rw [
        canonicalGapPayloadBlock_eq_of_parity
          letter (parityEq letter),
        ih
      ]

/-- The canonical gap is determined exactly by source support and coordinate
parity. -/
theorem canonicalGap_eq_of_support_parity
    {left right : List Nat}
    (supportEq : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (parityEq :
      ∀ letter, left.count letter % 2 = right.count letter % 2) :
    canonicalGap left = canonicalGap right := by
  have sortedSupportEq :
      connectedComponentSortedSupport left =
        connectedComponentSortedSupport right :=
    connectedComponentSortedSupport_eq_of_support supportEq
  unfold canonicalGap
  rw [sortedSupportEq]
  cases supportShape :
      connectedComponentSortedSupport right with
  | nil =>
      simp [supportShape]
  | cons anchor payloadSupport =>
      simp only [supportShape]
      rw [
        canonicalGapPayload_eq_of_parity
          (support := payloadSupport) parityEq,
        parityEq anchor
      ]

end SemigroupBasis.CoRoots.S5_441
