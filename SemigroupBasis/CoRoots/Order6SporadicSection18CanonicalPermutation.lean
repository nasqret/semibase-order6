import SemigroupBasis.CoRoots.Order6SporadicSection18TaggedAdjacency

/-! Canonical first-block equality, slot/block multiplicities, and both
simple/block adjacency invariants. The remaining completeness step is the
actual derivation-producing exchange, not an assumed permutation-to-derivation. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis Actual

theorem CanonicalWitness.first_block_zero {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest) (valuation : Nat → Fin 6) (acc value : Fin 6)
    (uniform : ∀ x ∈ first.block, valuation x = value) (killed : tableMul acc value = 0) :
    run valuation acc whole = 0 := by
  have nonempty := (witness.2.2.2.2.2.2.2.1.1 first (List.Mem.head rest)).1
  obtain ⟨head, tail, blockShape⟩ := List.exists_cons_of_ne_nil nonempty
  have wordShape : whole = head :: head :: (squareList tail ++ render rest) := by
    simpa only [render, witness.2.2.2.2.1, blockShape, squareList_cons,
      List.nil_append, List.cons_append, List.append_assoc] using witness.2.2.2.2.2.2.2.2.symm
  rw [wordShape, run_cons, uniform head (by rw [blockShape]; simp), killed, run_zero]

theorem CanonicalWitness.same_first_block {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest)
    (same : SameEval left right) : leftFirst.block = rightFirst.block := by
  by_cases equal : leftFirst.block = rightFirst.block
  · exact equal
  · have rightPresent : BlockOccurs rightFirst.block (leftFirst :: leftRest) :=
      (leftWitness.same_block_sets rightWitness same rightFirst.block).mpr ⟨rightFirst, List.Mem.head _, rfl⟩
    obtain ⟨anchor, other, before, window, after, orientation, shape, anchored,
      _, _, otherPresent, outside, separated⟩ :=
      canonical_oriented_window leftWitness.2.2.2.2.2.2.2.1 leftFirst.block rightFirst.block equal
        ⟨leftFirst, List.Mem.head _, rfl⟩ rightPresent
    obtain ⟨anchorSlot, anchorMember, anchorBlock⟩ := anchored.anchor_present
    obtain ⟨otherSlot, otherMember, otherBlock⟩ := otherPresent
    have windowNonempty : window ≠ [] := by
      intro empty
      rw [empty] at anchorMember
      cases anchorMember
    obtain ⟨valuation, acc, nonzero, insideFour, outsideFive, _⟩ :=
      leftWitness.window_valuation before window after shape windowNonempty outside separated
    have incompatible : ∀ a : Fin 6, tableMul a 4 = 0 ∨ tableMul a 5 = 0 := by decide
    apply False.elim
    rcases orientation with original | switched
    · have leftFour : ∀ x ∈ leftFirst.block, valuation x = 4 := by
        intro x member
        apply insideFour anchorSlot anchorMember x
        rw [anchorBlock, original.1]
        exact member
      have rightFive : ∀ x ∈ rightFirst.block, valuation x = 5 := by
        intro x member
        apply outsideFive otherSlot otherMember x
        rw [otherBlock, original.2]
        exact member
      rcases incompatible acc with killed | killed
      · exact nonzero (leftWitness.first_block_zero valuation acc 4 leftFour killed)
      · exact nonzero ((same valuation acc).trans (rightWitness.first_block_zero valuation acc 5 rightFive killed))
    · have leftFive : ∀ x ∈ leftFirst.block, valuation x = 5 := by
        intro x member
        apply outsideFive otherSlot otherMember x
        rw [otherBlock, switched.2]
        exact member
      have rightFour : ∀ x ∈ rightFirst.block, valuation x = 4 := by
        intro x member
        apply insideFour anchorSlot anchorMember x
        rw [anchorBlock, switched.1]
        exact member
      rcases incompatible acc with killed | killed
      · exact nonzero ((same valuation acc).trans (rightWitness.first_block_zero valuation acc 4 rightFour killed))
      · exact nonzero (leftWitness.first_block_zero valuation acc 5 leftFive killed)

private theorem slot_eq_of_fields (left right : Slot)
    (gaps : left.gap = right.gap) (blocks : left.block = right.block) : left = right := by
  cases left
  cases right
  cases gaps
  cases blocks
  rfl

private theorem map_recover_slots (recover : List Nat → Slot) :
    ∀ chain : List Slot, (∀ slot ∈ chain, recover slot.gap = slot) →
      (chain.map Slot.gap).map recover = chain
  | [], _ => rfl
  | head :: tail, fixed => by
      simp only [List.map_cons, fixed head (List.Mem.head tail)]
      exact congrArg (List.cons head) (map_recover_slots recover tail
        (fun slot member => fixed slot (List.Mem.tail head member)))

theorem canonicalRestPermutation {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) : leftRest.Perm rightRest := by
  classical
  have gapPermutation := (canonicalGapPermutation same leftWitness rightWitness).1
  let recover (gap : List Nat) : Slot :=
    if found : ∃ slot ∈ leftRest, slot.gap = gap then Classical.choose found else ⟨gap, []⟩
  have fixedLeft : ∀ slot ∈ leftRest, recover slot.gap = slot := by
    intro slot member
    have found : ∃ chosen ∈ leftRest, chosen.gap = slot.gap := ⟨slot, member, rfl⟩
    have properties := Classical.choose_spec found
    have blocks := leftWitness.same_block_after_equal_gap leftWitness (SameEval.refl left.toList)
      (Classical.choose found) slot properties.1 member properties.2
    simp only [recover, dif_pos found]
    exact slot_eq_of_fields _ _ properties.2 blocks
  have fixedRight : ∀ slot ∈ rightRest, recover slot.gap = slot := by
    intro slot member
    have gapMember : slot.gap ∈ leftRest.map Slot.gap :=
      gapPermutation.mem_iff.mpr (List.mem_map.mpr ⟨slot, member, rfl⟩)
    have found : ∃ chosen ∈ leftRest, chosen.gap = slot.gap := List.mem_map.mp gapMember
    have properties := Classical.choose_spec found
    have blocks := leftWitness.same_block_after_equal_gap rightWitness same
      (Classical.choose found) slot properties.1 member properties.2
    simp only [recover, dif_pos found]
    exact slot_eq_of_fields _ _ properties.2 blocks
  have recovered := gapPermutation.map recover
  rwa [map_recover_slots recover leftRest fixedLeft, map_recover_slots recover rightRest fixedRight] at recovered

theorem canonicalChainPermutation {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) :
    (leftFirst :: leftRest).Perm (rightFirst :: rightRest) := by
  have firstEqual := slot_eq_of_fields leftFirst rightFirst
    (leftWitness.2.2.2.2.1.trans rightWitness.2.2.2.2.1.symm)
    (leftWitness.same_first_block rightWitness same)
  rw [firstEqual]
  exact (canonicalRestPermutation same leftWitness rightWitness).cons rightFirst

theorem canonicalBlockPermutation {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) :
    ((leftFirst :: leftRest).map Slot.block).Perm ((rightFirst :: rightRest).map Slot.block) :=
  (canonicalChainPermutation same leftWitness rightWitness).map Slot.block

def PrecedesGap (chain : List Slot) (block gap : List Nat) : Prop :=
  ∃ before slot next after, chain = before ++ slot :: next :: after ∧ slot.block = block ∧ next.gap = gap

private theorem successor_mem_rest (first : Slot) (rest before : List Slot) (slot next : Slot) (after : List Slot)
    (shape : first :: rest = before ++ slot :: next :: after) : next ∈ rest := by
  cases before with
  | nil =>
      have tailShape : rest = next :: after := (List.cons.inj shape).2
      rw [tailShape]
      exact List.Mem.head _
  | cons head tail =>
      have tailShape : rest = tail ++ slot :: next :: after := (List.cons.inj shape).2
      rw [tailShape]
      simp

private theorem exists_predecessor (first : Slot) (rest : List Slot) (slot : Slot) (member : slot ∈ rest) :
    ∃ before previous after, first :: rest = before ++ previous :: slot :: after := by
  induction rest generalizing first with
  | nil => cases member
  | cons next tail ih =>
      rcases List.mem_cons.mp member with equal | inTail
      · subst slot
        exact ⟨[], first, tail, rfl⟩
      · obtain ⟨before, previous, after, shape⟩ := ih next inTail
        exact ⟨first :: before, previous, after, congrArg (List.cons first) shape⟩

private theorem precedesGap_forward {left right leftAlphabet rightAlphabet : List Nat}
    {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (leftWitness : CanonicalWitness left leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right rightAlphabet rightFirst rightRest) (same : SameEval left right)
    (restPermutation : leftRest.Perm rightRest) (block gap : List Nat)
    (present : PrecedesGap (leftFirst :: leftRest) block gap) : PrecedesGap (rightFirst :: rightRest) block gap := by
  obtain ⟨leftBefore, leftSlot, next, leftAfter, leftShape, blockEqual, gapEqual⟩ := present
  have nextMember := successor_mem_rest leftFirst leftRest leftBefore leftSlot next leftAfter leftShape
  obtain ⟨rightBefore, rightSlot, rightAfter, rightShape⟩ :=
    exists_predecessor rightFirst rightRest next (restPermutation.mem_iff.mp nextMember)
  have equal := leftWitness.same_block_before_equal_gap rightWitness same leftBefore leftSlot next leftAfter
    rightBefore rightSlot next rightAfter leftShape rightShape rfl
  exact ⟨rightBefore, rightSlot, next, rightAfter, rightShape, equal.symm.trans blockEqual, gapEqual⟩

theorem canonicalSimpleBlockAdjacency {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) (gap block : List Nat) :
    ((∃ slot ∈ leftRest, slot.gap = gap ∧ slot.block = block) ↔
      (∃ slot ∈ rightRest, slot.gap = gap ∧ slot.block = block)) ∧
    (PrecedesGap (leftFirst :: leftRest) block gap ↔ PrecedesGap (rightFirst :: rightRest) block gap) := by
  have permutation := canonicalRestPermutation same leftWitness rightWitness
  constructor
  · constructor
    · rintro ⟨slot, member, equal⟩
      exact ⟨slot, permutation.mem_iff.mp member, equal⟩
    · rintro ⟨slot, member, equal⟩
      exact ⟨slot, permutation.mem_iff.mpr member, equal⟩
  · exact ⟨precedesGap_forward leftWitness rightWitness same permutation block gap,
      precedesGap_forward rightWitness leftWitness same.symm permutation.symm block gap⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.first_block_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.same_first_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalRestPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalChainPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalBlockPermutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalSimpleBlockAdjacency

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
