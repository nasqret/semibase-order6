import SemigroupBasis.CoRoots.Order6SporadicSection18LoopExchange
import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationAnchors

/-! Canonical preservation by semantic rigidity of saturation. A semantically
valid permutation of the original nonempty, normalized blocks cannot acquire
new larger blocks: canonical block-set preservation and overlap closure force
every pointwise saturation inclusion to be equality. No completeness is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

private theorem slot_eq_of_parts (left right : Slot)
    (gaps : left.gap = right.gap) (blocks : left.block = right.block) : left = right := by
  cases left
  cases right
  cases gaps
  cases blocks
  rfl

theorem ChainExtends.rigid_in_family (family : List Slot)
    (nonempty : ∀ slot ∈ family, slot.block ≠ []) (overlap : OverlapClosed family)
    {input output : List Slot} (extended : ChainExtends input output) :
    (∀ slot ∈ input, slot ∈ family) →
    (∀ slot ∈ output, ∃ original ∈ family, original.block = slot.block) → input = output := by
  induction extended with
  | nil => intro _ _; rfl
  | @cons left right restLeft restRight head tail ih =>
      intro inputMember outputMember
      have leftMember := inputMember left (List.Mem.head restLeft)
      obtain ⟨original, originalMember, originalBlock⟩ := outputMember right (List.Mem.head restRight)
      obtain ⟨x, xs, shape⟩ := List.exists_cons_of_ne_nil (nonempty left leftMember)
      have xLeft : x ∈ left.block := by rw [shape]; simp
      have xOriginal : x ∈ original.block := by
        rw [originalBlock]
        exact head.2 x xLeft
      have blocks : left.block = right.block :=
        (overlapClosed_members family overlap left leftMember original originalMember x xLeft xOriginal).trans originalBlock
      have slots := slot_eq_of_parts left right head.1 blocks
      have restEqual := ih
        (fun slot member => inputMember slot (List.Mem.tail left member))
        (fun slot member => outputMember slot (List.Mem.tail right member))
      rw [slots, restEqual]

/-- Same first slot, a permutation of the remaining slots, and ACTUAL semantic
equivalence suffice to preserve the full CanonicalWitness. The proof saturates
independently, constructs a genuine canonical output witness, then proves the
entire saturation fixed point equal to the input by pointwise block rigidity. -/
theorem CanonicalWitness.permuted_of_sameEval {whole alphabet : List Nat} {first : Slot} {rest : List Slot}
    (witness : CanonicalWitness whole alphabet first rest) (newRest : List Slot)
    (permutation : newRest.Perm rest)
    (same : Actual.SameEval whole (render (first :: newRest))) :
    CanonicalWitness (render (first :: newRest)) alphabet first newRest := by
  have originalCanonical := witness.2.2.2.2.2.2.2.1
  have inputPermutation : (first :: newRest).Perm (first :: rest) := permutation.cons first
  have inputMember : ∀ slot ∈ first :: newRest, slot ∈ first :: rest :=
    fun slot member => inputPermutation.mem_iff.mp member
  have bounded : BoundedNonempty alphabet (first :: newRest) := by
    intro slot member
    have good := originalCanonical.1 slot (inputMember slot member)
    exact ⟨good.1, fun x present => good.bounded x present⟩
  obtain ⟨output, canonical, derivation, gaps, extended⟩ :=
    exists_saturated_squareChain_withAnchors alphabet (first :: newRest) bounded
  have semantic := same.trans (Actual.derives_sameEval derivation)
  cases output with
  | nil => cases extended
  | cons next tail =>
      have gapBoundary : first.gap :: newRest.map Slot.gap = next.gap :: tail.map Slot.gap := by
        simpa only [List.map_cons] using gaps
      have firstGap := (List.cons.inj gapBoundary).1
      have tailGaps := (List.cons.inj gapBoundary).2
      have outputWitness : CanonicalWitness (render (next :: tail)) alphabet next tail := by
        refine ⟨witness.1, witness.2.1, ?_, ?_, firstGap.symm.trans witness.2.2.2.2.1, ?_, ?_, canonical, rfl⟩
        · intro x
          constructor
          · intro inAlphabet
            have original := (witness.2.2.1 x).mp inAlphabet
            exact ⟨(semantic.mem x).mp original.1,
              fun one => original.2 ((semantic.countOne x).mpr one)⟩
          · rintro ⟨member, notOne⟩
            exact (witness.2.2.1 x).mpr ⟨(semantic.mem x).mpr member,
              fun one => notOne ((semantic.countOne x).mp one)⟩
        · intro empty
          have lengths := congrArg List.length tailGaps
          rw [empty] at lengths
          simp only [List.length_map, List.length_nil] at lengths
          have originalLength := permutation.length_eq
          exact witness.2.2.2.1 (List.eq_nil_of_length_eq_zero (by omega))
        · intro slot member empty
          have gapMember : slot.gap ∈ newRest.map Slot.gap := by
            rw [tailGaps]
            exact List.mem_map.mpr ⟨slot, member, rfl⟩
          obtain ⟨original, originalMember, gapEqual⟩ := List.mem_map.mp gapMember
          exact witness.2.2.2.2.2.1 original (permutation.mem_iff.mp originalMember) (gapEqual.trans empty)
        · intro slot member x inGap
          have gapMember : slot.gap ∈ (first :: newRest).map Slot.gap := by
            rw [gaps]
            exact List.mem_map.mpr ⟨slot, member, rfl⟩
          obtain ⟨original, originalMember, gapEqual⟩ := List.mem_map.mp gapMember
          have simple := witness.gap_simple original (inputMember original originalMember) x
            (by rw [gapEqual]; exact inGap)
          exact (semantic.countOne x).mp simple
      have outputMember : ∀ slot ∈ next :: tail, ∃ original ∈ first :: rest, original.block = slot.block := by
        intro slot member
        exact outputWitness.matching_block witness semantic.symm slot member
      have fixed := extended.rigid_in_family (first :: rest)
        (fun slot member => (originalCanonical.1 slot member).1) originalCanonical.2.1 inputMember outputMember
      have heads := (List.cons.inj fixed).1
      have tails := (List.cons.inj fixed).2
      subst next
      subst tail
      exact outputWitness

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ChainExtends.rigid_in_family
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.permuted_of_sameEval

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
