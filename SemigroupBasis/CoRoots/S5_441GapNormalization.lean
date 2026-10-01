import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCanonical
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeComponents
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeInteriorNormalize
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeRetarget

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

private theorem support_iff_of_positiveParityReduce_perm
    {left right : List Nat}
    (permutation :
      (positiveParityReduce left).Perm
        (positiveParityReduce right))
    (tested : Nat) :
    tested ∈ left ↔ tested ∈ right := by
  rw [← mem_positiveParityReduce_iff tested left,
    ← mem_positiveParityReduce_iff tested right]
  exact permutation.mem_iff

private theorem count_mod_two_eq_of_positiveParityReduce_perm
    {left right : List Nat}
    (permutation :
      (positiveParityReduce left).Perm
        (positiveParityReduce right))
    (tested : Nat) :
    left.count tested % 2 = right.count tested % 2 := by
  have reducedCount :=
    (List.perm_iff_count.mp permutation) tested
  calc
    left.count tested % 2 =
        (positiveParityReduce left).count tested % 2 :=
      (positiveParityReduce_count_mod_two tested left).symm
    _ = (positiveParityReduce right).count tested % 2 :=
      congrArg (fun count => count % 2) reducedCount
    _ = right.count tested % 2 :=
      positiveParityReduce_count_mod_two tested right

private theorem parityEnvelopeReducedProfile_perm_support_iff
    {leftEndpoint rightEndpoint : Nat}
    {leftInterior rightInterior : List Nat}
    (permutation :
      (parityEnvelopeReducedProfile
        leftEndpoint leftInterior).Perm
        (parityEnvelopeReducedProfile
          rightEndpoint rightInterior))
    (tested : Nat) :
    tested ∈ parityEnvelopeRender leftEndpoint leftInterior [] ↔
      tested ∈
        parityEnvelopeRender rightEndpoint rightInterior [] :=
  support_iff_of_positiveParityReduce_perm permutation tested

private theorem parityEnvelopeReducedProfile_perm_count_mod_two
    {leftEndpoint rightEndpoint : Nat}
    {leftInterior rightInterior : List Nat}
    (permutation :
      (parityEnvelopeReducedProfile
        leftEndpoint leftInterior).Perm
        (parityEnvelopeReducedProfile
          rightEndpoint rightInterior))
    (tested : Nat) :
    (parityEnvelopeRender leftEndpoint leftInterior []).count tested % 2 =
      (parityEnvelopeRender
        rightEndpoint rightInterior []).count tested % 2 :=
  count_mod_two_eq_of_positiveParityReduce_perm permutation tested

/-- Every nonempty exact-cut-free gap derives to its deterministic canonical
gap. The proof first folds support components to one envelope, normalizes the
interior at that endpoint, retargets to the least supported endpoint when
needed, and finally normalizes to `canonicalGap`. -/
theorem listDerivesCanonicalGap_of_no_exactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right) :
    ListDerives gap (canonicalGap gap) := by
  by_cases gapEmpty : gap = []
  · subst gap
    simpa [canonicalGap_nil] using ListDerives.refl []
  obtain
    ⟨endpoint, interior, gapToEnvelope, gapPermutation⟩ :=
      exists_parityEnvelopeDerivation_of_no_exactCut
        noExactCut gapEmpty
  have endpointMember : endpoint ∈ gap := by
    apply gapPermutation.mem_iff.mpr
    simp [parityEnvelopeRender]
  have envelopeToEndpointCanonical :
      ListDerives
        (parityEnvelopeRender endpoint interior [])
        (parityEnvelopeCanonical gap endpoint) := by
    apply
      listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
    · intro tested
      exact
        gapPermutation.mem_iff.symm.trans
          (parityEnvelopeCanonical_mem_iff
            endpointMember tested).symm
    · intro tested
      have gapEnvelopeCount :=
        (List.perm_iff_count.mp gapPermutation) tested
      calc
        (parityEnvelopeRender endpoint interior []).count tested % 2 =
            gap.count tested % 2 :=
          congrArg (fun count => count % 2) gapEnvelopeCount.symm
        _ = (parityEnvelopeCanonical gap endpoint).count tested % 2 :=
          (parityEnvelopeCanonical_count_mod_two
            endpointMember tested).symm
  have gapToEndpointCanonical :
      ListDerives gap (parityEnvelopeCanonical gap endpoint) :=
    ListDerives.trans gapToEnvelope
      envelopeToEndpointCanonical
  have supportNonempty :
      connectedComponentSortedSupport gap ≠ [] :=
    connectedComponentSortedSupport_nonempty gapEmpty
  obtain ⟨anchor, payloadSupport, supportShape⟩ :=
    List.exists_cons_of_ne_nil supportNonempty
  have anchorMember : anchor ∈ gap :=
    canonicalGap_anchor_mem supportShape
  by_cases endpointEqAnchor : endpoint = anchor
  · subst endpoint
    simpa [
      parityEnvelopeCanonical_eq_canonicalGap supportShape
    ] using gapToEndpointCanonical
  have anchorInteriorMember :
      anchor ∈ parityEnvelopeCanonicalInterior gap endpoint := by
    rw [← List.count_pos_iff,
      parityEnvelopeCanonicalInterior_count_nonendpoint
        anchorMember (Ne.symm endpointEqAnchor)]
    split <;> omega
  have endpointCanonicalReduced :
      ParityEnvelopeInteriorReduced endpoint
        (parityEnvelopeCanonicalInterior gap endpoint) :=
    { endpoint_count_le_one :=
        parityEnvelopeCanonicalInterior_endpoint_count_le_one
          gap endpoint
      other_count_le_two := fun tested _ =>
        parityEnvelopeCanonicalInterior_count_le_two
          gap endpoint tested }
  obtain
    ⟨anchorInterior, endpointToAnchor,
      reducedProfilePermutation, _anchorReduced⟩ :=
        exists_reducedParityEnvelopeRetarget
          endpointEqAnchor anchorInteriorMember
          endpointCanonicalReduced
  have anchorEnvelopeToCanonical :
      ListDerives
        (parityEnvelopeRender anchor anchorInterior [])
        (parityEnvelopeCanonical gap anchor) := by
    apply
      listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
    · intro tested
      exact
        (parityEnvelopeReducedProfile_perm_support_iff
          reducedProfilePermutation tested).symm.trans <|
          (parityEnvelopeCanonical_mem_iff
            endpointMember tested).trans <|
            (parityEnvelopeCanonical_mem_iff
              anchorMember tested).symm
    · intro tested
      exact
        (parityEnvelopeReducedProfile_perm_count_mod_two
          reducedProfilePermutation tested).symm.trans <|
          (parityEnvelopeCanonical_count_mod_two
            endpointMember tested).trans <|
            (parityEnvelopeCanonical_count_mod_two
              anchorMember tested).symm
  have gapToAnchorCanonical :
      ListDerives gap (parityEnvelopeCanonical gap anchor) :=
    ListDerives.trans gapToEndpointCanonical <|
      ListDerives.trans endpointToAnchor
        anchorEnvelopeToCanonical
  simpa [
    parityEnvelopeCanonical_eq_canonicalGap supportShape
  ] using gapToAnchorCanonical

/-- Every gap emitted by the deterministic exact-cut decomposition derives
to its own canonical gap. -/
theorem exactCutDecomposition_gap_derives_canonicalGap
    {letters : List Nat} {segment : ExactCutSegment}
    (segmentMember :
      segment ∈ exactCutDecomposition letters) :
    ListDerives segment.gap (canonicalGap segment.gap) :=
  listDerivesCanonicalGap_of_no_exactCut
    (exactCutDecomposition_gap_no_exactCut segmentMember)

end SemigroupBasis.CoRoots.S5_441
