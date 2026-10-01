import SemigroupBasis.CoRoots.Order6SporadicSection27F10Measured

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev ListDerives := S5_107.ListDerives basis

/-- The TWO alpha clauses of Proposition27.1; no beta adjacency clause. -/
structure AlphaCanonicalBlocks (blocks : List FirstOccurrenceGapBlock) : Prop where
  sparse : SparseBlocks [] blocks
  noCrossing : ¬ Has27Crossing (gapBlockMarkers blocks) (renderGapBlocks blocks)

/-- A literal crossing is repaired using F10's own eighteen-law basis. -/
theorem crossing_derives {markers source : List Nat}
    (witness : CrossingWitness markers source) :
    ListDerives source witness.target := by
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [CrossingWitness.target] using
    listDerivesDDisplayed witness.earlier witness.later witness.pre
      witness.gapOne witness.gapTwo witness.gapThree witness.post

/-- Every D repair lowers the rank sum strictly; A-C re-sparsification never
increases it. Thus this recursion has no word or alphabet bound. -/
theorem listDerivesSparseToAlphaCanonicalBlocks
    (markers : List Nat) (markersNodup : markers.Nodup) :
    ∀ (blocks : List FirstOccurrenceGapBlock),
      SparseBlocks [] blocks → gapBlockMarkers blocks = markers →
      ∃ canonicalBlocks, AlphaCanonicalBlocks canonicalBlocks ∧
        gapBlockMarkers canonicalBlocks = markers ∧
        ListDerives (renderGapBlocks blocks) (renderGapBlocks canonicalBlocks)
  | blocks, sparse, markerSequence => by
      classical
      have sourceSequence :
          firstOccurrenceSequenceList (renderGapBlocks blocks) = markers := by
        calc
          firstOccurrenceSequenceList (renderGapBlocks blocks) =
              gapBlockMarkers blocks :=
            firstOccurrenceSequenceList_renderGapBlocks sparse.wellFormed
          _ = markers := markerSequence
      by_cases crossing : Has27Crossing markers (renderGapBlocks blocks)
      · obtain ⟨witness⟩ := crossing.nonemptyWitness markersNodup
        obtain ⟨repairedBlocks, repairedSparse, repairedSequenceRaw,
            resparsify, resparsifyWeight⟩ :=
          listDerivesToSparseBlocksMeasured markers witness.target
        have repairedSequence : gapBlockMarkers repairedBlocks = markers := by
          calc
            gapBlockMarkers repairedBlocks = firstOccurrenceSequenceList witness.target :=
              repairedSequenceRaw
            _ = firstOccurrenceSequenceList (renderGapBlocks blocks) :=
              witness.firstOccurrenceSequenceList_target
            _ = markers := sourceSequence
        have decrease :
            betaWeight markers (renderGapBlocks repairedBlocks) <
              betaWeight markers (renderGapBlocks blocks) :=
          Nat.lt_of_le_of_lt resparsifyWeight witness.weight_lt
        obtain ⟨canonicalBlocks, canonical, canonicalSequence, recurse⟩ :=
          listDerivesSparseToAlphaCanonicalBlocks markers markersNodup
            repairedBlocks repairedSparse repairedSequence
        exact ⟨canonicalBlocks, canonical, canonicalSequence,
          (crossing_derives witness).trans (resparsify.trans recurse)⟩
      · refine ⟨blocks, ⟨sparse, ?_⟩, markerSequence, S5_107.ListDerives.refl _⟩
        simpa [markerSequence] using crossing
termination_by blocks _ _ => betaWeight markers (renderGapBlocks blocks)
decreasing_by assumption

/-- Unrestricted alpha normalization for exactly F10's eighteen laws. -/
theorem listDerivesToAlphaCanonicalBlocks (letters : List Nat) :
    ∃ canonicalBlocks, AlphaCanonicalBlocks canonicalBlocks ∧
      gapBlockMarkers canonicalBlocks = firstOccurrenceSequenceList letters ∧
      ListDerives letters (renderGapBlocks canonicalBlocks) := by
  let markers := firstOccurrenceSequenceList letters
  obtain ⟨sparseBlocks, sparse, sparseSequenceRaw, sparsify, _⟩ :=
    listDerivesToSparseBlocksMeasured markers letters
  have sparseSequence : gapBlockMarkers sparseBlocks = markers := sparseSequenceRaw
  have markersNodup : markers.Nodup := by
    rw [← sparseSequence]
    exact sparse.markersNodup
  obtain ⟨canonicalBlocks, canonical, canonicalSequence, normalize⟩ :=
    listDerivesSparseToAlphaCanonicalBlocks markers markersNodup
      sparseBlocks sparse sparseSequence
  exact ⟨canonicalBlocks, canonical, canonicalSequence, sparsify.trans normalize⟩

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.crossing_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesSparseToAlphaCanonicalBlocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.listDerivesToAlphaCanonicalBlocks
