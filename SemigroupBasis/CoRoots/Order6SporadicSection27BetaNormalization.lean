import SemigroupBasis.CoRoots.Order6SporadicSection27MeasuredSparsification

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## Terminating normalization of sparse beta blocks -/

/-- Starting from condition-(I) blocks with a fixed first-occurrence order,
repair the first available condition-(II) obstruction, otherwise the first
available condition-(III) obstruction.  Every repair is followed by measured
A/B/C sparsification, and the whole test is then repeated. -/
theorem listDerivesSparseToBetaCanonicalBlocks
    (markers : List Nat) (markersNodup : markers.Nodup) :
    ∀ (blocks : List FirstOccurrenceGapBlock),
      SparseBlocks [] blocks →
      gapBlockMarkers blocks = markers →
      ∃ canonicalBlocks,
        BetaCanonicalBlocks canonicalBlocks ∧
          gapBlockMarkers canonicalBlocks = markers ∧
          ListDerives
            (renderGapBlocks blocks)
            (renderGapBlocks canonicalBlocks)
  | blocks, sparse, markerSequence => by
      classical
      have sourceSequence :
          firstOccurrenceSequenceList (renderGapBlocks blocks) = markers := by
        calc
          firstOccurrenceSequenceList (renderGapBlocks blocks) =
              gapBlockMarkers blocks :=
            firstOccurrenceSequenceList_renderGapBlocks sparse.wellFormed
          _ = markers := markerSequence
      by_cases crossing :
          Has27Crossing markers (renderGapBlocks blocks)
      · obtain ⟨witness⟩ := crossing.nonemptyWitness markersNodup
        obtain ⟨repairedBlocks, repairedSparse, repairedSequenceRaw,
            resparsify, resparsifyWeight⟩ :=
          listDerivesToSparseBlocksMeasured markers witness.target
        have repairedSequence :
            gapBlockMarkers repairedBlocks = markers := by
          calc
            gapBlockMarkers repairedBlocks =
                firstOccurrenceSequenceList witness.target :=
              repairedSequenceRaw
            _ = firstOccurrenceSequenceList (renderGapBlocks blocks) :=
              witness.firstOccurrenceSequenceList_target
            _ = markers := sourceSequence
        have decrease :
            betaWeight markers (renderGapBlocks repairedBlocks) <
              betaWeight markers (renderGapBlocks blocks) :=
          Nat.lt_of_le_of_lt resparsifyWeight witness.weight_lt
        obtain ⟨canonicalBlocks, canonical, canonicalSequence, recurse⟩ :=
          listDerivesSparseToBetaCanonicalBlocks
            markers markersNodup repairedBlocks repairedSparse repairedSequence
        exact ⟨canonicalBlocks, canonical, canonicalSequence,
          witness.derives.trans (resparsify.trans recurse)⟩
      · by_cases adjacent :
            Has27AdjacentPair markers (renderGapBlocks blocks)
        · obtain ⟨witness⟩ := adjacent.nonemptyWitness markersNodup
          obtain ⟨repairedBlocks, repairedSparse, repairedSequenceRaw,
              resparsify, resparsifyWeight⟩ :=
            listDerivesToSparseBlocksMeasured markers witness.target
          have repairedSequence :
              gapBlockMarkers repairedBlocks = markers := by
            calc
              gapBlockMarkers repairedBlocks =
                  firstOccurrenceSequenceList witness.target :=
                repairedSequenceRaw
              _ = firstOccurrenceSequenceList (renderGapBlocks blocks) :=
                witness.firstOccurrenceSequenceList_target
              _ = markers := sourceSequence
          have decrease :
              betaWeight markers (renderGapBlocks repairedBlocks) <
                betaWeight markers (renderGapBlocks blocks) :=
            Nat.lt_of_le_of_lt resparsifyWeight witness.weight_lt
          obtain ⟨canonicalBlocks, canonical, canonicalSequence, recurse⟩ :=
            listDerivesSparseToBetaCanonicalBlocks
              markers markersNodup repairedBlocks repairedSparse repairedSequence
          exact ⟨canonicalBlocks, canonical, canonicalSequence,
            witness.derives.trans (resparsify.trans recurse)⟩
        · refine ⟨blocks, ?_, markerSequence, ?_⟩
          · exact {
              sparse := sparse
              noCrossing := by
                simpa [markerSequence] using crossing
              noAdjacentPair := by
                simpa [markerSequence] using adjacent
            }
          · exact S5_107.ListDerives.refl (basis := basis) _
termination_by blocks _ _ =>
  betaWeight markers (renderGapBlocks blocks)
decreasing_by
  all_goals assumption

/-! ## Top-level beta normalization -/

/-- Every list derives to literal Proposition 27.3 beta blocks.  The returned
marker equality records that normalization preserves the original
first-occurrence order. -/
theorem listDerivesToBetaCanonicalBlocks (letters : List Nat) :
    ∃ canonicalBlocks,
      BetaCanonicalBlocks canonicalBlocks ∧
        gapBlockMarkers canonicalBlocks =
          firstOccurrenceSequenceList letters ∧
        ListDerives letters (renderGapBlocks canonicalBlocks) := by
  let markers := firstOccurrenceSequenceList letters
  obtain ⟨sparseBlocks, sparse, sparseSequenceRaw,
      sparsify, _sparsifyWeight⟩ :=
    listDerivesToSparseBlocksMeasured markers letters
  have sparseSequence : gapBlockMarkers sparseBlocks = markers := by
    simpa [markers] using sparseSequenceRaw
  have markersNodup : markers.Nodup := by
    rw [← sparseSequence]
    exact sparse.markersNodup
  obtain ⟨canonicalBlocks, canonical, canonicalSequence, normalize⟩ :=
    listDerivesSparseToBetaCanonicalBlocks
      markers markersNodup sparseBlocks sparse sparseSequence
  exact ⟨canonicalBlocks, canonical, by simpa [markers] using canonicalSequence,
    sparsify.trans normalize⟩

end SemigroupBasis.CoRoots.Order6SporadicSection27
