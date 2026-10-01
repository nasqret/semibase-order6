import SemigroupBasis.CoRoots.S5_107CanonicalDerivation
import SemigroupBasis.CoRoots.S5_107MarkerCombinatorics
import SemigroupBasis.CoRoots.S5_107ScannerEndpoints
import SemigroupBasis.CoRoots.S5_107SquareDedup

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- Extract the scanner blocks around any selected tail occurrence of the
anchor. The result retains the original nonempty block multiset and the
original marker multiset. -/
theorem listDerivesExtractTerminatedWithAnchor
    (first : List Nat × Nat)
    (tail : List (List Nat × Nat))
    (selected : List Nat × Nat)
    (final : List Nat)
    (anchor : Nat)
    (selectedMember : selected ∈ tail)
    (selectedMarker : selected.2 = anchor) :
    ListDerives basis
      (renderSquaredTerminatedBlocks (first :: tail) ++ final)
      (first.1 ++ [anchor] ++
        renderAnchoredBlocks anchor
          (nonemptyTerminatedBlocks tail) ++
        renderMultipleSquares
          (terminatedFactorMarkers (first :: tail)) ++
        final) := by
  rcases selected with ⟨selectedBlock, marker⟩
  simp only [Prod.snd] at selectedMarker
  subst marker
  let remainder :=
    tail.erase (selectedBlock, anchor)
  let nonempty :=
    blockBearingFactors remainder
  let empty :=
    markerOnlyFactors remainder
  let arranged :=
    nonempty ++ (selectedBlock, anchor) :: empty
  have tailPermutation :
      tail.Perm arranged := by
    simpa [remainder, nonempty, empty, arranged] using
      (perm_selected_factor_after_blockBearing selectedMember)
  have rearranged :=
    listDerivesSquaredTailPermutation
      tailPermutation first final
  have nonemptyBlocks :
      ∀ factor ∈ nonempty, factor.1 ≠ [] := by
    simpa [nonempty] using
      blockBearingFactors_blocks_nonempty remainder
  have emptyBlocks :
      ∀ factor ∈ empty, factor.1 = [] := by
    simpa [empty] using
      markerOnlyFactors_blocks_empty remainder
  have emptyRendering :
      renderSquaredTerminatedBlocks empty =
        renderMultipleSquares
          (terminatedFactorMarkers empty) :=
    renderSquaredTerminatedBlocks_eq_renderMultipleSquares_of_blocks_empty
      empty emptyBlocks
  have emptyNonemptyBlocks :
      nonemptyTerminatedBlocks empty = [] :=
    nonemptyTerminatedBlocks_eq_nil_of_blocks_empty
      empty emptyBlocks
  have nonemptyProjection :
      nonemptyTerminatedBlocks nonempty =
        terminatedFactorBlocks nonempty :=
    nonemptyTerminatedBlocks_eq_terminatedFactorBlocks_of_blocks_nonempty
      nonempty nonemptyBlocks
  by_cases selectedEmpty : selectedBlock = []
  · subst selectedBlock
    let sourceBlocks :=
      terminatedFactorBlocks nonempty
    let sourceMultiples :=
      anchor :: first.2 ::
        terminatedFactorMarkers nonempty ++
          terminatedFactorMarkers empty
    have extractedCore :=
      listDerivesAnchorFactorChainFromEmptyFactor
        first.1 first.2 anchor nonempty
        (renderSquaredTerminatedBlocks empty ++ final)
        nonemptyBlocks
    rw [emptyRendering] at extractedCore
    have extracted :
        ListDerives basis
          (renderSquaredTerminatedBlocks
              (first :: arranged) ++ final)
          (first.1 ++ [anchor] ++
            renderAnchoredBlocks anchor sourceBlocks ++
            renderMultipleSquares sourceMultiples ++ final) := by
      simpa [arranged, sourceBlocks, sourceMultiples,
        emptyRendering, renderSquaredTerminatedBlocks,
        terminatedFactorMarkers, renderMultipleSquares,
        List.append_assoc] using extractedCore
    have arrangedBlocks :
        nonemptyTerminatedBlocks arranged =
          sourceBlocks := by
      dsimp [arranged, sourceBlocks]
      rw [nonemptyTerminatedBlocks_append]
      change
        nonemptyTerminatedBlocks nonempty ++
            nonemptyTerminatedBlocks empty =
          terminatedFactorBlocks nonempty
      rw [nonemptyProjection, emptyNonemptyBlocks]
      simp
    have blockPermutation :
        sourceBlocks.Perm
          (nonemptyTerminatedBlocks tail) := by
      have projected :=
        nonemptyTerminatedBlocks_perm tailPermutation
      rw [arrangedBlocks] at projected
      exact projected.symm
    have sourceToArranged :
        sourceMultiples.Perm
          (terminatedFactorMarkers
            (first :: arranged)) := by
      have moved :=
        perm_cons_append anchor
          (first.2 :: terminatedFactorMarkers nonempty)
          (terminatedFactorMarkers empty)
      simpa [sourceMultiples, arranged,
        terminatedFactorMarkers, List.append_assoc] using moved
    have arrangedToOriginal :
        (terminatedFactorMarkers
            (first :: arranged)).Perm
          (terminatedFactorMarkers
            (first :: tail)) :=
      terminatedFactorMarkers_perm <|
        (List.Perm.cons first tailPermutation).symm
    have multiplePermutation :
        sourceMultiples.Perm
          (terminatedFactorMarkers
            (first :: tail)) :=
      sourceToArranged.trans arrangedToOriginal
    have sourceBlocksNonempty :
        ∀ block ∈ sourceBlocks, block ≠ [] := by
      intro block member
      exact
        nonemptyTerminatedBlocks_blocks_nonempty tail
          block (blockPermutation.mem_iff.mp member)
    have reordered :=
      listDerivesRenderedCanonicalCore
        first.1 final anchor
        blockPermutation multiplePermutation
        sourceBlocksNonempty
    exact rearranged.trans (extracted.trans reordered)
  · obtain ⟨selectedHead, selectedTail, selectedShape⟩ :=
      List.exists_cons_of_ne_nil selectedEmpty
    subst selectedBlock
    let sourceBlocks :=
      terminatedFactorBlocks nonempty ++
        [selectedHead :: selectedTail]
    let sourceMultiples :=
      first.2 ::
        terminatedFactorMarkers nonempty ++
          [anchor] ++ terminatedFactorMarkers empty
    have extractedCore :=
      listDerivesAnchorNonemptyFactorChainRetainingSquare
        first.1 first.2 anchor nonempty
        selectedHead selectedTail
        (renderSquaredTerminatedBlocks empty ++ final)
        nonemptyBlocks
    rw [emptyRendering] at extractedCore
    have extracted :
        ListDerives basis
          (renderSquaredTerminatedBlocks
              (first :: arranged) ++ final)
          (first.1 ++ [anchor] ++
            renderAnchoredBlocks anchor sourceBlocks ++
            renderMultipleSquares sourceMultiples ++ final) := by
      simpa [arranged, sourceBlocks, sourceMultiples,
        emptyRendering, renderSquaredTerminatedBlocks,
        terminatedFactorMarkers, renderMultipleSquares,
        List.append_assoc] using extractedCore
    have arrangedBlocks :
        nonemptyTerminatedBlocks arranged =
          sourceBlocks := by
      simp [arranged, sourceBlocks, nonemptyProjection,
        emptyNonemptyBlocks, nonemptyTerminatedBlocks]
    have blockPermutation :
        sourceBlocks.Perm
          (nonemptyTerminatedBlocks tail) := by
      have projected :=
        nonemptyTerminatedBlocks_perm tailPermutation
      rw [arrangedBlocks] at projected
      exact projected.symm
    have sourceToArranged :
        sourceMultiples.Perm
          (terminatedFactorMarkers
            (first :: arranged)) := by
      simpa [sourceMultiples, arranged,
        terminatedFactorMarkers, List.append_assoc] using
          (List.Perm.refl sourceMultiples)
    have arrangedToOriginal :
        (terminatedFactorMarkers
            (first :: arranged)).Perm
          (terminatedFactorMarkers
            (first :: tail)) :=
      terminatedFactorMarkers_perm <|
        (List.Perm.cons first tailPermutation).symm
    have multiplePermutation :
        sourceMultiples.Perm
          (terminatedFactorMarkers
            (first :: tail)) := by
      simpa [sourceMultiples, arranged,
        terminatedFactorMarkers, List.append_assoc] using
          sourceToArranged.trans arrangedToOriginal
    have sourceBlocksNonempty :
        ∀ block ∈ sourceBlocks, block ≠ [] := by
      intro block member
      exact
        nonemptyTerminatedBlocks_blocks_nonempty tail
          block (blockPermutation.mem_iff.mp member)
    have reordered :=
      listDerivesRenderedCanonicalCore
        first.1 final anchor
        blockPermutation multiplePermutation
        sourceBlocksNonempty
    exact rearranged.trans (extracted.trans reordered)

/-- Every word with a multiple variable derives to an anchored rendering
using exactly the scanner's interior blocks and one square per scanner marker
occurrence. -/
theorem listDerivesExtractScannerCanonicalCore
    (letters : List Nat)
    (anchor : Nat)
    (remainingMultiples : List Nat)
    (multiplesShape :
      sortedMultipleLetters letters =
        anchor :: remainingMultiples) :
    ListDerives basis letters
      (initialSimpleBlock letters ++ [anchor] ++
        renderAnchoredBlocks anchor
          (interiorSimpleBlocks letters) ++
        renderMultipleSquares
          (terminatedFactorMarkers
            (terminatedBlocks letters)) ++
        finalSimpleBlock letters) := by
  have anchorMultiple :
      2 ≤ letters.count anchor :=
    (sortedMultipleLetters_mem_iff anchor letters).mp <| by
      rw [multiplesShape]
      simp
  have markerMember :
      anchor ∈
        terminatedFactorMarkers
          (terminatedBlocks letters) :=
    (mem_terminatedFactorMarkers_iff
      anchor letters).mpr anchorMultiple
  have factorsNonempty :
      terminatedBlocks letters ≠ [] := by
    intro factorsEmpty
    rw [factorsEmpty] at markerMember
    simp [terminatedFactorMarkers] at markerMember
  obtain ⟨first, tail, factorsShape⟩ :=
    List.exists_cons_of_ne_nil factorsNonempty
  obtain ⟨selected, selectedMember, selectedMarker⟩ :=
    exists_tail_factor_with_marker_of_multiple
      letters first tail anchor factorsShape anchorMultiple
  have squared :=
    listDerivesSquareAllTerminatedMarkers letters
  have extracted :=
    listDerivesExtractTerminatedWithAnchor
      first tail selected
      (terminatedFinalBlock letters)
      anchor selectedMember selectedMarker
  have endpoints :=
    terminatedBlocks_cons_endpoint_blocks
      letters first tail factorsShape
  have finalEndpoint :=
    terminatedFinalBlock_eq_finalSimpleBlock letters
  rw [factorsShape] at squared
  have combined := squared.trans extracted
  simpa [endpoints.1, endpoints.2, finalEndpoint,
    factorsShape] using combined

/-- Unrestricted list-level canonicalization for the `S5_107` basis. -/
theorem listDerivesToSimpleAdjacencyCanonicalList
    (letters : List Nat) :
    ListDerives basis letters
      (simpleAdjacencyCanonicalList letters) := by
  cases multiplesShape :
      sortedMultipleLetters letters with
  | nil =>
      exact
        listDerivesToSimpleAdjacencyCanonicalListOfNoMultiples
          letters multiplesShape
  | cons anchor remainingMultiples =>
      have extractedOccurrences :=
        listDerivesExtractScannerCanonicalCore
          letters anchor remainingMultiples multiplesShape
      have deduplicatedSquares :=
        (listDerivesMultipleSquareDedup
          (terminatedFactorMarkers
            (terminatedBlocks letters))).context
          (initialSimpleBlock letters ++ [anchor] ++
            renderAnchoredBlocks anchor
              (interiorSimpleBlocks letters))
          (finalSimpleBlock letters)
      have extracted :
          ListDerives basis letters
            (initialSimpleBlock letters ++ [anchor] ++
              renderAnchoredBlocks anchor
                (interiorSimpleBlocks letters) ++
              renderMultipleSquares
                (distinctLetters
                  (terminatedFactorMarkers
                    (terminatedBlocks letters))) ++
              finalSimpleBlock letters) := by
        exact extractedOccurrences.trans <| by
          simpa [List.append_assoc] using deduplicatedSquares
      have blockPermutation :
          (interiorSimpleBlocks letters).Perm
            (sortedSimpleBlocks
              (interiorSimpleBlocks letters)) := by
        unfold sortedSimpleBlocks
        exact (List.mergeSort_perm _ _).symm
      have multiplePermutation :
          (distinctLetters
              (terminatedFactorMarkers
                (terminatedBlocks letters))).Perm
            (anchor :: remainingMultiples) := by
        have markers :=
          distinctTerminatedMarkers_perm_sortedMultipleLetters
            letters
        rwa [multiplesShape] at markers
      exact
        listDerivesToSimpleAdjacencyCanonicalListOfExtracted
          letters anchor remainingMultiples
          (interiorSimpleBlocks letters)
          (distinctLetters
            (terminatedFactorMarkers
              (terminatedBlocks letters)))
          multiplesShape extracted blockPermutation
          multiplePermutation <| by
            intro block member
            exact
              simpleBlocks_blocks_nonempty letters
                block
                ((mem_interiorSimpleBlocks_iff
                  letters block).mp member).1

/-- Every word derives to the deterministic simple-adjacency canonical word. -/
theorem derivesCanonicalUnrestricted
    (word : Word Nat) :
    Derives basis word
      (simpleAdjacencyCanonicalWord word) :=
  derivesCanonical word <|
    listDerivesToSimpleAdjacencyCanonicalList word.toList

end SemigroupBasis.CoRoots.S5_107
