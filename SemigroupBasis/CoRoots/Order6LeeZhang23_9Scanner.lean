import SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax
import SemigroupBasis.CoRoots.S5_107Extraction

/-!
# Lee--Zhang Proposition 23.9 successor-block scanner

This file is purely combinatorial.  It runs the established terminated-block
scanner on the reversed source list and translates the result back to the
orientation

`w₀ · x₁w₁ · ... · xᵣwᵣ`,

where each `xᵢ` is globally multiple and every letter of every `wᵢ` is
globally simple.  No derivation theorem for the fixed thirteen-law
`S5_402` basis is invoked or reused here.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner

open SemigroupBasis
open Order6LeeZhang23_9Syntax

/-- One globally multiple marker paired with the globally simple block that
immediately follows it in the original word orientation. -/
abbrev SuccessorFactor := Nat × List Nat

/-- Translate a terminated factor from the reversed scan back to the
successor-factor orientation. -/
def reverseTerminatedFactor
    (factor : List Nat × Nat) : SuccessorFactor :=
  (factor.2, factor.1.reverse)

/-- The initial globally simple block `w₀`.  It is the reversal of the
trailing simple block in the scan of the reversed source. -/
def initialSimpleBlock (letters : List Nat) : List Nat :=
  (S5_107.terminatedFinalBlock letters.reverse).reverse

/-- The ordered successor factors `(x₁,w₁),...,(xᵣ,wᵣ)`.  Reversing
both the source and the emitted factor order is essential: scanning the
original source directly records the wrong edge orientation for `FNS`. -/
def successorFactors (letters : List Nat) : List SuccessorFactor :=
  (S5_107.terminatedBlocks letters.reverse).reverse.map
    reverseTerminatedFactor

/-- The complete source-facing output of the reversed terminated scan. -/
structure SuccessorFactorization where
  initial : List Nat
  factors : List SuccessorFactor

/-- Package the initial block and ordered successor factors. -/
def successorFactorization
    (letters : List Nat) : SuccessorFactorization where
  initial := initialSimpleBlock letters
  factors := successorFactors letters

@[simp]
theorem successorFactorization_initial (letters : List Nat) :
    (successorFactorization letters).initial =
      initialSimpleBlock letters :=
  rfl

@[simp]
theorem successorFactorization_factors (letters : List Nat) :
    (successorFactorization letters).factors =
      successorFactors letters :=
  rfl

/-- Render one marker-followed-by-simple-block factor. -/
def renderSuccessorFactor (factor : SuccessorFactor) : List Nat :=
  factor.1 :: factor.2

/-- Render an ordered successor-factor list. -/
def renderSuccessorFactors : List SuccessorFactor → List Nat
  | [] => []
  | factor :: rest =>
      renderSuccessorFactor factor ++ renderSuccessorFactors rest

@[simp]
theorem renderSuccessorFactors_append
    (left right : List SuccessorFactor) :
    renderSuccessorFactors (left ++ right) =
      renderSuccessorFactors left ++ renderSuccessorFactors right := by
  induction left with
  | nil =>
      rfl
  | cons factor rest ih =>
      simp [renderSuccessorFactors, ih, List.append_assoc]

private theorem renderSuccessorFactors_reverseTerminated :
    ∀ factors : List (List Nat × Nat),
      renderSuccessorFactors
          (factors.reverse.map reverseTerminatedFactor) =
        (S5_107.renderTerminatedBlocks factors).reverse
  | [] => by
      rfl
  | (block, marker) :: rest => by
      rw [List.reverse_cons, List.map_append,
        renderSuccessorFactors_append,
        renderSuccessorFactors_reverseTerminated rest]
      simp [renderSuccessorFactors, renderSuccessorFactor,
        reverseTerminatedFactor, S5_107.renderTerminatedBlocks,
        List.reverse_append, List.append_assoc]

/-- The successor scan reconstructs the source list literally. -/
theorem reconstruct (letters : List Nat) :
    initialSimpleBlock letters ++
      renderSuccessorFactors (successorFactors letters) = letters := by
  unfold initialSimpleBlock successorFactors
  rw [renderSuccessorFactors_reverseTerminated,
    ← List.reverse_append,
    S5_107.terminatedBlocks_render,
    List.reverse_reverse]

/-- Structure-facing form of literal reconstruction. -/
theorem successorFactorization_render (letters : List Nat) :
    (successorFactorization letters).initial ++
      renderSuccessorFactors
        (successorFactorization letters).factors = letters := by
  simpa using reconstruct letters

/-- Exact membership bridge back to the pure terminated scan on the
reversed source. -/
theorem successorFactor_mem_iff_reversedTerminated
    (letters block : List Nat) (marker : Nat) :
    (marker, block) ∈ successorFactors letters ↔
      (block.reverse, marker) ∈
        S5_107.terminatedBlocks letters.reverse := by
  constructor
  · intro member
    obtain ⟨source, sourceMember, sourceMaps⟩ :=
      List.mem_map.mp member
    have sourceMember' := List.mem_reverse.mp sourceMember
    rcases source with ⟨sourceBlock, sourceMarker⟩
    simp only [reverseTerminatedFactor, Prod.mk.injEq] at sourceMaps
    rcases sourceMaps with ⟨markerEq, blockEq⟩
    subst marker
    subst block
    simpa using sourceMember'
  · intro member
    apply List.mem_map.mpr
    refine ⟨(block.reverse, marker), ?_, ?_⟩
    · exact List.mem_reverse.mpr member
    · simp [reverseTerminatedFactor]

/-- Every successor marker is globally multiple in the frozen source. -/
theorem successorFactor_marker_multiple
    (letters block : List Nat) (marker : Nat)
    (member : (marker, block) ∈ successorFactors letters) :
    2 ≤ letters.count marker := by
  have sourceMember :=
    (successorFactor_mem_iff_reversedTerminated
      letters block marker).mp member
  have multiple :=
    S5_107.terminatedBlocks_marker_multiple
      letters.reverse (block.reverse, marker) sourceMember
  simpa only [List.count_reverse] using multiple

/-- Every letter carried by a successor block is globally simple in the
frozen source. -/
theorem successorFactor_block_letter_simple
    (letters block : List Nat) (marker letter : Nat)
    (factorMember : (marker, block) ∈ successorFactors letters)
    (letterMember : letter ∈ block) :
    letters.count letter = 1 := by
  have sourceMember :=
    (successorFactor_mem_iff_reversedTerminated
      letters block marker).mp factorMember
  have sourceSimple :=
    S5_107.terminatedBlocks_block_simple
      letters.reverse (block.reverse, marker) sourceMember
      letter (List.mem_reverse.mpr letterMember)
  simpa only [List.count_reverse] using sourceSimple

/-- Every letter carried by the initial block is globally simple in the
frozen source. -/
theorem initialSimpleBlock_letter_simple
    (letters : List Nat) (letter : Nat)
    (member : letter ∈ initialSimpleBlock letters) :
    letters.count letter = 1 := by
  have sourceMember :
      letter ∈ S5_107.terminatedFinalBlock letters.reverse :=
    List.mem_reverse.mp member
  have sourceSimple :=
    S5_107.terminatedFinalBlock_letter_simple
      letters.reverse letter sourceMember
  simpa only [List.count_reverse] using sourceSimple

/-- Every displayed successor factor occurs as a literal
`... ++ marker :: block ++ ...` segment of the source. -/
theorem successorFactor_split
    (letters block : List Nat) (marker : Nat)
    (member : (marker, block) ∈ successorFactors letters) :
    ∃ before after,
      letters = before ++ marker :: block ++ after := by
  obtain ⟨beforeFactors, afterFactors, factorShape⟩ :=
    List.mem_iff_append.mp member
  refine
    ⟨initialSimpleBlock letters ++
        renderSuccessorFactors beforeFactors,
      renderSuccessorFactors afterFactors, ?_⟩
  calc
    letters = initialSimpleBlock letters ++
        renderSuccessorFactors (successorFactors letters) :=
      (reconstruct letters).symm
    _ = initialSimpleBlock letters ++
        renderSuccessorFactors
          (beforeFactors ++ (marker, block) :: afterFactors) := by
      rw [factorShape]
    _ = (initialSimpleBlock letters ++
          renderSuccessorFactors beforeFactors) ++
        marker :: block ++ renderSuccessorFactors afterFactors := by
      simp [renderSuccessorFactors, renderSuccessorFactor,
        List.append_assoc]

/-- A label occurs as a successor marker exactly when it is globally
multiple in the source. -/
theorem exists_successorFactor_iff_multiple
    (letters : List Nat) (marker : Nat) :
    (∃ block, (marker, block) ∈ successorFactors letters) ↔
      2 ≤ letters.count marker := by
  constructor
  · rintro ⟨block, member⟩
    exact successorFactor_marker_multiple
      letters block marker member
  · intro multiple
    have reversedMultiple : 2 ≤ letters.reverse.count marker := by
      simpa only [List.count_reverse] using multiple
    have markerMember :
        marker ∈
          S5_107.terminatedFactorMarkers
            (S5_107.terminatedBlocks letters.reverse) :=
      (S5_107.mem_terminatedFactorMarkers_iff
        marker letters.reverse).mpr reversedMultiple
    obtain ⟨source, sourceMember, sourceMarker⟩ :=
      List.mem_map.mp markerMember
    rcases source with ⟨sourceBlock, sourceMarker'⟩
    simp only [Prod.snd] at sourceMarker
    subst sourceMarker'
    refine ⟨sourceBlock.reverse, ?_⟩
    exact
      (successorFactor_mem_iff_reversedTerminated
        letters sourceBlock.reverse marker).mpr <| by
          simpa using sourceMember

/-- The successor-factor list is nonempty exactly when the source contains
a globally multiple label. -/
theorem successorFactors_ne_nil_iff_exists_multiple
    (letters : List Nat) :
    successorFactors letters ≠ [] ↔
      ∃ marker, 2 ≤ letters.count marker := by
  constructor
  · intro nonempty
    obtain ⟨factor, factorMember⟩ :=
      List.exists_mem_of_ne_nil
        (successorFactors letters) nonempty
    exact ⟨factor.1,
      successorFactor_marker_multiple
        letters factor.2 factor.1 factorMember⟩
  · rintro ⟨marker, multiple⟩ empty
    obtain ⟨block, member⟩ :=
      (exists_successorFactor_iff_multiple
        letters marker).mpr multiple
    rw [empty] at member
    exact List.not_mem_nil member

/-- Marker projection in original occurrence order. -/
def successorMarkers (letters : List Nat) : List Nat :=
  (successorFactors letters).map Prod.fst

/-- Membership in the marker projection is exactly global multiplicity. -/
theorem mem_successorMarkers_iff
    (letters : List Nat) (marker : Nat) :
    marker ∈ successorMarkers letters ↔
      2 ≤ letters.count marker := by
  constructor
  · intro member
    obtain ⟨factor, factorMember, factorMarker⟩ :=
      List.mem_map.mp member
    rcases factor with ⟨sourceMarker, block⟩
    simp only [Prod.fst] at factorMarker
    subst sourceMarker
    exact successorFactor_marker_multiple
      letters block marker factorMember
  · intro multiple
    obtain ⟨block, factorMember⟩ :=
      (exists_successorFactor_iff_multiple
        letters marker).mpr multiple
    exact List.mem_map.mpr
      ⟨(marker, block), factorMember, rfl⟩

/-! ## Published `FNS`/`FSS` coordinates exposed by the scan -/

/-- The first letter of every nonempty successor block gives one published
`FNS` edge from its globally multiple marker. -/
theorem successorFactor_head_fns
    (word : Word Nat) (marker next : Nat) (rest : List Nat)
    (member :
      (marker, next :: rest) ∈ successorFactors word.toList) :
    FNS word marker next := by
  have markerMultiple :=
    successorFactor_marker_multiple
      word.toList (next :: rest) marker member
  have nextSimple : word.toList.count next = 1 :=
    successorFactor_block_letter_simple
      word.toList (next :: rest) marker next member (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro markerSimple
    unfold S5_402.GloballySimple S5_107.SimpleIn at markerSimple
    omega
  · simpa [S5_402.GloballySimple, S5_107.SimpleIn] using nextSimple
  · apply (S5_107.mem_adjacentPairs_iff_exists_split
      marker next word).mpr
    obtain ⟨before, after, shape⟩ :=
      successorFactor_split
        word.toList (next :: rest) marker member
    exact ⟨before, rest ++ after, by
      simpa [List.append_assoc] using shape⟩

/-- Every directed edge internal to a successor block is a published `FSS`
edge of the source word. -/
theorem successorFactor_block_edge_fss
    (word : Word Nat) (marker source target : Nat)
    (block : List Nat)
    (factorMember :
      (marker, block) ∈ successorFactors word.toList)
    (edgeMember :
      (source, target) ∈ S5_107.listAdjacentPairs block) :
    FSS word source target := by
  obtain ⟨insideBefore, insideAfter, blockShape⟩ :=
    (S5_107.mem_listAdjacentPairs_iff_exists_split
      source target block).mp edgeMember
  have sourceMember : source ∈ block := by
    rw [blockShape]
    simp
  have targetMember : target ∈ block := by
    rw [blockShape]
    simp
  have sourceSimple :=
    successorFactor_block_letter_simple
      word.toList block marker source factorMember sourceMember
  have targetSimple :=
    successorFactor_block_letter_simple
      word.toList block marker target factorMember targetMember
  refine ⟨?_, ?_, ?_⟩
  · simpa [S5_402.GloballySimple, S5_107.SimpleIn] using sourceSimple
  · simpa [S5_402.GloballySimple, S5_107.SimpleIn] using targetSimple
  · apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word).mpr
    obtain ⟨before, after, wholeShape⟩ :=
      successorFactor_split
        word.toList block marker factorMember
    refine ⟨before ++ marker :: insideBefore,
      insideAfter ++ after, ?_⟩
    rw [wholeShape, blockShape]
    simp [List.append_assoc]

/-- Every directed edge internal to the initial simple block is a published
`FSS` edge of the source word. -/
theorem initialSimpleBlock_edge_fss
    (word : Word Nat) (source target : Nat)
    (edgeMember :
      (source, target) ∈
        S5_107.listAdjacentPairs
          (initialSimpleBlock word.toList)) :
    FSS word source target := by
  obtain ⟨before, after, blockShape⟩ :=
    (S5_107.mem_listAdjacentPairs_iff_exists_split
      source target (initialSimpleBlock word.toList)).mp edgeMember
  have sourceMember :
      source ∈ initialSimpleBlock word.toList := by
    rw [blockShape]
    simp
  have targetMember :
      target ∈ initialSimpleBlock word.toList := by
    rw [blockShape]
    simp
  have sourceSimple :=
    initialSimpleBlock_letter_simple
      word.toList source sourceMember
  have targetSimple :=
    initialSimpleBlock_letter_simple
      word.toList target targetMember
  refine ⟨?_, ?_, ?_⟩
  · simpa [S5_402.GloballySimple, S5_107.SimpleIn] using sourceSimple
  · simpa [S5_402.GloballySimple, S5_107.SimpleIn] using targetSimple
  · apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word).mpr
    refine ⟨before,
      after ++ renderSuccessorFactors
        (successorFactors word.toList), ?_⟩
    calc
      word.toList = initialSimpleBlock word.toList ++
          renderSuccessorFactors
            (successorFactors word.toList) :=
        (reconstruct word.toList).symm
      _ = (before ++ source :: target :: after) ++
          renderSuccessorFactors
            (successorFactors word.toList) := by
        rw [blockShape]
      _ = before ++ source :: target ::
          (after ++ renderSuccessorFactors
            (successorFactors word.toList)) := by
        simp [List.append_assoc]

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner
