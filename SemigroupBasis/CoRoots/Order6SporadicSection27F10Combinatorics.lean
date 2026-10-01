import SemigroupBasis.CoRoots.Order6SporadicSection27F10Normalization
import SemigroupBasis.CoRoots.Order6SporadicSection27BetaBlockCombinatorics

/-! Basis-independent block facts for the TWO-clause F10 alpha proof.
The least-difference and ordered-prefix witnesses are shared combinatorics;
no F9/G1 separator, extra E law, or adjacency-free premise is used here.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis.CoRoots.S5_870

theorem choice_member {allowed seconds : List Nat} (choice : ChoiceIn allowed seconds)
    {letter : Nat} (member : letter ∈ seconds) : letter ∈ allowed := by
  rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
  · simp [empty] at member
  · rw [shape] at member
    have equal : letter = selected := by simpa using member
    simpa [equal] using selectedAllowed

theorem marker_mem_render {blocks : List FirstOccurrenceGapBlock} {letter : Nat}
    (member : letter ∈ gapBlockMarkers blocks) : letter ∈ renderGapBlocks blocks := by
  induction blocks with
  | nil => simp [gapBlockMarkers] at member
  | cons block rest ih =>
      simp only [gapBlockMarkers, List.map_cons, List.mem_cons] at member
      simp only [renderGapBlocks, List.mem_cons, List.mem_append]
      rcases member with atMarker | inRest
      · exact Or.inl atMarker
      · exact Or.inr (Or.inr (ih inRest))

theorem sparse_mem_seen {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) {letter : Nat}
    (member : letter ∈ renderGapBlocks blocks) :
    letter ∈ seenAfterGapBlocks seen blocks := by
  induction sparse with
  | nil => simp [renderGapBlocks] at member
  | cons seen block rest _ choice _ ih =>
      simp only [renderGapBlocks, List.mem_cons, List.mem_append] at member
      rw [seenAfterGapBlocks_cons]
      rcases member with atMarker | inSeconds | inRest
      · subst letter
        simp [seenAfterGapBlocks]
      · exact List.mem_append.mpr (Or.inr (choice_member choice inSeconds))
      · exact ih inRest

theorem current_fresh {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) :
    d.leftBlock.marker ∉ renderGapBlocks d.commonPrefix := by
  intro member
  exact d.markerFresh (sparse_mem_seen d.leftPrefixSparse member)

theorem prefix_mem_seen {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) {letter : Nat}
    (member : letter ∈ renderGapBlocks d.commonPrefix) :
    letter ∈ d.leftBlock.marker :: seenAfterGapBlocks [] d.commonPrefix :=
  List.Mem.tail _ (sparse_mem_seen d.leftPrefixSparse member)

theorem selected_mem_prefix {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) {selected : Nat}
    (allowed : selected ∈ d.leftBlock.marker :: seenAfterGapBlocks [] d.commonPrefix)
    (different : selected ≠ d.leftBlock.marker) :
    selected ∈ renderGapBlocks d.commonPrefix := by
  have seen := (List.mem_cons.mp allowed).resolve_left different
  have marker : selected ∈ gapBlockMarkers d.commonPrefix := by
    simpa [seenAfterGapBlocks] using seen
  exact marker_mem_render marker

/-- Literal condition-(II), not an adjacent-pair or nested-arc surrogate. -/
theorem crossing_zone_disjoint
    {markers letters firstZone middleZone after : List Nat} {later : Nat}
    (noCrossing : ¬ Has27Crossing markers letters)
    (order : ∀ earlier, earlier ∈ firstZone → EarlierIn markers earlier later)
    (shape : letters = firstZone ++ [later] ++ middleZone ++ [later] ++ after) :
    ∀ letter, letter ∈ firstZone → letter ∉ middleZone := by
  intro letter inFirst inMiddle
  obtain ⟨before, firstGap, firstShape⟩ := List.mem_iff_append.mp inFirst
  obtain ⟨secondGap, thirdGap, middleShape⟩ := List.mem_iff_append.mp inMiddle
  apply noCrossing
  exact ⟨letter, later, before, firstGap, secondGap, thirdGap, after,
    order letter inFirst, by
      simpa [firstShape, middleShape, List.append_assoc] using shape⟩

theorem crossing_bridge_disjoint
    {markers letters firstZone bridgeTail after : List Nat} {later : Nat}
    (noCrossing : ¬ Has27Crossing markers letters)
    (laterAbsent : later ∉ firstZone)
    (order : ∀ earlier, earlier ∈ firstZone → EarlierIn markers earlier later)
    (shape : letters = firstZone ++ [later] ++ bridgeTail ++ [later] ++ after) :
    ∀ letter, letter ∈ later :: bridgeTail → letter ∉ firstZone := by
  intro letter member inFirst
  rcases List.mem_cons.mp member with equal | inMiddle
  · subst letter
    exact laterAbsent inFirst
  · exact crossing_zone_disjoint noCrossing order shape letter inFirst inMiddle

def swap_difference {seen : List Nat} {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks seen left right) :
    LeastDifferingSparseBlocks seen right left where
  commonPrefix := d.commonPrefix
  leftBlock := d.rightBlock
  rightBlock := d.leftBlock
  leftTail := d.rightTail
  rightTail := d.leftTail
  left_eq := d.right_eq
  right_eq := d.left_eq
  sameMarker := d.sameMarker.symm
  differentSeconds := fun equal => d.differentSeconds equal.symm
  tailMarkers_eq := d.tailMarkers_eq.symm
  leftPrefixSparse := d.rightPrefixSparse
  rightPrefixSparse := d.leftPrefixSparse
  markerFresh := by simpa only [d.sameMarker] using d.markerFresh
  leftChoice := by simpa only [d.sameMarker] using d.rightChoice
  rightChoice := by simpa only [d.sameMarker] using d.leftChoice
  leftTailSparse := by simpa only [d.sameMarker] using d.rightTailSparse
  rightTailSparse := by simpa only [d.sameMarker] using d.leftTailSparse

theorem oriented_cases {markers : List Nat} {current : Nat} {ls rs : List Nat}
    (oriented : OrientedChoiceDifference markers current ls rs) :
    (∃ selected, ls = [selected] ∧ rs = []) ∨
    (∃ selected, ls = [selected] ∧ rs = [current]) ∨
    (∃ earlier later, ls = [earlier] ∧ rs = [later] ∧
      EarlierIn markers earlier later ∧ EarlierIn markers later current) := by
  cases oriented with
  | selectedEmpty selected _ => exact Or.inl ⟨selected, rfl, rfl⟩
  | selectedCurrent selected _ => exact Or.inr (Or.inl ⟨selected, rfl, rfl⟩)
  | orderedSelected earlier later first second =>
      exact Or.inr (Or.inr ⟨earlier, later, rfl, rfl, first, second⟩)

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.choice_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.marker_mem_render
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.sparse_mem_seen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.current_fresh
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.prefix_mem_seen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.selected_mem_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.crossing_zone_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.crossing_bridge_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.swap_difference
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.oriented_cases
