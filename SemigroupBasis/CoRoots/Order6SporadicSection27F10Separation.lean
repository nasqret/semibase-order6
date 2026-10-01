import SemigroupBasis.CoRoots.Order6SporadicSection27F10Observations

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev Seen {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) :=
  d.leftBlock.marker :: seenAfterGapBlocks [] d.commonPrefix

theorem rendered_prefix_seen {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) {x : Nat}
    (member : x ∈ d.renderedPrefix) : x ∈ Seen d := by
  rcases List.mem_append.mp member with inPrefix | atCurrent
  · exact prefix_mem_seen d inPrefix
  · have equal : x = d.leftBlock.marker := List.mem_singleton.mp atCurrent
    simp [Seen, equal]

theorem difference_markers {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) :
    gapBlockMarkers left = gapBlockMarkers right := by
  rw [d.left_markerSequence_eq, d.right_markerSequence_eq, d.sameMarker, d.tailMarkers_eq]

theorem observe_split (v : Nat → Fin 6) (stem seconds : List Nat)
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) (future : ∀ x, x ∉ seen → v x = 5) :
    observe v (stem ++ seconds ++ renderGapBlocks blocks) =
      mul (scan v (scan v 3 stem) seconds) 5 := by
  unfold observe
  rw [scan_append, scan_append]
  exact finish_sparse sparse v future _

theorem observe_difference {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) (v : Nat → Fin 6)
    (future : ∀ x, x ∉ Seen d → v x = 5)
    (start : scan v 3 d.renderedPrefix = 1) :
    observe v (renderGapBlocks left) = mul (scan v 1 d.leftBlock.seconds) 5 ∧
      observe v (renderGapBlocks right) = mul (scan v 1 d.rightBlock.seconds) 5 := by
  constructor
  · rw [d.left_render_eq, observe_split v _ _ d.leftTailSparse future, start]
  · rw [d.right_render_eq, observe_split v _ _ d.rightTailSparse future, start]

def simpleValuation (stem : List Nat) (current : Nat) (active : Fin 6) (x : Nat) : Fin 6 :=
  if x ∈ stem then 3 else if x = current then active else 5

theorem simple_prefix_value {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) (active : Fin 6) {x : Nat}
    (member : x ∈ renderGapBlocks d.commonPrefix) :
    simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker active x = 3 := by
  simp only [simpleValuation, if_pos member]

theorem simple_current_value {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) (active : Fin 6) :
    simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker active d.leftBlock.marker = active := by
  simp [simpleValuation, current_fresh d]

theorem simple_future {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) (active : Fin 6) :
    ∀ x, x ∉ Seen d →
      simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker active x = 5 := by
  intro x fresh
  have absent : x ∉ renderGapBlocks d.commonPrefix := fun h => fresh (prefix_mem_seen d h)
  have different : x ≠ d.leftBlock.marker := by
    intro equal
    exact fresh (by simp [Seen, equal])
  simp only [simpleValuation, if_neg absent, if_neg different]

theorem simple_start {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) (active : Fin 6)
    (activeValue : mul 3 active = 1) :
    scan (simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker active)
      3 d.renderedPrefix = 1 := by
  let v := simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker active
  have prior : scan v 3 (renderGapBlocks d.commonPrefix) = 3 :=
    scan_fixed v 3 3 _ (fun _ member => simple_prefix_value d active member) (by decide)
  change scan v 3 (renderGapBlocks d.commonPrefix ++ [d.leftBlock.marker]) = 1
  rw [scan_append, prior, scan_cons, scan_nil]
  have atCurrent : v d.leftBlock.marker = active := simple_current_value d active
  rw [atCurrent]
  exact activeValue

/-- Paper Cases1 and2, including an empty common prefix and a terminal block. -/
theorem selected_empty_separates {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) {selected : Nat}
    (ls : d.leftBlock.seconds = [selected]) (rs : d.rightBlock.seconds = []) :
    ∃ v, observe v (renderGapBlocks left) = 0 ∧ observe v (renderGapBlocks right) = 2 := by
  let v := simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker 1
  have allowed : selected ∈ Seen d := choice_member d.leftChoice (by simp [ls])
  have selectedValue : v selected = 1 ∨ v selected = 3 := by
    by_cases equal : selected = d.leftBlock.marker
    · exact Or.inl (by simpa [equal] using simple_current_value d (1 : Fin 6))
    · exact Or.inr (simple_prefix_value d (1 : Fin 6) (selected_mem_prefix d allowed equal))
  have shapes := observe_difference d v (simple_future d 1) (simple_start d 1 (by decide))
  refine ⟨v, ?_, ?_⟩
  · rw [shapes.1, ls, scan_cons, scan_nil]
    rcases selectedValue with value | value <;> rw [value] <;> decide
  · rw [shapes.2, rs, scan_nil]
    decide

/-- Paper Case3 uses current=4 and previous letters=3, not a new identity. -/
theorem selected_current_separates {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right) {selected : Nat}
    (ls : d.leftBlock.seconds = [selected]) (rs : d.rightBlock.seconds = [d.leftBlock.marker]) :
    ∃ v, observe v (renderGapBlocks left) = 0 ∧ observe v (renderGapBlocks right) = 2 := by
  let v := simpleValuation (renderGapBlocks d.commonPrefix) d.leftBlock.marker 4
  have different : selected ≠ d.leftBlock.marker := by
    intro equal
    apply d.differentSeconds
    rw [ls, rs, equal]
  have allowed : selected ∈ Seen d := choice_member d.leftChoice (by simp [ls])
  have atSelected : v selected = 3 :=
    simple_prefix_value d (4 : Fin 6) (selected_mem_prefix d allowed different)
  have atCurrent : v d.leftBlock.marker = 4 := simple_current_value d (4 : Fin 6)
  have shapes := observe_difference d v (simple_future d 4) (simple_start d 4 (by decide))
  refine ⟨v, ?_, ?_⟩
  · rw [shapes.1, ls, scan_cons, scan_nil, atSelected]
    decide
  · rw [shapes.2, rs, scan_cons, scan_nil, atCurrent]
    decide

/-- Paper Case4. Condition(II) gives disjoint support zones on the right. -/
theorem ordered_selected_separates {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right)
    (noCrossing : ¬ Has27Crossing (gapBlockMarkers right) (renderGapBlocks right))
    {earlier later : Nat}
    (ls : d.leftBlock.seconds = [earlier]) (rs : d.rightBlock.seconds = [later])
    (first : EarlierIn (gapBlockMarkers left) earlier later)
    (second : EarlierIn (gapBlockMarkers left) later d.leftBlock.marker) :
    ∃ v, observe v (renderGapBlocks left) = 0 ∧ observe v (renderGapBlocks right) = 2 := by
  obtain ⟨split⟩ := d.orderedRenderedPrefixSplit ls rs first second
  let firstZone := split.before ++ earlier :: split.between
  let bridgeTail := split.after ++ [d.leftBlock.marker]
  let bridgeZone := later :: bridgeTail
  have prefixShape : d.renderedPrefix = firstZone ++ bridgeZone := by
    simp only [LeastDifferingSparseBlocks.renderedPrefix, split.render_eq,
      firstZone, bridgeZone, bridgeTail, List.append_assoc, List.cons_append]
  have rightShape : renderGapBlocks right =
      firstZone ++ [later] ++ bridgeTail ++ [later] ++ renderGapBlocks d.rightTail := by
    rw [d.right_render_eq, prefixShape, rs]
    simp [bridgeZone, List.append_assoc]
  have noCrossing' : ¬ Has27Crossing (gapBlockMarkers left) (renderGapBlocks right) := by
    rw [difference_markers d]
    exact noCrossing
  have disjoint : ∀ x, x ∈ bridgeZone → x ∉ firstZone :=
    crossing_bridge_disjoint noCrossing' split.later_not_mem_firstZone
      split.firstZone_chronology rightShape
  let v : Nat → Fin 6 := fun x => if x ∈ firstZone then 3 else if x ∈ bridgeZone then 4 else 5
  have ordinary : ∀ x, x ∈ firstZone → v x = 3 := by
    intro x member
    simp only [v, if_pos member]
  have bridge : ∀ x, x ∈ bridgeZone → v x = 4 := by
    intro x member
    simp only [v, if_neg (disjoint x member), if_pos member]
  have future : ∀ x, x ∉ Seen d → v x = 5 := by
    intro x fresh
    have absentFirst : x ∉ firstZone := by
      intro member
      apply fresh
      apply rendered_prefix_seen d
      rw [prefixShape]
      exact List.mem_append.mpr (Or.inl member)
    have absentBridge : x ∉ bridgeZone := by
      intro member
      apply fresh
      apply rendered_prefix_seen d
      rw [prefixShape]
      exact List.mem_append.mpr (Or.inr member)
    simp only [v, if_neg absentFirst, if_neg absentBridge]
  have atLater : v later = 4 := bridge later (by simp [bridgeZone])
  have atEarlier : v earlier = 3 := ordinary earlier (by simp [firstZone])
  have start : scan v 3 d.renderedPrefix = 1 := by
    rw [prefixShape, scan_append, scan_fixed v 3 3 firstZone ordinary (by decide)]
    change scan v 3 (later :: bridgeTail) = 1
    rw [scan_cons, atLater]
    have startValue : mul 3 4 = 1 := by decide
    rw [startValue]
    exact scan_fixed v 1 4 bridgeTail
      (fun x member => bridge x (List.Mem.tail later member)) (by decide)
  have shapes := observe_difference d v future start
  refine ⟨v, ?_, ?_⟩
  · rw [shapes.1, ls, scan_cons, scan_nil, atEarlier]
    decide
  · rw [shapes.2, rs, scan_cons, scan_nil, atLater]
    decide

theorem oriented_difference_separates {left right : List FirstOccurrenceGapBlock}
    (d : LeastDifferingSparseBlocks [] left right)
    (noCrossing : ¬ Has27Crossing (gapBlockMarkers right) (renderGapBlocks right))
    (oriented : OrientedChoiceDifference (gapBlockMarkers left) d.leftBlock.marker
      d.leftBlock.seconds d.rightBlock.seconds) :
    ∃ v, observe v (renderGapBlocks left) = 0 ∧ observe v (renderGapBlocks right) = 2 := by
  rcases oriented_cases oriented with ⟨selected, ls, rs⟩ | ⟨selected, ls, rs⟩ |
    ⟨earlier, later, ls, rs, first, second⟩
  · exact selected_empty_separates d ls rs
  · exact selected_current_separates d ls rs
  · exact ordered_selected_separates d noCrossing ls rs first second

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.rendered_prefix_seen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.difference_markers
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.observe_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.observe_difference
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.simple_prefix_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.simple_current_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.simple_future
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.simple_start
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.selected_empty_separates
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.selected_current_separates
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.ordered_selected_separates
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.oriented_difference_separates
