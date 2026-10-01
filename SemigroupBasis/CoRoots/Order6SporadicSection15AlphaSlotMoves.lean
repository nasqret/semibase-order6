import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

/-! ## Renderer-indexed alpha slot repairs

An already paired alpha word has marker sequence
`x1 x1 x2 x2 ...`.  A slot is the factor between two consecutive markers.
Thus two paired labels use three slots and render as
`x H x K y T y`.  The repairs below move a nonempty slot left across an
adjacent empty slot.  They package the two parity placements from Lemma 15.3,
but do not claim that an arbitrary alpha word admits this rendering or that
repeated repairs produce the global alpha normal form.
-/

namespace AlphaSlotMoves

/-- Duplicate every paired label to obtain the displayed marker sequence. -/
def pairedMarkers : List Nat -> List Nat
  | [] => []
  | label :: labels => label :: label :: pairedMarkers labels

/-- Insert the supplied gap slots between consecutive markers.  If slots run
out, the remaining markers are adjacent; excess slots after the last marker
are ignored.  The balanced alpha use has exactly one fewer slot than markers.
-/
def renderGapSlots : List Nat -> List (List Nat) -> List Nat
  | [], _ => []
  | markers, [] => markers
  | marker :: markers, slot :: slots =>
      marker :: (slot ++ renderGapSlots markers slots)

/-- Render paired labels against a flat list of gap slots.  In particular,
`renderPairedGapSlots [x, y] [h, k, t]` is `x H x K y T y`. -/
def renderPairedGapSlots
    (labels : List Nat) (slots : List (List Nat)) : List Nat :=
  renderGapSlots (pairedMarkers labels) slots

/-- Number of nonempty slots.  The explicit recursion keeps the inversion
calculation independent of a decidable list predicate. -/
def nonemptySlotCount : List (List Nat) -> Nat
  | [] => 0
  | [] :: slots => nonemptySlotCount slots
  | (_ :: _) :: slots => (nonemptySlotCount slots).succ

/-- Number of pairs `i < j` for which slot `i` is empty and slot `j` is
nonempty.  A compacted slot list has all nonempty slots before all empty ones
and therefore has measure zero. -/
def emptyBeforeNonemptyInversions : List (List Nat) -> Nat
  | [] => 0
  | [] :: slots =>
      nonemptySlotCount slots + emptyBeforeNonemptyInversions slots
  | (_ :: _) :: slots => emptyBeforeNonemptyInversions slots

@[simp]
theorem nonemptySlotCount_append
    (left right : List (List Nat)) :
    nonemptySlotCount (left ++ right) =
      nonemptySlotCount left + nonemptySlotCount right := by
  induction left with
  | nil =>
      simp only [List.nil_append, nonemptySlotCount, Nat.zero_add]
  | cons slot slots induction =>
      cases slot with
      | nil =>
          simpa [nonemptySlotCount] using induction
      | cons head tail =>
          simpa [nonemptySlotCount, Nat.succ_add] using
            congrArg Nat.succ induction

/-- Swapping an adjacent empty/nonempty inversion removes exactly one
inversion, independently of the surrounding slots. -/
theorem emptyBeforeNonemptyInversions_adjacent
    (stem suffix : List (List Nat))
    (gapHead : Nat) (gapTail : List Nat) :
    emptyBeforeNonemptyInversions
        (stem ++ [] :: (gapHead :: gapTail) :: suffix) =
      emptyBeforeNonemptyInversions
        (stem ++ (gapHead :: gapTail) :: [] :: suffix) + 1 := by
  induction stem with
  | nil =>
      simp only [List.nil_append, emptyBeforeNonemptyInversions,
        nonemptySlotCount]
      omega
  | cons slot stem induction =>
      cases slot with
      | nil =>
          have countEq :
              nonemptySlotCount
                  (stem ++ [] :: (gapHead :: gapTail) :: suffix) =
                nonemptySlotCount
                  (stem ++ (gapHead :: gapTail) :: [] :: suffix) := by
            simp [nonemptySlotCount_append, nonemptySlotCount]
          simp only [List.cons_append, emptyBeforeNonemptyInversions]
          rw [countEq, induction]
          omega
      | cons head tail =>
          simpa only [List.cons_append,
            emptyBeforeNonemptyInversions] using induction

/-- Strict form of `emptyBeforeNonemptyInversions_adjacent`, suitable as a
termination step for a future structurally justified compaction recursion. -/
theorem emptyBeforeNonemptyInversions_adjacent_lt
    (stem suffix : List (List Nat))
    (gapHead : Nat) (gapTail : List Nat) :
    emptyBeforeNonemptyInversions
        (stem ++ (gapHead :: gapTail) :: [] :: suffix) <
      emptyBeforeNonemptyInversions
        (stem ++ [] :: (gapHead :: gapTail) :: suffix) := by
  rw [emptyBeforeNonemptyInversions_adjacent]
  omega

/-- Even placement: the empty slot lies inside the `x` pair and the following
nonempty slot lies between the `x` and `y` pairs.  This is paper Case 1. -/
theorem listDerivesCompactEvenAlphaSlot
    (before after betweenY gapTail : List Nat)
    (x y gapHead : Nat) :
    ListDerives
      (before ++ renderPairedGapSlots [x, y]
        [[], gapHead :: gapTail, betweenY] ++ after)
      (before ++ renderPairedGapSlots [x, y]
        [gapHead :: gapTail, [], betweenY] ++ after) := by
  simpa [renderPairedGapSlots, pairedMarkers, renderGapSlots,
    List.append_assoc] using
      listDerivesAlphaRepairCase1
        before after betweenY gapTail x y gapHead

/-- Odd placement: the empty slot lies between the `x` and `y` pairs and the
following nonempty slot lies inside the `y` pair.  This is paper Case 2. -/
theorem listDerivesCompactOddAlphaSlot
    (before after betweenX gapTail : List Nat)
    (x y gapHead : Nat) :
    ListDerives
      (before ++ renderPairedGapSlots [x, y]
        [betweenX, [], gapHead :: gapTail] ++ after)
      (before ++ renderPairedGapSlots [x, y]
        [betweenX, gapHead :: gapTail, []] ++ after) := by
  simpa [renderPairedGapSlots, pairedMarkers, renderGapSlots,
    List.append_assoc] using
      listDerivesAlphaRepairCase2
        before after betweenX gapTail x y gapHead

/-- The even renderer repair strictly decreases the slot inversion measure. -/
theorem compactEvenAlphaSlot_decreases
    (betweenY gapTail : List Nat) (gapHead : Nat) :
    emptyBeforeNonemptyInversions
        [gapHead :: gapTail, [], betweenY] <
      emptyBeforeNonemptyInversions
        [[], gapHead :: gapTail, betweenY] := by
  simpa using
    emptyBeforeNonemptyInversions_adjacent_lt
      [] [betweenY] gapHead gapTail

/-- The odd renderer repair strictly decreases the slot inversion measure. -/
theorem compactOddAlphaSlot_decreases
    (betweenX gapTail : List Nat) (gapHead : Nat) :
    emptyBeforeNonemptyInversions
        [betweenX, gapHead :: gapTail, []] <
      emptyBeforeNonemptyInversions
        [betweenX, [], gapHead :: gapTail] := by
  simpa using
    emptyBeforeNonemptyInversions_adjacent_lt
      [betweenX] [] gapHead gapTail

end AlphaSlotMoves

end SemigroupBasis.CoRoots.Order6SporadicSection15
