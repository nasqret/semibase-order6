import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaOccurrencePairing
import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaSlotMoves
import SemigroupBasis.CoRoots.Order6SporadicSection15CanonicalData

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

/-! ## The honest post-pair alpha layer

Occurrence pairing leaves one flat gap after every marker.  This file first
groups an adjacent-pair marker list into the renderer used by
`AlphaPairMoves`, then sorts the pair labels without moving any gap.  For the
next stage, the final flat gap is kept as an endpoint and the remaining
`2 * labels.length - 1` internal slots are compacted recursively.

Compaction uses only the two repairs from `AlphaSlotMoves`; its recursion is
measured by `emptyBeforeNonemptyInversions`.  Occupied units may subsequently
be permuted only through an explicit certificate whose constructors record
the required even or odd pair anchors.

This is not an alpha normalizer.  In particular, the current source does not
prove that an arbitrary alpha word supplies the balanced marker/gap
decomposition below, that the endpoint is retained or absorbed in the branch
selected by `CanonicalData.alphaRenderData`, or that the occupied units are
the sorted maximal simple runs expected by
`CanonicalData.alphaCanonicalList`.  Those are the exact remaining parser and
endpoint boundaries.
-/

namespace AlphaPostPair

/-! ### Converting paired markers to paired-label records -/

/-- Read one label from each consecutive pair.  The total fallback ignores an
unmatched final marker; public conversion theorems require
`PairedMarkerList`. -/
def pairedLabels : List Nat -> List Nat
  | first :: _second :: markers => first :: pairedLabels markers
  | _ => []

/-- Group a flat gap list into the inside/trailing records used by
`AlphaPairMoves.renderPairedLabels`. -/
def pairedGapRecords : List (List Nat) -> List (List Nat × List Nat)
  | inside :: trailing :: gaps =>
      (inside, trailing) :: pairedGapRecords gaps
  | _ => []

/-- Expanding the labels read from a genuinely paired marker list recovers
the original markers. -/
theorem pairedMarkers_pairedLabels
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers) :
    AlphaSlotMoves.pairedMarkers (pairedLabels markers) = markers := by
  induction paired with
  | nil =>
      rfl
  | pair marker paired induction =>
      simp [pairedLabels, AlphaSlotMoves.pairedMarkers, induction]

/-- A paired marker list has exactly twice as many markers as pair labels. -/
theorem pairedLabels_length
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers) :
    markers.length = 2 * (pairedLabels markers).length := by
  induction paired with
  | nil =>
      rfl
  | pair marker paired induction =>
      simp only [List.length_cons, pairedLabels]
      omega

/-- Balanced flat gaps group into exactly one record per pair label. -/
theorem pairedGapRecords_length
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers)
    (gaps : List (List Nat))
    (balanced : gaps.length = markers.length) :
    (pairedGapRecords gaps).length = (pairedLabels markers).length := by
  induction paired generalizing gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      rfl
  | pair marker paired induction =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons inside remaining =>
          cases remaining with
          | nil =>
              simp at balanced
          | cons trailing gaps =>
              have tailResult := induction gaps (by
                simp only [List.length_cons] at balanced ⊢
                omega)
              simp [pairedGapRecords, pairedLabels, tailResult]

/-- On balanced inputs, the alternating marker/gap renderer is the same as
`AlphaSlotMoves.renderGapSlots`. -/
private theorem renderMarkerGaps_eq_renderGapSlots
    (markers : List Nat) (gaps : List (List Nat))
    (balanced : gaps.length = markers.length) :
    AlphaOccurrencePairing.renderMarkerGaps markers gaps =
      AlphaSlotMoves.renderGapSlots markers gaps := by
  induction markers generalizing gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      rfl
  | cons marker markers induction =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons gap gaps =>
          have tailBalanced : gaps.length = markers.length := by
            simpa using balanced
          simp [AlphaOccurrencePairing.renderMarkerGaps,
            AlphaSlotMoves.renderGapSlots,
            induction gaps tailBalanced, List.append_assoc]

/-- Pair records and flat slots are two presentations of the same renderer
when there are exactly two flat gaps per label. -/
theorem renderPairedLabels_pairedGapRecords
    (labels : List Nat) (gaps : List (List Nat))
    (balanced : gaps.length = 2 * labels.length) :
    AlphaPairMoves.renderPairedLabels labels (pairedGapRecords gaps) =
      AlphaSlotMoves.renderPairedGapSlots labels gaps := by
  induction labels generalizing gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      rfl
  | cons label labels induction =>
      cases gaps with
      | nil =>
          simp only [List.length_nil, List.length_cons] at balanced
          omega
      | cons inside remaining =>
          cases remaining with
          | nil =>
              simp only [List.length_nil, List.length_cons] at balanced
              omega
          | cons trailing gaps =>
              have tailBalanced : gaps.length = 2 * labels.length := by
                simp only [List.length_cons] at balanced
                omega
              simpa [pairedGapRecords,
                AlphaPairMoves.renderPairedLabels,
                AlphaSlotMoves.renderPairedGapSlots,
                AlphaSlotMoves.pairedMarkers,
                AlphaSlotMoves.renderGapSlots,
                List.append_assoc] using
                induction gaps tailBalanced

/-- A paired marker list with one gap after every marker is exactly a
balanced `renderPairedLabels` value. -/
theorem renderMarkerGaps_eq_renderPairedLabels
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers)
    (gaps : List (List Nat))
    (balanced : gaps.length = markers.length) :
    AlphaOccurrencePairing.renderMarkerGaps markers gaps =
      AlphaPairMoves.renderPairedLabels
        (pairedLabels markers) (pairedGapRecords gaps) := by
  have flatBalanced : gaps.length = 2 * (pairedLabels markers).length :=
    balanced.trans (pairedLabels_length paired)
  calc
    AlphaOccurrencePairing.renderMarkerGaps markers gaps =
        AlphaSlotMoves.renderGapSlots markers gaps :=
      renderMarkerGaps_eq_renderGapSlots markers gaps balanced
    _ = AlphaSlotMoves.renderPairedGapSlots
          (pairedLabels markers) gaps := by
      simp only [AlphaSlotMoves.renderPairedGapSlots,
        pairedMarkers_pairedLabels paired]
    _ = AlphaPairMoves.renderPairedLabels
          (pairedLabels markers) (pairedGapRecords gaps) :=
      (renderPairedLabels_pairedGapRecords
        (pairedLabels markers) gaps flatBalanced).symm

/-! ### Sorting paired labels without moving slots -/

/-- Deterministic ascending order for already paired labels. -/
def sortedPairedLabels (labels : List Nat) : List Nat :=
  labels.mergeSort (fun left right : Nat => decide (left ≤ right))

theorem sortedPairedLabels_perm (labels : List Nat) :
    (sortedPairedLabels labels).Perm labels := by
  exact List.mergeSort_perm _ _

/-- Sorting pair labels is derivable while every inside/trailing record stays
in its original physical position. -/
theorem listDerivesSortPairedLabels
    (before after : List Nat)
    (labels : List Nat) (slots : List (List Nat × List Nat))
    (balanced : slots.length = labels.length) :
    ListDerives
      (before ++ AlphaPairMoves.renderPairedLabels labels slots ++ after)
      (before ++ AlphaPairMoves.renderPairedLabels
        (sortedPairedLabels labels) slots ++ after) :=
  AlphaPairMoves.listDerivesPermuteRenderedAlphaPairs
    before after slots balanced (sortedPairedLabels_perm labels).symm

/-- Pair all exact-twice markers and then sort the resulting pair labels.  No
slot is compacted by this theorem. -/
theorem listDerivesPairAndSortMarkerOccurrences
    (before after markers : List Nat) (gaps : List (List Nat))
    (balanced : gaps.length = markers.length)
    (twice : AlphaOccurrencePairing.TwiceOccurringMarkers markers)
    (markerFree : AlphaOccurrencePairing.MarkerFreeGaps markers gaps) :
    ListDerives
      (before ++ AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after)
      (before ++ AlphaPairMoves.renderPairedLabels
        (sortedPairedLabels
          (pairedLabels
            (AlphaOccurrencePairing.pairMarkerOccurrences markers)))
        (pairedGapRecords gaps) ++ after) := by
  let pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences markers
  have markerPermutation : markers.Perm pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences_perm markers
  have paired : AlphaOccurrencePairing.PairedMarkerList pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences_paired markers twice
  have pairedBalanced : gaps.length = pairedMarkers.length :=
    balanced.trans markerPermutation.length_eq
  have recordBalanced :
      (pairedGapRecords gaps).length =
        (pairedLabels pairedMarkers).length :=
    pairedGapRecords_length paired gaps pairedBalanced
  have pairing :=
    AlphaOccurrencePairing.listDerivesPairMarkerOccurrences
      before after markers gaps balanced twice markerFree
  have rendering :=
    renderMarkerGaps_eq_renderPairedLabels paired gaps pairedBalanced
  rw [rendering] at pairing
  exact pairing.trans
    (listDerivesSortPairedLabels before after
      (pairedLabels pairedMarkers) (pairedGapRecords gaps)
      recordBalanced)

/-! ### Keeping the final endpoint outside internal slot compaction -/

@[simp]
theorem pairedMarkers_length (labels : List Nat) :
    (AlphaSlotMoves.pairedMarkers labels).length = 2 * labels.length := by
  induction labels with
  | nil =>
      rfl
  | cons label labels induction =>
      simp only [AlphaSlotMoves.pairedMarkers, List.length_cons]
      omega

private theorem renderGapSlots_append_endpoint :
    forall (marker : Nat) (markers : List Nat)
      (internal : List (List Nat)) (endpoint : List Nat),
      internal.length + 1 = (marker :: markers).length ->
      AlphaSlotMoves.renderGapSlots
          (marker :: markers) (internal ++ [endpoint]) =
        AlphaSlotMoves.renderGapSlots (marker :: markers) internal ++
          endpoint
  | marker, [], internal, endpoint, balanced => by
      have internalEmpty : internal = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons, List.length_nil] at balanced
        omega
      subst internal
      simp [AlphaSlotMoves.renderGapSlots]
  | marker, next :: markers, internal, endpoint, balanced => by
      cases internal with
      | nil =>
          simp at balanced
      | cons slot slots =>
          have tailBalanced :
              slots.length + 1 = (next :: markers).length := by
            simp only [List.length_cons] at balanced ⊢
            omega
          have induction :=
            renderGapSlots_append_endpoint
              next markers slots endpoint tailBalanced
          simp [AlphaSlotMoves.renderGapSlots, induction,
            List.append_assoc]

/-- With one fewer internal slot than paired markers, appending one endpoint
gap to the slots is the same as appending its letters after the rendering. -/
theorem renderPairedGapSlots_append_endpoint
    (labels : List Nat) (internal : List (List Nat))
    (endpoint : List Nat)
    (balanced : internal.length + 1 = 2 * labels.length) :
    AlphaSlotMoves.renderPairedGapSlots
        labels (internal ++ [endpoint]) =
      AlphaSlotMoves.renderPairedGapSlots labels internal ++ endpoint := by
  cases labels with
  | nil =>
      simp at balanced
  | cons label labels =>
      have markerBalanced :
          internal.length + 1 =
            (label :: label ::
              AlphaSlotMoves.pairedMarkers labels).length := by
        simp only [List.length_cons, pairedMarkers_length] at balanced ⊢
        omega
      simpa [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers] using
        renderGapSlots_append_endpoint label
          (label :: AlphaSlotMoves.pairedMarkers labels)
          internal endpoint markerBalanced

/-! ### Recursive compaction of internal slots -/

/-- One anchor-certified empty/nonempty repair.  `tail` skips one complete
pair (two slots), so the parity of the recursive repair is unchanged. -/
inductive AlphaSlotStep :
    List Nat -> List (List Nat) -> List (List Nat) -> Prop
  | even (left right gapHead : Nat)
      (labels gapTail between : List Nat)
      (slots : List (List Nat)) :
      AlphaSlotStep (left :: right :: labels)
        ([] :: (gapHead :: gapTail) :: between :: slots)
        ((gapHead :: gapTail) :: [] :: between :: slots)
  | odd (left right gapHead : Nat)
      (labels gapTail between : List Nat)
      (slots : List (List Nat)) :
      AlphaSlotStep (left :: right :: labels)
        (between :: [] :: (gapHead :: gapTail) :: slots)
        (between :: (gapHead :: gapTail) :: [] :: slots)
  | tail (left : Nat) (first second : List Nat)
      {labels : List Nat} {source target : List (List Nat)} :
      AlphaSlotStep labels source target ->
        AlphaSlotStep (left :: labels)
          (first :: second :: source)
          (first :: second :: target)

/-- Every certified slot step is one adjacent empty/nonempty transposition in
some prefix context. -/
theorem AlphaSlotStep.as_adjacent
    {labels : List Nat} {source target : List (List Nat)}
    (step : AlphaSlotStep labels source target) :
    ∃ stem suffix gapHead gapTail,
      source = stem ++ [] :: (gapHead :: gapTail) :: suffix /\
      target = stem ++ (gapHead :: gapTail) :: [] :: suffix := by
  induction step with
  | even left right gapHead labels gapTail between slots =>
      exact ⟨[], between :: slots, gapHead, gapTail, rfl, rfl⟩
  | odd left right gapHead labels gapTail between slots =>
      exact ⟨[between], slots, gapHead, gapTail, rfl, rfl⟩
  | tail left first second step induction =>
      rcases induction with
        ⟨stem, suffix, gapHead, gapTail, sourceEq, targetEq⟩
      refine ⟨first :: second :: stem, suffix,
        gapHead, gapTail, ?_, ?_⟩
      · simp [sourceEq]
      · simp [targetEq]

/-- A certified repair strictly decreases the existing inversion measure. -/
theorem AlphaSlotStep.decreases
    {labels : List Nat} {source target : List (List Nat)}
    (step : AlphaSlotStep labels source target) :
    AlphaSlotMoves.emptyBeforeNonemptyInversions target <
      AlphaSlotMoves.emptyBeforeNonemptyInversions source := by
  rcases step.as_adjacent with
    ⟨stem, suffix, gapHead, gapTail, rfl, rfl⟩
  exact AlphaSlotMoves.emptyBeforeNonemptyInversions_adjacent_lt
    stem suffix gapHead gapTail

/-- A slot repair only permutes slots. -/
theorem AlphaSlotStep.perm
    {labels : List Nat} {source target : List (List Nat)}
    (step : AlphaSlotStep labels source target) :
    source.Perm target := by
  rcases step.as_adjacent with
    ⟨stem, suffix, gapHead, gapTail, rfl, rfl⟩
  exact List.Perm.append_left stem
    (List.Perm.swap (gapHead :: gapTail) [] suffix)

theorem AlphaSlotStep.length_eq
    {labels : List Nat} {source target : List (List Nat)}
    (step : AlphaSlotStep labels source target) :
    target.length = source.length :=
  step.perm.length_eq.symm

/-- Realize a certified slot repair by the appropriate parity case from
`AlphaSlotMoves`. -/
theorem AlphaSlotStep.listDerives
    {labels : List Nat} {source target : List (List Nat)}
    (step : AlphaSlotStep labels source target)
    (before after : List Nat) :
    ListDerives
      (before ++ AlphaSlotMoves.renderPairedGapSlots labels source ++ after)
      (before ++ AlphaSlotMoves.renderPairedGapSlots labels target ++ after) := by
  induction step generalizing before with
  | even left right gapHead labels gapTail between slots =>
      cases slots with
      | nil =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            AlphaSlotMoves.listDerivesCompactEvenAlphaSlot
              before
              (AlphaSlotMoves.pairedMarkers labels ++ after)
              between gapTail left right gapHead
      | cons trailing slots =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            AlphaSlotMoves.listDerivesCompactEvenAlphaSlot
              before
              (trailing ++
                AlphaSlotMoves.renderGapSlots
                  (AlphaSlotMoves.pairedMarkers labels) slots ++ after)
              between gapTail left right gapHead
  | odd left right gapHead labels gapTail between slots =>
      cases slots with
      | nil =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            AlphaSlotMoves.listDerivesCompactOddAlphaSlot
              before
              (AlphaSlotMoves.pairedMarkers labels ++ after)
              between gapTail left right gapHead
      | cons trailing slots =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            AlphaSlotMoves.listDerivesCompactOddAlphaSlot
              before
              (trailing ++
                AlphaSlotMoves.renderGapSlots
                  (AlphaSlotMoves.pairedMarkers labels) slots ++ after)
              between gapTail left right gapHead
  | tail left first second step induction =>
      have repaired := induction
        (before ++ [left] ++ first ++ [left] ++ second)
      simpa [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers,
        AlphaSlotMoves.renderGapSlots,
        List.append_assoc] using repaired

private theorem exists_adjacent_slot_inversion :
    forall slots : List (List Nat),
      0 < AlphaSlotMoves.emptyBeforeNonemptyInversions slots ->
      ∃ stem suffix gapHead gapTail,
        slots = stem ++ [] :: (gapHead :: gapTail) :: suffix
  | [], positive => by
      simp [AlphaSlotMoves.emptyBeforeNonemptyInversions] at positive
  | [] :: slots, positive => by
      cases slots with
      | nil =>
          simp [AlphaSlotMoves.emptyBeforeNonemptyInversions,
            AlphaSlotMoves.nonemptySlotCount] at positive
      | cons next slots =>
          cases next with
          | nil =>
              have tailPositive :
                  0 < AlphaSlotMoves.emptyBeforeNonemptyInversions
                    ([] :: slots) := by
                simp only [AlphaSlotMoves.emptyBeforeNonemptyInversions,
                  AlphaSlotMoves.nonemptySlotCount] at positive ⊢
                omega
              rcases exists_adjacent_slot_inversion
                  ([] :: slots) tailPositive with
                ⟨stem, suffix, gapHead, gapTail, sourceEq⟩
              refine ⟨[] :: stem, suffix, gapHead, gapTail, ?_⟩
              simp [sourceEq]
          | cons gapHead gapTail =>
              exact ⟨[], slots, gapHead, gapTail, rfl⟩
  | (slotHead :: slotTail) :: slots, positive => by
      have tailPositive :
          0 < AlphaSlotMoves.emptyBeforeNonemptyInversions slots := by
        simpa [AlphaSlotMoves.emptyBeforeNonemptyInversions] using positive
      rcases exists_adjacent_slot_inversion slots tailPositive with
        ⟨stem, suffix, gapHead, gapTail, sourceEq⟩
      refine ⟨(slotHead :: slotTail) :: stem,
        suffix, gapHead, gapTail, ?_⟩
      simp [sourceEq]
termination_by slots => slots.length
decreasing_by
  all_goals (simp_all only [List.length_cons] <;> omega)

/-- Balanced internal slots provide the two pair anchors required by every
adjacent empty/nonempty inversion. -/
private theorem alphaSlotStep_of_adjacent :
    forall (labels : List Nat) (stem suffix : List (List Nat))
      (gapHead : Nat) (gapTail : List Nat),
      (stem ++ [] :: (gapHead :: gapTail) :: suffix).length + 1 =
          2 * labels.length ->
      AlphaSlotStep labels
        (stem ++ [] :: (gapHead :: gapTail) :: suffix)
        (stem ++ (gapHead :: gapTail) :: [] :: suffix)
  | labels, [], suffix, gapHead, gapTail, balanced => by
      cases labels with
      | nil =>
          simp at balanced
      | cons left labels =>
          cases labels with
          | nil =>
              simp at balanced
          | cons right labels =>
              cases suffix with
              | nil =>
                  simp at balanced
                  omega
              | cons between slots =>
                  exact AlphaSlotStep.even
                    left right gapHead labels gapTail between slots
  | labels, [between], suffix, gapHead, gapTail, balanced => by
      cases labels with
      | nil =>
          simp at balanced
      | cons left labels =>
          cases labels with
          | nil =>
              simp at balanced
          | cons right labels =>
              exact AlphaSlotStep.odd
                left right gapHead labels gapTail between suffix
  | labels, first :: second :: stem,
      suffix, gapHead, gapTail, balanced => by
      cases labels with
      | nil =>
          simp at balanced
      | cons left labels =>
          have tailBalanced :
              (stem ++ [] :: (gapHead :: gapTail) :: suffix).length + 1 =
                2 * labels.length := by
            simp only [List.length_append, List.length_cons,
              List.length_nil] at balanced ⊢
            omega
          exact AlphaSlotStep.tail left first second
            (alphaSlotStep_of_adjacent
              labels stem suffix gapHead gapTail tailBalanced)
termination_by _ stem _ _ _ _ => stem.length
decreasing_by
  simp only [List.length_cons]
  omega

/-- Positive inversion measure plus the internal-slot population equation
produces an anchor-certified repair. -/
theorem existsAlphaSlotStep
    (labels : List Nat) (slots : List (List Nat))
    (balanced : slots.length + 1 = 2 * labels.length)
    (positive :
      0 < AlphaSlotMoves.emptyBeforeNonemptyInversions slots) :
    ∃ target, AlphaSlotStep labels slots target := by
  rcases exists_adjacent_slot_inversion slots positive with
    ⟨stem, suffix, gapHead, gapTail, rfl⟩
  exact
    ⟨stem ++ (gapHead :: gapTail) :: [] :: suffix,
      alphaSlotStep_of_adjacent
        labels stem suffix gapHead gapTail balanced⟩

/-- Recursively move every nonempty internal slot left of every empty slot.
The result is source-only at this stage: it is derivably reached, has zero
inversion measure, and is a permutation of the source slots. -/
theorem listDerivesCompactAlphaSlots :
    forall (labels : List Nat) (slots : List (List Nat))
      (before after : List Nat),
      slots.length + 1 = 2 * labels.length ->
      ∃ compacted,
        ListDerives
          (before ++
            AlphaSlotMoves.renderPairedGapSlots labels slots ++ after)
          (before ++
            AlphaSlotMoves.renderPairedGapSlots labels compacted ++ after) /\
        AlphaSlotMoves.emptyBeforeNonemptyInversions compacted = 0 /\
        slots.Perm compacted
  | labels, slots, before, after, balanced => by
      by_cases compact :
          AlphaSlotMoves.emptyBeforeNonemptyInversions slots = 0
      · exact ⟨slots, S5_107.ListDerives.refl _, compact,
          List.Perm.refl slots⟩
      · have positive :
            0 < AlphaSlotMoves.emptyBeforeNonemptyInversions slots :=
          Nat.pos_of_ne_zero compact
        obtain ⟨repaired, step⟩ :=
          existsAlphaSlotStep labels slots balanced positive
        have repairedBalanced :
            repaired.length + 1 = 2 * labels.length := by
          rw [step.length_eq]
          exact balanced
        obtain ⟨compacted, recurse, finalCompact, finalPermutation⟩ :=
          listDerivesCompactAlphaSlots
            labels repaired before after repairedBalanced
        exact
          ⟨compacted,
            (step.listDerives before after).trans recurse,
            finalCompact,
            step.perm.trans finalPermutation⟩
termination_by labels slots before after _ =>
  AlphaSlotMoves.emptyBeforeNonemptyInversions slots
decreasing_by exact step.decreases

/-! ### Permuting occupied units when pair anchors permit -/

/-- A permutation certificate generated only by the two anchored placements
of (15.1e).  The direct constructors require both transposed units to be
nonempty; `tail` moves the certificate two slots to the right. -/
inductive AnchoredOccupiedUnitPermutation :
    List Nat -> List (List Nat) -> List (List Nat) -> Prop
  | refl (labels : List Nat) (slots : List (List Nat)) :
      AnchoredOccupiedUnitPermutation labels slots slots
  | even (leftAnchor rightAnchor leftHead rightHead : Nat)
      (labels leftTail rightTail between : List Nat)
      (slots : List (List Nat)) :
      AnchoredOccupiedUnitPermutation
        (leftAnchor :: rightAnchor :: labels)
        ((leftHead :: leftTail) :: (rightHead :: rightTail) ::
          between :: slots)
        ((rightHead :: rightTail) :: (leftHead :: leftTail) ::
          between :: slots)
  | odd (leftAnchor rightAnchor leftHead rightHead : Nat)
      (labels leftTail rightTail between : List Nat)
      (slots : List (List Nat)) :
      AnchoredOccupiedUnitPermutation
        (leftAnchor :: rightAnchor :: labels)
        (between :: (leftHead :: leftTail) ::
          (rightHead :: rightTail) :: slots)
        (between :: (rightHead :: rightTail) ::
          (leftHead :: leftTail) :: slots)
  | tail (leftAnchor : Nat) (first second : List Nat)
      {labels : List Nat} {source target : List (List Nat)} :
      AnchoredOccupiedUnitPermutation labels source target ->
        AnchoredOccupiedUnitPermutation (leftAnchor :: labels)
          (first :: second :: source) (first :: second :: target)
  | trans {labels : List Nat}
      {source middle target : List (List Nat)} :
      AnchoredOccupiedUnitPermutation labels source middle ->
      AnchoredOccupiedUnitPermutation labels middle target ->
      AnchoredOccupiedUnitPermutation labels source target

theorem AnchoredOccupiedUnitPermutation.perm
    {labels : List Nat} {source target : List (List Nat)}
    (moves : AnchoredOccupiedUnitPermutation labels source target) :
    source.Perm target := by
  induction moves with
  | refl labels slots =>
      exact List.Perm.refl slots
  | even leftAnchor rightAnchor leftHead rightHead labels
      leftTail rightTail between slots =>
      exact List.Perm.swap
        (rightHead :: rightTail) (leftHead :: leftTail)
        (between :: slots)
  | odd leftAnchor rightAnchor leftHead rightHead labels
      leftTail rightTail between slots =>
      exact List.Perm.cons between <|
        List.Perm.swap
          (rightHead :: rightTail) (leftHead :: leftTail) slots
  | tail leftAnchor first second moves induction =>
      exact List.Perm.cons first (List.Perm.cons second induction)
  | trans first second firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Every anchor-certified occupied-unit permutation is derivable.  This is
the strongest permutation closure available without an endpoint anchor. -/
theorem listDerivesPermuteOccupiedAlphaUnits
    {labels : List Nat} {source target : List (List Nat)}
    (moves : AnchoredOccupiedUnitPermutation labels source target)
    (before after : List Nat) :
    ListDerives
      (before ++ AlphaSlotMoves.renderPairedGapSlots labels source ++ after)
      (before ++ AlphaSlotMoves.renderPairedGapSlots labels target ++ after) := by
  induction moves generalizing before with
  | refl labels slots =>
      exact S5_107.ListDerives.refl _
  | even leftAnchor rightAnchor leftHead rightHead labels
      leftTail rightTail between slots =>
      cases slots with
      | nil =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            listDerivesAlphaUnitSwapForward
              before (AlphaSlotMoves.pairedMarkers labels ++ after)
              between leftTail rightTail
              leftAnchor rightAnchor leftHead rightHead
      | cons trailing slots =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            listDerivesAlphaUnitSwapForward
              before
              (trailing ++
                AlphaSlotMoves.renderGapSlots
                  (AlphaSlotMoves.pairedMarkers labels) slots ++ after)
              between leftTail rightTail
              leftAnchor rightAnchor leftHead rightHead
  | odd leftAnchor rightAnchor leftHead rightHead labels
      leftTail rightTail between slots =>
      cases slots with
      | nil =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            listDerivesAlphaUnitSwapReverse
              before (AlphaSlotMoves.pairedMarkers labels ++ after)
              between leftTail rightTail
              leftAnchor rightAnchor leftHead rightHead
      | cons trailing slots =>
          simpa [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            List.append_assoc] using
            listDerivesAlphaUnitSwapReverse
              before
              (trailing ++
                AlphaSlotMoves.renderGapSlots
                  (AlphaSlotMoves.pairedMarkers labels) slots ++ after)
              between leftTail rightTail
              leftAnchor rightAnchor leftHead rightHead
  | tail leftAnchor first second moves induction =>
      have reordered := induction
        (before ++ [leftAnchor] ++ first ++ [leftAnchor] ++ second)
      simpa [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers,
        AlphaSlotMoves.renderGapSlots,
        List.append_assoc] using reordered
  | trans first second firstInduction secondInduction =>
      exact (firstInduction before).trans (secondInduction before)

/-! ### Combined post-pair theorem -/

/-- Pair and sort marker labels, split off a supplied final endpoint gap, and
compact all remaining slots.  The theorem deliberately returns the exact
zero-inversion intermediate rather than identifying it with
`CanonicalData.alphaCanonicalList`. -/
theorem listDerivesPairSortAndCompactAlphaSlots
    (before after markers : List Nat) (gaps : List (List Nat))
    (internal : List (List Nat)) (endpoint : List Nat)
    (balanced : gaps.length = markers.length)
    (gapShape : gaps = internal ++ [endpoint])
    (twice : AlphaOccurrencePairing.TwiceOccurringMarkers markers)
    (markerFree : AlphaOccurrencePairing.MarkerFreeGaps markers gaps) :
    ∃ compacted,
      ListDerives
        (before ++ AlphaOccurrencePairing.renderMarkerGaps markers gaps ++ after)
        (before ++ AlphaSlotMoves.renderPairedGapSlots
          (sortedPairedLabels
            (pairedLabels
              (AlphaOccurrencePairing.pairMarkerOccurrences markers)))
          compacted ++ endpoint ++ after) /\
      AlphaSlotMoves.emptyBeforeNonemptyInversions compacted = 0 /\
      internal.Perm compacted := by
  let pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences markers
  let labels := pairedLabels pairedMarkers
  let sortedLabels := sortedPairedLabels labels
  have markerPermutation : markers.Perm pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences_perm markers
  have paired : AlphaOccurrencePairing.PairedMarkerList pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences_paired markers twice
  have pairedBalanced : gaps.length = pairedMarkers.length :=
    balanced.trans markerPermutation.length_eq
  have flatBalanced : gaps.length = 2 * labels.length := by
    exact pairedBalanced.trans (pairedLabels_length paired)
  have sortedLength : sortedLabels.length = labels.length :=
    (sortedPairedLabels_perm labels).length_eq
  have internalBalanced : internal.length + 1 = 2 * sortedLabels.length := by
    rw [sortedLength]
    rw [gapShape] at flatBalanced
    simpa using flatBalanced
  have pairAndSort :=
    listDerivesPairAndSortMarkerOccurrences
      before after markers gaps balanced twice markerFree
  have flatRendering :=
    renderPairedLabels_pairedGapRecords sortedLabels gaps <| by
      simpa [sortedLength] using flatBalanced
  rw [flatRendering] at pairAndSort
  have endpointRendering :
      AlphaSlotMoves.renderPairedGapSlots sortedLabels gaps =
        AlphaSlotMoves.renderPairedGapSlots sortedLabels internal ++
          endpoint := by
    rw [gapShape]
    exact renderPairedGapSlots_append_endpoint
      sortedLabels internal endpoint internalBalanced
  rw [endpointRendering] at pairAndSort
  obtain ⟨compacted, compaction, compactedZero, slotPermutation⟩ :=
    listDerivesCompactAlphaSlots
      sortedLabels internal (before) (endpoint ++ after) internalBalanced
  exact
    ⟨compacted,
      pairAndSort.trans (by
        simpa [List.append_assoc] using compaction),
      compactedZero,
      slotPermutation⟩

end AlphaPostPair

end SemigroupBasis.CoRoots.Order6SporadicSection15
