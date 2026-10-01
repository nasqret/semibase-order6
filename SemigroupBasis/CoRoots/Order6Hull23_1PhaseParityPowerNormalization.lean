import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPowerMoves

/-!
# Hull 23.1 post-sweep power normalization

This module records the literal power data left by the Balance sweep in
Lee--Zhang Lemma 23.5 and closes the basis-independent and local derivational
parts of the subsequent power normalization.  It remains over the fifteen
identities of Proposition 23.1: every derivational helper below is assembled
from the gap, debt, and power moves proved for that basis.

The central intermediate is `PriorPowerDatum`.  Its exponent is the complete
leading marker power after the gap sweep, while `debtBit` records the possible
single terminal copy that must be absorbed.  The stored equation is exact
modulo two, and the phase bit supplies the lower bound needed by the ordinary
and exceptional power contractions.

The active carrier used below is
`gapDebt lastBlock ++ sweptPriorDebt beforeBlocks`.  A rejected intermediate
version used only `sweptPriorDebt beforeBlocks`; the source `[0, 1, 0]`
falsifies that choice because its required prior debt copy occurs in the final
gap.  Its marker-swapped dual `[1, 0, 1]` is the companion regression case.
Keeping both counterexamples explicit prevents the incomplete carrier from
being reintroduced.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityPowerNormalization

open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPowerMoves

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

abbrev GapBlock := FirstOccurrenceGapBlock

/-! ## Exact power data left by one swept prior block -/

/-- The post-sweep state of one phase strictly before the selected final
doubled phase.

`exponent` is the complete adjacent leading power.  `debtBit` says whether
one additional occurrence of the same marker remains in the terminal debt.
The final field is therefore the exact parity equation for that marker. -/
structure PriorPowerDatum where
  entry : PhaseParityEntry
  exponent : Nat
  debtBit : Bool
  exponent_pos : 0 < exponent
  undoubled_eq_one :
    entry.phase.doubled = false -> exponent = 1
  doubled_ge_two :
    entry.phase.doubled = true -> 2 <= exponent
  parity_eq :
    (exponent + if debtBit then 1 else 0) % 2 =
      entry.parity % 2

/-- The unique bit that corrects the parity of an already gathered marker
power. -/
def parityCorrectionBit (exponent parity : Nat) : Bool :=
  decide (exponent % 2 ≠ parity % 2)

theorem add_parityCorrectionBit_mod_two
    (exponent parity : Nat) :
    (exponent +
        if parityCorrectionBit exponent parity then 1 else 0) % 2 =
      parity % 2 := by
  have exponentBound : exponent % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have parityBound : parity % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  by_cases same : exponent % 2 = parity % 2
  · simp [parityCorrectionBit, same]
  · simp [parityCorrectionBit, same]
    omega

/-- Construct the genuine prior-power datum of one source block aligned with
its phase/parity entry.  The swept exponent is `seconds.length + 1`, exactly
as proved by `sweptGapMarkerPower_length`. -/
def priorPowerDatumOfAlignedBlock
    (block : GapBlock) (entry : PhaseParityEntry)
    (aligned : entry.phase = phaseOfGapBlock block) : PriorPowerDatum where
  entry := entry
  exponent := block.seconds.length + 1
  debtBit := parityCorrectionBit
    (block.seconds.length + 1) entry.parity
  exponent_pos := by omega
  undoubled_eq_one := by
    intro undoubled
    by_cases empty : block.seconds = []
    · simp [empty]
    · have sourceDoubled :
          (phaseOfGapBlock block).doubled = true := by
        simp [phaseOfGapBlock, empty]
      rw [← aligned, undoubled] at sourceDoubled
      contradiction
  doubled_ge_two := by
    intro doubled
    have nonempty : block.seconds ≠ [] := by
      intro empty
      have sourceUndoubled :
          (phaseOfGapBlock block).doubled = false := by
        simp [phaseOfGapBlock, empty]
      rw [← aligned, doubled] at sourceUndoubled
      contradiction
    have positive : 0 < block.seconds.length :=
      List.length_pos_iff.mpr nonempty
    omega
  parity_eq :=
    add_parityCorrectionBit_mod_two
      (block.seconds.length + 1) entry.parity

/-- Literal adjacent power represented by one datum. -/
def renderPriorPowerDatum (datum : PriorPowerDatum) : List Nat :=
  List.replicate datum.exponent datum.entry.phase.label

/-- Concatenation of all gathered prior marker powers. -/
def renderPriorPowerData : List PriorPowerDatum -> List Nat
  | [] => []
  | datum :: rest =>
      renderPriorPowerDatum datum ++ renderPriorPowerData rest

/-- The possible one-copy terminal debts, in entry order. -/
def priorDebtLabels : List PriorPowerDatum -> List Nat
  | [] => []
  | datum :: rest =>
      (if datum.debtBit then [datum.entry.phase.label] else []) ++
        priorDebtLabels rest

theorem renderPriorPowerDatum_of_alignedBlock
    (block : GapBlock) (entry : PhaseParityEntry)
    (aligned : entry.phase = phaseOfGapBlock block) :
    renderPriorPowerDatum
        (priorPowerDatumOfAlignedBlock block entry aligned) =
      sweptGapMarkerPower block := by
  have labelAligned : entry.phase.label = block.marker := by
    simpa [phaseOfGapBlock] using congrArg Phase.label aligned
  rw [sweptGapMarkerPower_eq_replicate]
  simp [renderPriorPowerDatum, priorPowerDatumOfAlignedBlock,
    labelAligned]

/-- An aligned source-block/entry prefix has a list of genuine power data,
and rendering those data is literally the leading power list produced by the
gap sweep. -/
theorem exists_priorPowerData_of_phase_alignment :
    forall (blocks : List GapBlock) (entries : List PhaseParityEntry),
      entries.map (fun entry => entry.phase) =
          blocks.map phaseOfGapBlock ->
        exists data : List PriorPowerDatum,
          data.map (fun datum => datum.entry) = entries /\
          data.map (fun datum => datum.exponent) =
            blocks.map (fun block => block.seconds.length + 1) /\
          renderPriorPowerData data = renderSweptPriorBlocks blocks
  | [], [], _ => by
      exact ⟨[], by simp [renderPriorPowerData, renderSweptPriorBlocks]⟩
  | [], _ :: _, aligned => by
      simp at aligned
  | _ :: _, [], aligned => by
      simp at aligned
  | block :: blocks, entry :: entries, aligned => by
      have headAligned : entry.phase = phaseOfGapBlock block := by
        simpa using congrArg List.head? aligned
      have tailAligned :
          entries.map (fun selected => selected.phase) =
            blocks.map phaseOfGapBlock := by
        simpa using congrArg List.tail aligned
      obtain ⟨data, entriesShape, exponentsShape, renderShape⟩ :=
        exists_priorPowerData_of_phase_alignment
          blocks entries tailAligned
      let datum :=
        priorPowerDatumOfAlignedBlock block entry headAligned
      have headRender :
          renderPriorPowerDatum datum = sweptGapMarkerPower block := by
        simpa [datum] using
          renderPriorPowerDatum_of_alignedBlock
            block entry headAligned
      refine ⟨datum :: data, ?_⟩
      constructor
      · simp [datum, priorPowerDatumOfAlignedBlock, entriesShape]
      constructor
      · simp [datum, exponentsShape,
          priorPowerDatumOfAlignedBlock]
      · simp only [renderPriorPowerData, renderSweptPriorBlocks]
        rw [headRender, renderShape]

theorem renderPriorPowerDatum_of_undoubled
    (datum : PriorPowerDatum)
    (undoubled : datum.entry.phase.doubled = false) :
    renderPriorPowerDatum datum = [datum.entry.phase.label] := by
  rw [renderPriorPowerDatum,
    datum.undoubled_eq_one undoubled]
  rfl

theorem priorPowerParity_of_noDebt
    (datum : PriorPowerDatum)
    (noDebt : datum.debtBit = false) :
    datum.exponent % 2 = datum.entry.parity % 2 := by
  simpa [noDebt] using datum.parity_eq

theorem priorPowerParity_after_debt
    (datum : PriorPowerDatum)
    (hasDebt : datum.debtBit = true) :
    (datum.exponent + 1) % 2 = datum.entry.parity % 2 := by
  simpa [hasDebt] using datum.parity_eq

/-! ## Corrected active-debt carrier support and accounting -/

private theorem mem_replicate_self_of_pos_local
    (letter copies : Nat) (positive : 0 < copies) :
    letter ∈ List.replicate copies letter := by
  cases copies with
  | zero =>
      simp at positive
  | succ rest =>
      simp [List.replicate_succ]

private theorem count_replicate_self_local
    (letter : Nat) :
    forall copies : Nat,
      (List.replicate copies letter).count letter = copies
  | 0 => rfl
  | copies + 1 => by
      rw [List.replicate_succ, List.count_cons_self,
        count_replicate_self_local letter copies]

/-- In a sweep that starts with an arbitrary historical marker list, every
emitted debt letter is either historical or remains represented by a marker
power in the swept prefix. -/
private theorem sweptPriorDebt_seen_in_seen_or_sweptPrefix :
    forall {seen : List Nat} {blocks : List GapBlock},
      GapBlocksWellFormed seen blocks ->
        forall letter, letter ∈ sweptPriorDebt blocks ->
          letter ∈ seen ∨ letter ∈ renderSweptPriorBlocks blocks
  | seen, [], _, letter, member => by
      simp [sweptPriorDebt] at member
  | seen, block :: rest, formed, letter, member => by
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          have markerInPower :
              block.marker ∈ sweptGapMarkerPower block := by
            change block.marker ∈
              List.replicate
                  (block.seconds.count block.marker) block.marker ++
                List.replicate
                  ((gapDebt block).length + 1) block.marker
            exact List.mem_append.mpr <| Or.inr <|
              mem_replicate_self_of_pos_local
                block.marker ((gapDebt block).length + 1) (by omega)
          have markerInPrefix :
              block.marker ∈
                renderSweptPriorBlocks (block :: rest) := by
            simpa only [renderSweptPriorBlocks] using
              (List.mem_append.mpr <| Or.inl markerInPower)
          simp only [sweptPriorDebt, List.mem_append] at member
          rcases member with inHeadDebt | inTailDebt
          · simp only [sweptGapDebt, List.mem_append] at inHeadDebt
            rcases inHeadDebt with inMarkerCopies | inGapDebt
            · have equal : letter = block.marker :=
                List.eq_of_mem_replicate inMarkerCopies
              subst letter
              exact Or.inr markerInPrefix
            · have inSeconds : letter ∈ block.seconds :=
                (List.mem_filter.mp inGapDebt).1
              rcases List.mem_cons.mp
                  (secondsSeen letter inSeconds) with
                atMarker | inSeen
              · subst letter
                exact Or.inr markerInPrefix
              · exact Or.inl inSeen
          · have tailSeen :=
              sweptPriorDebt_seen_in_seen_or_sweptPrefix
                tailFormed letter inTailDebt
            rcases tailSeen with inNextSeen | inTailPrefix
            · rcases List.mem_cons.mp inNextSeen with
                atMarker | inSeen
              · subst letter
                exact Or.inr markerInPrefix
              · exact Or.inl inSeen
            · exact Or.inr <| by
                simpa only [renderSweptPriorBlocks] using
                  (List.mem_append.mpr <| Or.inr inTailPrefix)

/-- Every letter in debt emitted by a sweep from the empty history has an
explicit witness in the swept marker-power prefix. -/
theorem sweptPriorDebt_seen_in_sweptPrefix
    {blocks : List GapBlock}
    (formed : GapBlocksWellFormed [] blocks) :
    forall letter, letter ∈ sweptPriorDebt blocks ->
      letter ∈ renderSweptPriorBlocks blocks := by
  intro letter member
  rcases sweptPriorDebt_seen_in_seen_or_sweptPrefix
      formed letter member with impossible | inPrefix
  · simp at impossible
  · exact inPrefix

/-- The complete active prior-debt carrier is witnessed in the already swept
prefix.  The `gapDebt lastBlock` summand is essential: it contains the prior
copy missed by the rejected swept-prefix-only carrier. -/
theorem activePriorDebt_seen_in_sweptPrefix
    {before after : List GapBlock} {lastBlock : GapBlock}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after)) :
    forall letter,
      letter ∈ gapDebt lastBlock ++ sweptPriorDebt before ->
        letter ∈ renderSweptPriorBlocks before := by
  intro letter member
  rcases List.mem_append.mp member with inLastDebt | inPriorDebt
  · have inSeconds : letter ∈ lastBlock.seconds :=
      (List.mem_filter.mp inLastDebt).1
    have different : letter ≠ lastBlock.marker := by
      simpa using (List.mem_filter.mp inLastDebt).2
    have witnessed :=
      lastGapSecondsSeenInSweptPrefix formed inSeconds
    rcases List.mem_append.mp witnessed with inPrefix | atLastMarker
    · exact inPrefix
    · have equal : letter = lastBlock.marker := by
        simpa using atLastMarker
      exact False.elim <| different equal
  · have beforeFormed : GapBlocksWellFormed [] before :=
      (gapBlocksWellFormed_append formed).1
    exact sweptPriorDebt_seen_in_sweptPrefix
      beforeFormed letter inPriorDebt

/-- Re-express active-carrier support through an exact rendering of the
gathered prior-power data. -/
theorem activePriorDebt_seen_in_renderPriorPowerData
    {before after : List GapBlock} {lastBlock : GapBlock}
    {data : List PriorPowerDatum}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after))
    (dataRender :
      renderPriorPowerData data = renderSweptPriorBlocks before) :
    forall letter,
      letter ∈ gapDebt lastBlock ++ sweptPriorDebt before ->
        letter ∈ renderPriorPowerData data := by
  intro letter member
  rw [dataRender]
  exact activePriorDebt_seen_in_sweptPrefix formed letter member

/-- A selected terminal-debt label is already present in the literal gathered
power rendering. -/
theorem priorDebtLabels_seen_in_renderPriorPowerData
    (data : List PriorPowerDatum) :
    forall letter, letter ∈ priorDebtLabels data ->
      letter ∈ renderPriorPowerData data := by
  induction data with
  | nil =>
      simp [priorDebtLabels]
  | cons datum rest induction =>
      intro letter member
      cases debtBit : datum.debtBit with
      | false =>
          have inRest : letter ∈ priorDebtLabels rest := by
            simpa [priorDebtLabels, debtBit] using member
          simpa only [renderPriorPowerData] using
            (List.mem_append.mpr <| Or.inr <|
              induction letter inRest)
      | true =>
          have selected :
              letter = datum.entry.phase.label ∨
                letter ∈ priorDebtLabels rest := by
            simpa [priorDebtLabels, debtBit] using member
          rcases selected with atHead | inRest
          · subst letter
            have inPower :
                datum.entry.phase.label ∈
                  renderPriorPowerDatum datum := by
              rw [renderPriorPowerDatum]
              exact mem_replicate_self_of_pos_local
                datum.entry.phase.label datum.exponent
                datum.exponent_pos
            simpa only [renderPriorPowerData] using
              (List.mem_append.mpr <| Or.inl inPower)
          · simpa only [renderPriorPowerData] using
              (List.mem_append.mpr <| Or.inr <|
                induction letter inRest)

private theorem mem_renderPriorPowerData_labels :
    forall {data : List PriorPowerDatum} {letter : Nat},
      letter ∈ renderPriorPowerData data ->
        letter ∈ data.map
          (fun datum => datum.entry.phase.label)
  | [], letter, member => by
      simp [renderPriorPowerData] at member
  | datum :: rest, letter, member => by
      simp only [renderPriorPowerData] at member
      rcases List.mem_append.mp member with inHead | inRest
      · rw [renderPriorPowerDatum] at inHead
        have equal : letter = datum.entry.phase.label :=
          List.eq_of_mem_replicate inHead
        subst letter
        simp
      · exact List.Mem.tail _ <|
          mem_renderPriorPowerData_labels inRest

private theorem mem_priorDebtLabels_dataLabels
    {data : List PriorPowerDatum} {letter : Nat}
    (member : letter ∈ priorDebtLabels data) :
    letter ∈ data.map (fun datum => datum.entry.phase.label) :=
  mem_renderPriorPowerData_labels
    (priorDebtLabels_seen_in_renderPriorPowerData data letter member)

/-- The datum labels are exactly the marker list of the aligned source-block
prefix. -/
theorem priorPowerData_labels_eq_gapBlockMarkers
    (blocks : List GapBlock) (entries : List PhaseParityEntry)
    (data : List PriorPowerDatum)
    (dataEntries : data.map (fun datum => datum.entry) = entries)
    (aligned :
      entries.map (fun entry => entry.phase) =
        blocks.map phaseOfGapBlock) :
    data.map (fun datum => datum.entry.phase.label) =
      gapBlockMarkers blocks := by
  calc
    data.map (fun datum => datum.entry.phase.label) =
        SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entryLabels
          entries := by
      rw [← dataEntries]
      simp [SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entryLabels,
        List.map_map, Function.comp_def]
    _ = gapBlockMarkers blocks := by
      have labelsEqual := congrArg (List.map Phase.label) aligned
      simpa [SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entryLabels,
        gapBlockMarkers, phaseOfGapBlock,
        List.map_map, Function.comp_def] using labelsEqual

private theorem count_replicate_of_ne_local
    {repeated tested : Nat} (different : tested ≠ repeated) :
    forall copies : Nat,
      (List.replicate copies repeated).count tested = 0
  | 0 => rfl
  | copies + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne_local different copies]

private theorem count_filter_bne_self
    (marker : Nat) (letters : List Nat) :
    (letters.filter (fun letter => letter != marker)).count marker = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem count_filter_bne_of_ne
    {marker tested : Nat} (different : tested ≠ marker) :
    forall letters : List Nat,
      (letters.filter (fun letter => letter != marker)).count tested =
        letters.count tested
  | [] => rfl
  | head :: tail => by
      by_cases atMarker : head = marker
      · subst head
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact count_filter_bne_of_ne different tail
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [count_filter_bne_of_ne different tail]

private theorem count_gapDebt_of_ne
    (block : GapBlock) {tested : Nat}
    (different : tested ≠ block.marker) :
    (gapDebt block).count tested = block.seconds.count tested := by
  exact count_filter_bne_of_ne different block.seconds

private theorem count_gapBlock_mod_two_eq_sweptGap
    (block : GapBlock) (tested : Nat) :
    (block.marker :: block.seconds).count tested % 2 =
      (sweptGapMarkerPower block ++ sweptGapDebt block).count tested % 2 := by
  by_cases equal : tested = block.marker
  · subst tested
    simp [sweptGapMarkerPower, sweptGapDebt, gapDebt,
      count_filter_bne_self, count_replicate_self_local]
    omega
  · simp [sweptGapMarkerPower, sweptGapDebt, gapDebt,
      count_replicate_of_ne_local equal,
      count_filter_bne_of_ne equal, equal, Ne.symm equal]

/-- Sweeping a block list preserves every letter count modulo two, including
both the leading marker powers and the emitted debt. -/
theorem count_renderGapBlocks_mod_two_eq_swept :
    forall (blocks : List GapBlock) (letter : Nat),
      (renderGapBlocks blocks).count letter % 2 =
        (renderSweptPriorBlocks blocks ++
          sweptPriorDebt blocks).count letter % 2
  | [], letter => by
      simp [renderGapBlocks, renderSweptPriorBlocks, sweptPriorDebt]
  | block :: rest, letter => by
      have headAccounting :=
        count_gapBlock_mod_two_eq_sweptGap block letter
      have tailAccounting :=
        count_renderGapBlocks_mod_two_eq_swept rest letter
      simp only [renderGapBlocks, renderSweptPriorBlocks,
        sweptPriorDebt, List.count_cons, List.count_append] at *
      omega

/-- Any rendered prior-power letter is one of the datum labels. -/
private theorem renderPriorPowerData_support
    {data : List PriorPowerDatum} {letter : Nat}
    (member : letter ∈ renderPriorPowerData data) :
    letter ∈ data.map (fun datum => datum.entry.phase.label) :=
  mem_renderPriorPowerData_labels member

/-- Any letter in the raw prior-power rendering is the label of a source
datum.  This public support direction is needed after the exact carrier has
been split into displayed pairs. -/
theorem renderPriorPowerData_label_support
    {data : List PriorPowerDatum} {letter : Nat}
    (member : letter ∈ renderPriorPowerData data) :
    letter ∈ data.map (fun datum => datum.entry.phase.label) :=
  mem_renderPriorPowerData_labels member

/-- Under distinct datum labels, the selected datum contributes its complete
exponent and every other datum contributes zero to its label count. -/
theorem count_renderPriorPowerData_self
    {data : List PriorPowerDatum}
    (labelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup)
    {datum : PriorPowerDatum} (member : datum ∈ data) :
    (renderPriorPowerData data).count datum.entry.phase.label =
      datum.exponent := by
  induction data with
  | nil =>
      simp at member
  | cons head rest induction =>
      have labelData :
          head.entry.phase.label ∉
              rest.map (fun datum => datum.entry.phase.label) ∧
            (rest.map
              (fun datum => datum.entry.phase.label)).Nodup := by
        simpa using List.nodup_cons.mp labelsNodup
      rcases List.mem_cons.mp member with atHead | inRest
      · subst datum
        have tailAbsent :
            head.entry.phase.label ∉ renderPriorPowerData rest := by
          intro inRendered
          exact labelData.1 <|
            renderPriorPowerData_support inRendered
        simp only [renderPriorPowerData, renderPriorPowerDatum,
          List.count_append, count_replicate_self_local]
        rw [List.count_eq_zero.mpr tailAbsent]
        omega
      · have different :
            datum.entry.phase.label ≠ head.entry.phase.label := by
          intro equal
          apply labelData.1
          rw [← equal]
          exact List.mem_map.mpr ⟨datum, inRest, rfl⟩
        rw [renderPriorPowerData, renderPriorPowerDatum,
          List.count_append,
          count_replicate_of_ne_local different,
          Nat.zero_add]
        exact induction labelData.2 inRest

/-- Under distinct datum labels, a selected label occurs in the debt-label
list exactly when its own stored correction bit is set. -/
theorem count_priorDebtLabels_self
    {data : List PriorPowerDatum}
    (labelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup)
    {datum : PriorPowerDatum} (member : datum ∈ data) :
    (priorDebtLabels data).count datum.entry.phase.label =
      if datum.debtBit then 1 else 0 := by
  induction data with
  | nil =>
      simp at member
  | cons head rest induction =>
      have labelData :
          head.entry.phase.label ∉
              rest.map (fun datum => datum.entry.phase.label) ∧
            (rest.map
              (fun datum => datum.entry.phase.label)).Nodup := by
        simpa using List.nodup_cons.mp labelsNodup
      rcases List.mem_cons.mp member with atHead | inRest
      · subst datum
        have tailAbsent :
            head.entry.phase.label ∉ priorDebtLabels rest := by
          intro inDebt
          exact labelData.1 <|
            mem_priorDebtLabels_dataLabels inDebt
        cases debtBit : head.debtBit <;>
          simp [priorDebtLabels, debtBit,
            List.count_eq_zero.mpr tailAbsent]
      · have different :
            datum.entry.phase.label ≠ head.entry.phase.label := by
          intro equal
          apply labelData.1
          rw [← equal]
          exact List.mem_map.mpr ⟨datum, inRest, rfl⟩
        cases debtBit : head.debtBit <;>
          simpa [priorDebtLabels, debtBit, different,
            Ne.symm different] using induction labelData.2 inRest

/-- Distinct datum labels imply distinct selected one-copy debt labels. -/
theorem priorDebtLabels_nodup
    (data : List PriorPowerDatum)
    (labelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup) :
    (priorDebtLabels data).Nodup := by
  induction data with
  | nil =>
      simp [priorDebtLabels]
  | cons datum rest induction =>
      have labelData :
          datum.entry.phase.label ∉
              rest.map (fun selected => selected.entry.phase.label) ∧
            (rest.map
              (fun selected => selected.entry.phase.label)).Nodup := by
        simpa using List.nodup_cons.mp labelsNodup
      have tailNodup := induction labelData.2
      cases debtBit : datum.debtBit with
      | false =>
          simpa [priorDebtLabels, debtBit] using tailNodup
      | true =>
          have tailAbsent :
              datum.entry.phase.label ∉ priorDebtLabels rest := by
            intro inDebt
            exact labelData.1 <|
              mem_priorDebtLabels_dataLabels inDebt
          simpa [priorDebtLabels, debtBit, tailAbsent] using tailNodup

private theorem mem_eraseDups_iff_local [BEq α] [LawfulBEq α] :
    ∀ (entry : α) (entries : List α),
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | entry, [] => by simp
  | entry, head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff_local entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  _ entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem nodup_eraseDups_local [BEq α] [LawfulBEq α] :
    ∀ entries : List α, entries.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        have filteredMember :=
          (mem_eraseDups_iff_local head
            (tail.filter fun candidate => !candidate == head)).mp member
        simpa using filteredMember
      · exact nodup_eraseDups_local
          (tail.filter fun candidate => !candidate == head)
termination_by
  entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem count_flatMap_replicate_of_nodup_local
    (amount : Nat → Nat) (tested : Nat) :
    ∀ {support : List Nat}, support.Nodup →
      (support.flatMap (fun letter =>
        List.replicate (amount letter) letter)).count tested =
          if tested ∈ support then amount tested else 0
  | [], _ => by simp
  | head :: tail, nodup => by
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [List.flatMap_cons, List.count_append,
        count_flatMap_replicate_of_nodup_local amount tested tailNodup]
      by_cases testedEq : tested = head
      · subst tested
        simp [count_replicate_self_local, headFresh]
      · rw [count_replicate_of_ne_local testedEq]
        simp [testedEq]

private theorem mem_flatMap_replicate_support_local
    (amount : Nat → Nat) {support : List Nat} {tested : Nat}
    (member :
      tested ∈ support.flatMap (fun letter =>
        List.replicate (amount letter) letter)) :
    tested ∈ support := by
  rcases List.mem_flatMap.mp member with
    ⟨letter, inSupport, inCopies⟩
  have equal : tested = letter :=
    List.eq_of_mem_replicate inCopies
  subst tested
  exact inSupport

private theorem eq_twice_div_two_add_of_mod_two_eq_of_le_one
    {whole remainder : Nat}
    (remainderAtMostOne : remainder ≤ 1)
    (sameParity : whole % 2 = remainder % 2) :
    whole = 2 * (whole / 2) + remainder := by
  omega

theorem exists_pairMarkers_of_mod_two_count
    (debt oddLabels : List Nat)
    (oddLabelsNodup : oddLabels.Nodup)
    (modTwo :
      ∀ letter,
        debt.count letter % 2 = oddLabels.count letter % 2) :
    ∃ pairMarkers : List Nat,
      (∀ letter,
        debt.count letter =
          2 * pairMarkers.count letter + oddLabels.count letter) ∧
      (∀ marker, marker ∈ pairMarkers → marker ∈ debt) := by
  let support := debt.eraseDups
  let pairMarkers :=
    support.flatMap (fun letter =>
      List.replicate (debt.count letter / 2) letter)
  have supportNodup : support.Nodup := by
    change debt.eraseDups.Nodup
    exact nodup_eraseDups_local debt
  have supportMem (letter : Nat) :
      letter ∈ support ↔ letter ∈ debt := by
    change letter ∈ debt.eraseDups ↔ letter ∈ debt
    exact mem_eraseDups_iff_local letter debt
  have pairCount (letter : Nat) :
      pairMarkers.count letter =
        if letter ∈ support then debt.count letter / 2 else 0 := by
    change
      (support.flatMap (fun selected =>
        List.replicate (debt.count selected / 2) selected)).count letter = _
    exact count_flatMap_replicate_of_nodup_local
      (fun selected => debt.count selected / 2)
      letter supportNodup
  refine ⟨pairMarkers, ?_, ?_⟩
  · intro letter
    rw [pairCount letter]
    have remainderAtMostOne : oddLabels.count letter ≤ 1 :=
      List.nodup_iff_count.mp oddLabelsNodup letter
    have exactSplit :=
      eq_twice_div_two_add_of_mod_two_eq_of_le_one
        remainderAtMostOne (modTwo letter)
    by_cases inDebt : letter ∈ debt
    · rw [if_pos ((supportMem letter).mpr inDebt)]
      exact exactSplit
    · have outsideSupport : letter ∉ support := by
        intro inSupport
        exact inDebt ((supportMem letter).mp inSupport)
      rw [if_neg outsideSupport]
      have debtCountZero : debt.count letter = 0 :=
        List.count_eq_zero.mpr inDebt
      simpa [debtCountZero] using exactSplit
  · intro marker markerMember
    change marker ∈ support.flatMap (fun selected =>
      List.replicate (debt.count selected / 2) selected) at markerMember
    exact (supportMem marker).mp
      (mem_flatMap_replicate_support_local
        (fun selected => debt.count selected / 2) markerMember)

/-- Split the corrected prior-label carrier into exact pairs and the selected
one-copy debt labels.  The all-letter parity premise is intentionally explicit:
it is the sweep/accounting bridge, not a consequence of support. -/
theorem exists_activePriorDebt_pairMarkers
    {before after : List GapBlock} {lastBlock : GapBlock}
    {data : List PriorPowerDatum}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after))
    (dataRender :
      renderPriorPowerData data = renderSweptPriorBlocks before)
    (labelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup)
    (modTwo :
      ∀ letter,
        (gapDebt lastBlock ++ sweptPriorDebt before).count letter % 2 =
          (priorDebtLabels data).count letter % 2) :
    ∃ pairMarkers : List Nat,
      (∀ letter,
        (gapDebt lastBlock ++ sweptPriorDebt before).count letter =
          2 * pairMarkers.count letter +
            (priorDebtLabels data).count letter) ∧
      (∀ marker, marker ∈ pairMarkers →
        marker ∈ renderPriorPowerData data) := by
  have oddLabelsNodup : (priorDebtLabels data).Nodup :=
    priorDebtLabels_nodup data labelsNodup
  obtain ⟨pairMarkers, countSplit, markerInDebt⟩ :=
    exists_pairMarkers_of_mod_two_count
      (gapDebt lastBlock ++ sweptPriorDebt before)
      (priorDebtLabels data) oddLabelsNodup modTwo
  refine ⟨pairMarkers, countSplit, ?_⟩
  intro marker markerMember
  exact activePriorDebt_seen_in_renderPriorPowerData
    formed dataRender marker
      (markerInDebt marker markerMember)

/-- The complete active prior-debt carrier has exactly the one-copy parity
residue selected by the aligned prior-power data.  The carrier includes the
old-letter debt of the selected final gap; omitting that summand is falsified
by the `[0, 1, 0]` and `[1, 0, 1]` regression words recorded above. -/
theorem activePriorDebt_count_mod_two_eq_priorDebtLabels
    (word : Word Nat)
    {beforeBlocks afterBlocks : List GapBlock} {lastBlock : GapBlock}
    {beforeEntries afterEntries : List PhaseParityEntry}
    {lastEntry : PhaseParityEntry} {data : List PriorPowerDatum}
    (sourceSplit :
      gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks)
    (afterEmpty :
      forall block, block ∈ afterBlocks -> block.seconds = [])
    (entrySplit :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries)
    (beforeAligned :
      beforeEntries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock)
    (dataEntries :
      data.map (fun datum => datum.entry) = beforeEntries)
    (dataRender :
      renderPriorPowerData data =
        renderSweptPriorBlocks beforeBlocks) :
    forall letter,
      (gapDebt lastBlock ++ sweptPriorDebt beforeBlocks).count letter % 2 =
        (priorDebtLabels data).count letter := by
  have formed :
      GapBlocksWellFormed []
        (beforeBlocks ++ lastBlock :: afterBlocks) := by
    rw [← sourceSplit]
    exact gapBlocksList_wellFormed word.toList
  have beforeFormed : GapBlocksWellFormed [] beforeBlocks :=
    (gapBlocksWellFormed_append formed).1
  have dataLabelsShape :
      data.map (fun datum => datum.entry.phase.label) =
        gapBlockMarkers beforeBlocks :=
    priorPowerData_labels_eq_gapBlockMarkers
      beforeBlocks beforeEntries data dataEntries beforeAligned
  have dataLabelsNodup :
      (data.map (fun datum => datum.entry.phase.label)).Nodup := by
    rw [dataLabelsShape]
    exact beforeFormed.markersNodup
  have markerSplitNodup :
      (gapBlockMarkers beforeBlocks ++
        lastBlock.marker :: gapBlockMarkers afterBlocks).Nodup := by
    simpa [gapBlockMarkers] using formed.markersNodup
  have beforeTailDisjoint :=
    (List.nodup_append.mp markerSplitNodup).2.2
  have activeSeen :=
    activePriorDebt_seen_in_renderPriorPowerData formed dataRender
  intro letter
  by_cases supported :
      letter ∈ data.map (fun datum => datum.entry.phase.label)
  · obtain ⟨datum, datumMember, labelEqual⟩ :=
      List.mem_map.mp supported
    subst letter
    have datumEntryMemberBefore : datum.entry ∈ beforeEntries := by
      rw [← dataEntries]
      exact List.mem_map.mpr ⟨datum, datumMember, rfl⟩
    have datumEntryMember :
        datum.entry ∈
          phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word) := by
      rw [entrySplit]
      exact List.mem_append.mpr <| Or.inl datumEntryMemberBefore
    have datumLabelMember :
        datum.entry.phase.label ∈
          data.map (fun selected => selected.entry.phase.label) :=
      List.mem_map.mpr ⟨datum, datumMember, rfl⟩
    have beforeMarkerMember :
        datum.entry.phase.label ∈ gapBlockMarkers beforeBlocks := by
      rw [← dataLabelsShape]
      exact datumLabelMember
    have notInMarkerTail :
        datum.entry.phase.label ∉
          lastBlock.marker :: gapBlockMarkers afterBlocks := by
      intro inTail
      exact beforeTailDisjoint
        datum.entry.phase.label beforeMarkerMember
        datum.entry.phase.label inTail rfl
    have differentLast :
        datum.entry.phase.label ≠ lastBlock.marker := by
      intro equal
      apply notInMarkerTail
      simp [equal]
    have absentAfterMarkers :
        datum.entry.phase.label ∉ gapBlockMarkers afterBlocks := by
      intro member
      exact notInMarkerTail <| List.Mem.tail _ member
    have afterRenderedCountZero :
        (renderGapBlocks afterBlocks).count
            datum.entry.phase.label = 0 := by
      rw [
        SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.renderGapBlocks_eq_markers_of_seconds_empty
          afterBlocks afterEmpty]
      exact List.count_eq_zero.mpr absentAfterMarkers
    have lastMarkerCountZero :
        [lastBlock.marker].count datum.entry.phase.label = 0 := by
      simp [differentLast, Ne.symm differentLast]
    have sourceRender :
        word.toList =
          renderGapBlocks beforeBlocks ++ [lastBlock.marker] ++
            lastBlock.seconds ++ renderGapBlocks afterBlocks := by
      calc
        word.toList =
            renderGapBlocks (gapBlocksList word.toList) :=
          (render_gapBlocksList word.toList).symm
        _ = renderGapBlocks
            (beforeBlocks ++ lastBlock :: afterBlocks) := by
          rw [sourceSplit]
        _ = renderGapBlocks beforeBlocks ++ [lastBlock.marker] ++
            lastBlock.seconds ++ renderGapBlocks afterBlocks := by
          rw [
            SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.renderGapBlocks_append]
          simp [renderGapBlocks, List.append_assoc]
    have sourceCount :
        word.toList.count datum.entry.phase.label =
          (renderGapBlocks beforeBlocks).count
              datum.entry.phase.label +
            lastBlock.seconds.count datum.entry.phase.label := by
      rw [sourceRender]
      simp only [List.count_append]
      rw [lastMarkerCountZero, afterRenderedCountZero]
      omega
    have lastDebtCount :
        (gapDebt lastBlock).count datum.entry.phase.label =
          lastBlock.seconds.count datum.entry.phase.label :=
      count_gapDebt_of_ne lastBlock differentLast
    have sweptPowerCount :
        (renderSweptPriorBlocks beforeBlocks).count
            datum.entry.phase.label = datum.exponent := by
      rw [← dataRender]
      exact count_renderPriorPowerData_self
        dataLabelsNodup datumMember
    have beforeSweepParity :
        (renderGapBlocks beforeBlocks).count
              datum.entry.phase.label % 2 =
          (datum.exponent +
            (sweptPriorDebt beforeBlocks).count
              datum.entry.phase.label) % 2 := by
      calc
        (renderGapBlocks beforeBlocks).count
              datum.entry.phase.label % 2 =
            (renderSweptPriorBlocks beforeBlocks ++
              sweptPriorDebt beforeBlocks).count
                datum.entry.phase.label % 2 :=
          count_renderGapBlocks_mod_two_eq_swept
            beforeBlocks datum.entry.phase.label
        _ = (datum.exponent +
            (sweptPriorDebt beforeBlocks).count
              datum.entry.phase.label) % 2 := by
          rw [List.count_append, sweptPowerCount]
    have storedParity :
        datum.entry.parity =
          word.toList.count datum.entry.phase.label % 2 :=
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.phaseParityEntry_parity_eq_source_count
        word datumEntryMember
    have sourceParity :
        datum.entry.parity =
          ((renderGapBlocks beforeBlocks).count
              datum.entry.phase.label +
            (gapDebt lastBlock).count
              datum.entry.phase.label) % 2 := by
      calc
        datum.entry.parity =
            word.toList.count datum.entry.phase.label % 2 := storedParity
        _ = ((renderGapBlocks beforeBlocks).count
                datum.entry.phase.label +
              lastBlock.seconds.count
                datum.entry.phase.label) % 2 := by
          rw [sourceCount]
        _ = ((renderGapBlocks beforeBlocks).count
                datum.entry.phase.label +
              (gapDebt lastBlock).count
                datum.entry.phase.label) % 2 := by
          rw [lastDebtCount]
    have datumParity := datum.parity_eq
    have debtLabelCount :=
      count_priorDebtLabels_self dataLabelsNodup datumMember
    rw [List.count_append, debtLabelCount]
    cases debtBit : datum.debtBit with
    | false =>
        simp [debtBit] at datumParity ⊢
        omega
    | true =>
        simp [debtBit] at datumParity ⊢
        omega
  · have activeAbsent :
        letter ∉ gapDebt lastBlock ++ sweptPriorDebt beforeBlocks := by
      intro member
      exact supported <| renderPriorPowerData_support <|
        activeSeen letter member
    have priorDebtAbsent : letter ∉ priorDebtLabels data := by
      intro member
      exact supported <| mem_priorDebtLabels_dataLabels member
    rw [List.count_eq_zero.mpr activeAbsent,
      List.count_eq_zero.mpr priorDebtAbsent]

/-! ## Exact pair/odd decomposition of witnessed debt -/

theorem count_displayedMarkerPairs
    (markers : List Nat) (letter : Nat) :
    (displayedMarkerPairs markers).count letter =
      2 * markers.count letter := by
  induction markers with
  | nil =>
      simp [displayedMarkerPairs]
  | cons marker rest induction =>
      by_cases equal : marker = letter
      · subst marker
        simp [displayedMarkerPairs, induction] <;> omega
      · have reverse : letter ≠ marker := Ne.symm equal
        simp [displayedMarkerPairs, induction, equal, reverse]

/-- Pure multiplicity criterion for the exact debt permutation used after the
sweep.  `pairMarkers` indexes adjacent equal pairs; `oddLabels` contains the
unpaired copies. -/
theorem debt_perm_displayedPairs_append_oddLabels
    (debt pairMarkers oddLabels : List Nat)
    (countSplit :
      forall letter,
        debt.count letter =
          2 * pairMarkers.count letter + oddLabels.count letter) :
    debt.Perm (displayedMarkerPairs pairMarkers ++ oddLabels) := by
  apply List.perm_iff_count.mpr
  intro letter
  rw [List.count_append,
    count_displayedMarkerPairs, countSplit]

/-- Turn the pure pair/odd multiplicity decomposition into a literal (23.1e)
derivation once all debt letters have earlier witnesses. -/
theorem hullListDerivesDecomposeWitnessedDebt
    (witnesses suffix debt pairMarkers oddLabels : List Nat)
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ witnesses)
    (countSplit :
      forall letter,
        debt.count letter =
          2 * pairMarkers.count letter + oddLabels.count letter) :
    HullListDerives
      (witnesses ++ debt ++ suffix)
      (witnesses ++ displayedMarkerPairs pairMarkers ++
        oddLabels ++ suffix) := by
  have permutation :=
    debt_perm_displayedPairs_append_oddLabels
      debt pairMarkers oddLabels countSplit
  simpa [List.append_assoc] using
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves.hullListDerivesWitnessedTailPermutation
      witnesses suffix debtSeen permutation

/-- Move a selected unpaired debt copy immediately after the gathered prefix.
This is the precise list operation used to absorb last-marker debt into the
last power. -/
theorem hullListDerivesMoveSelectedDebtToFront
    (witnesses suffix debt : List Nat) (selected : Nat)
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ witnesses)
    (selectedMember : selected ∈ debt) :
    HullListDerives
      (witnesses ++ debt ++ suffix)
      (witnesses ++ [selected] ++ debt.erase selected ++ suffix) := by
  have permutation :
      debt.Perm (selected :: debt.erase selected) :=
    List.perm_cons_erase selectedMember
  simpa [List.append_assoc] using
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves.hullListDerivesWitnessedTailPermutation
      witnesses suffix debtSeen permutation

/-! ## Canonical even-power blocks for two copied tail words -/

/-- One square, with no surplus pair, for a displayed tail occurrence. -/
def evenPowerBlockOfMarker (marker : Nat) : EvenPowerBlock where
  marker := marker
  extraPairs := []

/-- A canonical even-power block for every occurrence in a tail.  Repeated
tail letters are intentionally retained as distinct blocks: this makes the
builder valid without a support-nodup side condition. -/
def evenPowerBlocksOfTail (tail : List Nat) : List EvenPowerBlock :=
  tail.map evenPowerBlockOfMarker

theorem renderEvenPowerBlocks_evenPowerBlocksOfTail :
    forall tail : List Nat,
      renderEvenPowerBlocks (evenPowerBlocksOfTail tail) =
        displayedMarkerPairs tail
  | [] => rfl
  | marker :: rest => by
      change [marker, marker] ++
          renderEvenPowerBlocks (evenPowerBlocksOfTail rest) =
        [marker, marker] ++ displayedMarkerPairs rest
      rw [renderEvenPowerBlocks_evenPowerBlocksOfTail rest]

theorem powerBlockMarkers_evenPowerBlocksOfTail :
    forall tail : List Nat,
      powerBlockMarkers (evenPowerBlocksOfTail tail) = tail
  | [] => rfl
  | marker :: rest => by
      change marker ::
          powerBlockMarkers (evenPowerBlocksOfTail rest) =
        marker :: rest
      exact congrArg (List.cons marker)
        (powerBlockMarkers_evenPowerBlocksOfTail rest)

theorem evenPowerBlocksOfTail_split_terminal
    (tailStem : List Nat) (terminal : Nat) :
    evenPowerBlocksOfTail (tailStem ++ [terminal]) =
      evenPowerBlocksOfTail tailStem ++
        [evenPowerBlockOfMarker terminal] := by
  simp [evenPowerBlocksOfTail]

theorem evenPowerBlocksOfTail_markers_seen
    (tail : List Nat) :
    forall block, block ∈ evenPowerBlocksOfTail tail ->
      block.marker ∈ tail := by
  intro block member
  obtain ⟨marker, markerMember, blockShape⟩ :=
    List.mem_map.mp member
  subst block
  simpa [evenPowerBlockOfMarker] using markerMember

/-- The two copied tail words have exactly the multiplicities of the
canonical even-power-block rendering. -/
theorem copiedTailOrder_evenPowerBlocksOfTail
    (tail : List Nat) :
    (tail ++ tail).Perm
      (renderEvenPowerBlocks (evenPowerBlocksOfTail tail)) := by
  apply List.perm_iff_count.mpr
  intro letter
  rw [List.count_append,
    renderEvenPowerBlocks_evenPowerBlocksOfTail,
    count_displayedMarkerPairs]
  omega

/-- The second Exchange stage of the exceptional chain, specialized to the
canonical copied-tail builder. -/
theorem hullListDerivesGroupCopiedTail
    (witnesses suffix tail : List Nat)
    (tailSeen :
      forall letter, letter ∈ tail -> letter ∈ witnesses) :
    HullListDerives
      (witnesses ++ tail ++ tail ++ suffix)
      (witnesses ++
        renderEvenPowerBlocks (evenPowerBlocksOfTail tail) ++ suffix) := by
  have copiedSeen :
      forall letter, letter ∈ tail ++ tail -> letter ∈ witnesses := by
    intro letter member
    rcases List.mem_append.mp member with first | second
    · exact tailSeen letter first
    · exact tailSeen letter second
  simpa [List.append_assoc] using
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves.hullListDerivesWitnessedTailPermutation
      witnesses suffix copiedSeen
      (copiedTailOrder_evenPowerBlocksOfTail tail)

/-! ## Ordinary prior-power caps -/

theorem replicate_add_power
    (left right : Nat) (marker : Nat) :
    List.replicate (left + right) marker =
      List.replicate left marker ++ List.replicate right marker := by
  induction left with
  | zero => simp
  | succ copies induction =>
      have shift : copies + 1 + right = (copies + right) + 1 := by
        omega
      rw [shift, List.replicate_succ, List.replicate_succ,
        List.cons_append, induction]

theorem markerPairTail_eq_replicate
    (marker : Nat) :
    forall indices : List Nat,
      markerPairTail marker indices =
        List.replicate (2 * indices.length) marker
  | [] => rfl
  | _ :: rest => by
      simp only [markerPairTail, List.length_cons]
      rw [markerPairTail_eq_replicate marker rest]
      have arithmetic : 2 * (rest.length + 1) =
          2 + 2 * rest.length := by omega
      rw [arithmetic, replicate_add_power]
      rfl

theorem exists_evenMarkerPower_shape
    (marker exponent : Nat)
    (atLeastTwo : 2 <= exponent)
    (even : exponent % 2 = 0) :
    exists indices : List Nat,
      List.replicate exponent marker =
        [marker, marker] ++ markerPairTail marker indices := by
  let pairs := (exponent - 2) / 2
  have exponentShape : exponent = 2 + 2 * pairs := by
    dsimp [pairs]
    omega
  refine ⟨List.replicate pairs 0, ?_⟩
  rw [markerPairTail_eq_replicate, List.length_replicate]
  calc
    List.replicate exponent marker =
        List.replicate (2 + 2 * pairs) marker := by
      rw [exponentShape]
    _ = List.replicate 2 marker ++
          List.replicate (2 * pairs) marker :=
      replicate_add_power 2 (2 * pairs) marker
    _ = [marker, marker] ++
          List.replicate (2 * pairs) marker := by rfl

theorem exists_oddMarkerPower_shape
    (marker exponent : Nat)
    (atLeastThree : 3 <= exponent)
    (odd : exponent % 2 = 1) :
    exists indices : List Nat,
      List.replicate exponent marker =
        [marker, marker, marker] ++ markerPairTail marker indices := by
  let pairs := (exponent - 3) / 2
  have exponentShape : exponent = 3 + 2 * pairs := by
    dsimp [pairs]
    omega
  refine ⟨List.replicate pairs 0, ?_⟩
  rw [markerPairTail_eq_replicate, List.length_replicate]
  calc
    List.replicate exponent marker =
        List.replicate (3 + 2 * pairs) marker := by
      rw [exponentShape]
    _ = List.replicate 3 marker ++
          List.replicate (2 * pairs) marker :=
      replicate_add_power 3 (2 * pairs) marker
    _ = [marker, marker, marker] ++
          List.replicate (2 * pairs) marker := by rfl

/-- An undoubled prior phase has no power work: its gathered exponent is
literally one, hence it already renders the canonical marker-only block. -/
theorem hullListDerivesNormalizeUndoubledPriorPower
    (pre post : List Nat) (datum : PriorPowerDatum)
    (undoubled : datum.entry.phase.doubled = false) :
    HullListDerives
      (pre ++ renderPriorPowerDatum datum ++ post)
      (pre ++
        renderGapBlocks [canonicalPriorGapBlock datum.entry] ++ post) := by
  have sourceShape :=
    renderPriorPowerDatum_of_undoubled datum undoubled
  have targetShape :
      renderGapBlocks [canonicalPriorGapBlock datum.entry] =
        [datum.entry.phase.label] := by
    simp [canonicalPriorGapBlock, markerOnlyGapBlock,
      renderGapBlocks, undoubled]
  rw [sourceShape, targetShape]
  exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _

/-- A doubled prior phase with no terminal singleton caps directly to its
parity-selected square or cube, using (23.1b). -/
theorem hullListDerivesNormalizeDoubledPriorPowerNoDebt
    (pre post : List Nat) (datum : PriorPowerDatum)
    (doubled : datum.entry.phase.doubled = true)
    (noDebt : datum.debtBit = false) :
    HullListDerives
      (pre ++ renderPriorPowerDatum datum ++ post)
      (pre ++
        renderGapBlocks [canonicalPriorGapBlock datum.entry] ++ post) := by
  have atLeastTwo := datum.doubled_ge_two doubled
  have exponentParity := priorPowerParity_of_noDebt datum noDebt
  by_cases even : datum.entry.parity % 2 = 0
  · have exponentEven : datum.exponent % 2 = 0 := by
      rw [exponentParity, even]
    obtain ⟨indices, sourceShape⟩ :=
      exists_evenMarkerPower_shape
        datum.entry.phase.label datum.exponent
        atLeastTwo exponentEven
    have targetShape :
        renderGapBlocks [canonicalPriorGapBlock datum.entry] =
          [datum.entry.phase.label, datum.entry.phase.label] := by
      simp [canonicalPriorGapBlock, priorDoubledGapBlock,
        renderGapBlocks, doubled, even]
    rw [renderPriorPowerDatum, sourceShape, targetShape]
    simpa only [List.append_assoc] using
      hullListDerivesNormalizeEvenMarkerPower
        pre post indices datum.entry.phase.label
  · have parityBound : datum.entry.parity % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    have parityOdd : datum.entry.parity % 2 = 1 := by omega
    have exponentOdd : datum.exponent % 2 = 1 := by
      rw [exponentParity, parityOdd]
    have atLeastThree : 3 <= datum.exponent := by omega
    obtain ⟨indices, sourceShape⟩ :=
      exists_oddMarkerPower_shape
        datum.entry.phase.label datum.exponent
        atLeastThree exponentOdd
    have targetShape :
        renderGapBlocks [canonicalPriorGapBlock datum.entry] =
          [datum.entry.phase.label, datum.entry.phase.label,
            datum.entry.phase.label] := by
      simp [canonicalPriorGapBlock, priorDoubledGapBlock,
        renderGapBlocks, doubled, even]
    rw [renderPriorPowerDatum, sourceShape, targetShape]
    simpa only [List.append_assoc] using
      hullListDerivesNormalizeOddMarkerPower
        pre post indices datum.entry.phase.label

/-! ## Exceptional doubled power with one terminal copy -/

/-- A doubled gathered power followed by its one terminal debt copy has the
exact prefix shape expected by the Condition-IV exceptional theorem.  The
selected result also has the stored target parity. -/
theorem exists_conditionIVExceptionalPowerShape
    (datum : PriorPowerDatum)
    (doubled : datum.entry.phase.doubled = true)
    (hasDebt : datum.debtBit = true) :
    exists (result : ConditionIVActiveResult) (excessPairs : List Nat),
      renderPriorPowerDatum datum =
        conditionIVExceptionalPrefix result []
            datum.entry.phase.label excessPairs ++
          [datum.entry.phase.label, datum.entry.phase.label] /\
      (renderConditionIVActivePower
          result datum.entry.phase.label).count
            datum.entry.phase.label % 2 =
        datum.entry.parity % 2 := by
  have atLeastTwo := datum.doubled_ge_two doubled
  have absorbedParity := priorPowerParity_after_debt datum hasDebt
  by_cases even : datum.exponent % 2 = 0
  · obtain ⟨indices, powerShape⟩ :=
      exists_evenMarkerPower_shape
        datum.entry.phase.label datum.exponent atLeastTwo even
    have targetParity : datum.entry.parity % 2 = 1 := by
      have parityBound : datum.entry.parity % 2 < 2 :=
        Nat.mod_lt _ (by omega)
      omega
    refine ⟨.cube, indices, ?_⟩
    constructor
    · rw [renderPriorPowerDatum, powerShape]
      simpa [conditionIVExceptionalPrefix, List.append_assoc] using
        (markerPairTail_append_pair
          datum.entry.phase.label indices).symm
    · simp [renderConditionIVActivePower, targetParity]
  · have exponentBound : datum.exponent % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    have odd : datum.exponent % 2 = 1 := by omega
    have atLeastThree : 3 <= datum.exponent := by omega
    obtain ⟨indices, powerShape⟩ :=
      exists_oddMarkerPower_shape
        datum.entry.phase.label datum.exponent atLeastThree odd
    have targetParity : datum.entry.parity % 2 = 0 := by
      have parityBound : datum.entry.parity % 2 < 2 :=
        Nat.mod_lt _ (by omega)
      omega
    refine ⟨.square, indices, ?_⟩
    constructor
    · rw [renderPriorPowerDatum, powerShape]
      have commute :=
        congrArg
          (fun letters => [datum.entry.phase.label] ++ letters)
          (markerPairTail_append_pair
            datum.entry.phase.label indices).symm
      simpa [conditionIVExceptionalPrefix,
        List.append_assoc] using commute
    · simp [renderConditionIVActivePower, targetParity]

/-- Specialization of the literal six-step exceptional repair to the
canonical copied-tail builder.  No externally supplied permutation of the
two copied tails is required. -/
theorem hullListDerivesExceptionalPriorPowerWithTail
    (stable suffix debt tailStem : List Nat)
    (datum : PriorPowerDatum) (terminal : Nat)
    (doubled : datum.entry.phase.doubled = true)
    (hasDebt : datum.debtBit = true)
    (debtSeen :
      forall letter, letter ∈ debt ->
        letter ∈
          stable ++ renderPriorPowerDatum datum ++
            (tailStem ++ [terminal])) :
    exists result : ConditionIVActiveResult,
      (renderConditionIVActivePower
          result datum.entry.phase.label).count
            datum.entry.phase.label % 2 =
        datum.entry.parity % 2 /\
      HullListDerives
        (stable ++ renderPriorPowerDatum datum ++
          (tailStem ++ [terminal]) ++ debt ++
          [datum.entry.phase.label] ++ suffix)
        (stable ++
          renderConditionIVActivePower
            result datum.entry.phase.label ++
          tailStem ++ [terminal, terminal, terminal] ++
          debt ++ suffix) := by
  obtain ⟨result, excessPairs, powerShape, resultParity⟩ :=
    exists_conditionIVExceptionalPowerShape datum doubled hasDebt
  let tail := tailStem ++ [terminal]
  let blocks := evenPowerBlocksOfTail tail
  let earlierBlocks := evenPowerBlocksOfTail tailStem
  let terminalBlock := evenPowerBlockOfMarker terminal
  have prefixShape :
      conditionIVExceptionalPrefix result stable
          datum.entry.phase.label excessPairs ++
          [datum.entry.phase.label, datum.entry.phase.label] =
        stable ++ renderPriorPowerDatum datum := by
    rw [powerShape]
    cases result <;>
      simp [conditionIVExceptionalPrefix, List.append_assoc]
  have debtSeen' :
      forall letter, letter ∈ debt ->
        letter ∈
          conditionIVExceptionalPrefix result stable
              datum.entry.phase.label excessPairs ++
            [datum.entry.phase.label, datum.entry.phase.label] ++ tail := by
    intro letter member
    rw [prefixShape]
    simpa [tail, List.append_assoc] using debtSeen letter member
  have tailNonempty : tail ≠ [] := by
    simp [tail]
  have tailShape : tail = tailStem ++ [terminal] := rfl
  have blocksShape :
      blocks = earlierBlocks ++ [terminalBlock] := by
    simp [blocks, earlierBlocks, terminalBlock,
      tail, evenPowerBlocksOfTail_split_terminal]
  have terminalBlockMarker : terminalBlock.marker = terminal := rfl
  have copiedTailOrder :
      (tail ++ tail).Perm (renderEvenPowerBlocks blocks) := by
    simpa [blocks] using copiedTailOrder_evenPowerBlocksOfTail tail
  have earlierMarkersSeen :
      forall block, block ∈ earlierBlocks ->
        block.marker ∈ tailStem := by
    intro block member
    exact evenPowerBlocksOfTail_markers_seen
      tailStem block (by simpa [earlierBlocks] using member)
  have repaired :=
    hullListDerivesExceptionalTerminalRepairConditionIV
      stable suffix debt tail tailStem excessPairs
      datum.entry.phase.label terminal result
      blocks earlierBlocks terminalBlock
      tailNonempty tailShape blocksShape terminalBlockMarker
      debtSeen' copiedTailOrder earlierMarkersSeen
  rw [prefixShape] at repaired
  refine ⟨result, resultParity, ?_⟩
  exact by
    simpa [tail, List.append_assoc] using repaired

/-! ## Final terminal power -/

/-- The state returned after the prior debt pairs have been transferred to
the selected final marker.  The singleton side condition is exactly the
published Condition-V boundary: a terminal exponent of one is permitted only
when nonempty parity debt keeps the last gap doubled. -/
structure TerminalPowerDatum where
  entry : PhaseParityEntry
  exponent : Nat
  debt : List Nat
  exponent_pos : 0 < exponent
  parity_eq : exponent % 2 = entry.parity % 2
  singleton_has_debt : exponent = 1 -> debt ≠ []

def renderTerminalPowerDatum (datum : TerminalPowerDatum) : List Nat :=
  List.replicate datum.exponent datum.entry.phase.label ++ datum.debt

/-- Cap the gathered terminal exponent to the exact final doubled block.

* even parity contracts to a square;
* odd parity with empty debt contracts to a cube;
* odd parity with nonempty debt is either already a singleton or first caps
  to a cube and then uses (23.1d) to return to a singleton.
-/
theorem hullListDerivesNormalizeTerminalPower
    (pre post : List Nat) (datum : TerminalPowerDatum)
    (debtSeen :
      forall letter, letter ∈ datum.debt -> letter ∈ pre) :
    HullListDerives
      (pre ++ renderTerminalPowerDatum datum ++ post)
      (pre ++
        renderGapBlocks
          [lastDoubledGapBlock datum.debt datum.entry] ++ post) := by
  by_cases even : datum.entry.parity % 2 = 0
  · have exponentEven : datum.exponent % 2 = 0 := by
      rw [datum.parity_eq, even]
    have atLeastTwo : 2 <= datum.exponent := by
      have bound : datum.exponent % 2 < 2 :=
        Nat.mod_lt _ (by omega)
      have exponentPositive : 0 < datum.exponent :=
        datum.exponent_pos
      omega
    obtain ⟨indices, powerShape⟩ :=
      exists_evenMarkerPower_shape
        datum.entry.phase.label datum.exponent
        atLeastTwo exponentEven
    have targetShape :
        renderGapBlocks
            [lastDoubledGapBlock datum.debt datum.entry] =
          [datum.entry.phase.label, datum.entry.phase.label] ++
            datum.debt := by
      simp [lastDoubledGapBlock, renderGapBlocks, even]
    have capped :=
      hullListDerivesNormalizeEvenMarkerPower
        pre (datum.debt ++ post) indices
        datum.entry.phase.label
    simpa [renderTerminalPowerDatum, powerShape, targetShape,
      List.append_assoc] using capped
  · have parityBound : datum.entry.parity % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    have parityOdd : datum.entry.parity % 2 = 1 := by omega
    have exponentOdd : datum.exponent % 2 = 1 := by
      rw [datum.parity_eq, parityOdd]
    by_cases debtEmpty : datum.debt = []
    · have exponentNotOne : datum.exponent ≠ 1 := by
        intro exponentOne
        exact datum.singleton_has_debt exponentOne debtEmpty
      have atLeastThree : 3 <= datum.exponent := by
        have exponentBound : datum.exponent % 2 < 2 :=
          Nat.mod_lt _ (by omega)
        omega
      obtain ⟨indices, powerShape⟩ :=
        exists_oddMarkerPower_shape
          datum.entry.phase.label datum.exponent
          atLeastThree exponentOdd
      have targetShape :
          renderGapBlocks
              [lastDoubledGapBlock datum.debt datum.entry] =
            [datum.entry.phase.label, datum.entry.phase.label,
              datum.entry.phase.label] := by
        simp [lastDoubledGapBlock, renderGapBlocks,
          even, debtEmpty]
      have capped :=
        hullListDerivesNormalizeOddMarkerPower
          pre post indices datum.entry.phase.label
      rw [targetShape]
      simpa [renderTerminalPowerDatum, powerShape,
        debtEmpty, List.append_assoc] using capped
    · by_cases exponentOne : datum.exponent = 1
      · have targetShape :
            renderGapBlocks
                [lastDoubledGapBlock datum.debt datum.entry] =
              [datum.entry.phase.label] ++ datum.debt := by
          simp [lastDoubledGapBlock, renderGapBlocks,
            even, debtEmpty]
        rw [renderTerminalPowerDatum, exponentOne, targetShape]
        exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
      · have atLeastThree : 3 <= datum.exponent := by
          have exponentBound : datum.exponent % 2 < 2 :=
            Nat.mod_lt _ (by omega)
          omega
        obtain ⟨indices, powerShape⟩ :=
          exists_oddMarkerPower_shape
            datum.entry.phase.label datum.exponent
            atLeastThree exponentOdd
        have targetShape :
            renderGapBlocks
                [lastDoubledGapBlock datum.debt datum.entry] =
              [datum.entry.phase.label] ++ datum.debt := by
          simp [lastDoubledGapBlock, renderGapBlocks,
            even, debtEmpty]
        have capped :=
          hullListDerivesNormalizeOddMarkerPower
            pre (datum.debt ++ post) indices
            datum.entry.phase.label
        have returned :=
          hullListDerivesConditionVReturnRepair
            pre post datum.debt datum.entry.phase.label
            debtEmpty debtSeen
        have cappedFromSource :
            HullListDerives
              (pre ++ renderTerminalPowerDatum datum ++ post)
              (pre ++
                [datum.entry.phase.label, datum.entry.phase.label,
                  datum.entry.phase.label] ++ datum.debt ++ post) := by
          simpa [renderTerminalPowerDatum, powerShape,
            List.append_assoc] using capped
        have returnedToTarget :
            HullListDerives
              (pre ++
                [datum.entry.phase.label, datum.entry.phase.label,
                  datum.entry.phase.label] ++ datum.debt ++ post)
              (pre ++
                renderGapBlocks
                  [lastDoubledGapBlock datum.debt datum.entry] ++ post) := by
          simpa [targetShape, List.append_assoc] using returned
        exact cappedFromSource.trans returnedToTarget

/-! ## Closing the square and transferring gathered pairs -/

/-- Close the exposed final square and immediately put the remaining debt
into its exact pair/odd normal form. -/
theorem hullListDerivesCloseSquareAndDecomposeDebt
    (witnesses middle suffix debt pairMarkers oddLabels : List Nat)
    (marker anchor : Nat)
    (anchorSeen : anchor ∈ witnesses ++ [marker])
    (debtSeen :
      forall letter, letter ∈ debt ->
        letter ∈ witnesses ++ [marker] ++ middle ++ [anchor])
    (countSplit :
      forall letter,
        debt.count letter =
          2 * pairMarkers.count letter + oddLabels.count letter) :
    HullListDerives
      (witnesses ++ [marker] ++ middle ++
        [anchor, marker, marker] ++ debt ++ suffix)
      (witnesses ++ [marker] ++ middle ++ [anchor] ++
        displayedMarkerPairs pairMarkers ++ oddLabels ++ suffix) := by
  have closed :=
    hullListDerivesCloseExposedLastGapSquare
      witnesses middle (debt ++ suffix) marker anchor anchorSeen
  let gathered := witnesses ++ [marker] ++ middle ++ [anchor]
  have decomposed :=
    hullListDerivesDecomposeWitnessedDebt
      gathered suffix debt pairMarkers oddLabels
      (by
        intro letter member
        simpa [gathered, List.append_assoc] using debtSeen letter member)
      countSplit
  have closedAligned : HullListDerives
      (witnesses ++ [marker] ++ middle ++
        [anchor, marker, marker] ++ debt ++ suffix)
      (witnesses ++ [marker] ++ middle ++
        [anchor] ++ debt ++ suffix) := by
    simpa only [List.append_assoc] using closed
  have decomposedAligned : HullListDerives
      (witnesses ++ [marker] ++ middle ++
        [anchor] ++ debt ++ suffix)
      (witnesses ++ [marker] ++ middle ++ [anchor] ++
        displayedMarkerPairs pairMarkers ++ oddLabels ++ suffix) := by
    simpa [gathered, List.append_assoc] using decomposed
  exact closedAligned.trans decomposedAligned

/-- Transfer all displayed debt pairs to the selected terminal marker and
contract the accumulated terminal pairs to one cube. -/
theorem hullListDerivesTransferDebtPairsToTerminalCube
    (stem suffix pairMarkers oddLabels : List Nat) (terminal : Nat)
    (markersSeen :
      forall marker, marker ∈ pairMarkers -> marker ∈ stem) :
    HullListDerives
      (stem ++ [terminal] ++ displayedMarkerPairs pairMarkers ++
        [terminal, terminal] ++ oddLabels ++ suffix)
      (stem ++ [terminal, terminal, terminal] ++ oddLabels ++ suffix) := by
  have transferred :=
    hullListDerivesTransferDisplayedPairsToTerminal
      stem ([terminal, terminal] ++ oddLabels ++ suffix)
      pairMarkers terminal markersSeen
  have contracted :=
    hullListDerivesContractTransferredTerminalPairs
      stem (oddLabels ++ suffix) pairMarkers terminal
  have transferredAligned : HullListDerives
      (stem ++ [terminal] ++ displayedMarkerPairs pairMarkers ++
        [terminal, terminal] ++ oddLabels ++ suffix)
      (stem ++ [terminal] ++ markerPairTail terminal pairMarkers ++
        [terminal, terminal] ++ oddLabels ++ suffix) := by
    simpa only [List.append_assoc] using transferred
  have contractedAligned : HullListDerives
      (stem ++ [terminal] ++ markerPairTail terminal pairMarkers ++
        [terminal, terminal] ++ oddLabels ++ suffix)
      (stem ++ [terminal, terminal, terminal] ++
        oddLabels ++ suffix) := by
    simpa only [List.append_assoc] using contracted
  exact transferredAligned.trans contractedAligned

/-- Final Condition-V cap: a terminal cube followed by nonempty witnessed
debt contracts to the terminal singleton required by the canonical last
block. -/
theorem hullListDerivesNormalizeTerminalCubeWithDebt
    (witnesses suffix debt : List Nat) (terminal : Nat)
    (debtNonempty : debt ≠ [])
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ witnesses) :
    HullListDerives
      (witnesses ++ [terminal, terminal, terminal] ++ debt ++ suffix)
      (witnesses ++ [terminal] ++ debt ++ suffix) :=
  hullListDerivesConditionVReturnRepair
    witnesses suffix debt terminal debtNonempty debtSeen

end Order6Hull23_1PhaseParityPowerNormalization
end CoRoots
end SemigroupBasis
