import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
import SemigroupBasis.CoRoots.S5_870GapBlocks

/-!
# Basis-independent block facts for the Hull 23.1 renderer

This file relates the `S5_831` phase scanner, the executable first-occurrence
gap parser, and the literal Lee--Zhang (23.3) renderer.  It deliberately has
no derivational import: every result below is a fact about lists, gap blocks,
phase bits, or the phase-parity key.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityBlockFacts

open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant

abbrev GapBlock := FirstOccurrenceGapBlock

/-! ## Parser/scanner agreement -/

/-- The scanner phase represented by one parsed first-occurrence block. -/
def phaseOfGapBlock (block : GapBlock) : Phase where
  label := block.marker
  doubled := decide (block.seconds ≠ [])

private theorem scanPhases_append
    (phases : List Phase) :
    forall left right : List Nat,
      scanPhases phases (left ++ right) =
        scanPhases (scanPhases phases left) right
  | [], right => rfl
  | letter :: rest, right => by
      simpa [scanPhases] using
        scanPhases_append (phaseStep phases letter) rest right

private theorem markLastDoubled_append_singleton
    (earlierPhases : List Phase) (phase : Phase) :
    markLastDoubled (earlierPhases ++ [phase]) =
      earlierPhases ++ [{ label := phase.label, doubled := true }] := by
  induction earlierPhases with
  | nil =>
      simp [markLastDoubled]
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [markLastDoubled]
      | cons next rest =>
          change
            head :: markLastDoubled (next :: (rest ++ [phase])) =
              head :: next ::
                (rest ++ [{ label := phase.label, doubled := true }])
          exact congrArg (List.cons head) induction

private theorem scanPhases_oldAfterDoubled
    (earlierPhases : List Phase) (marker : Nat) :
    forall gap : List Nat,
      (forall letter, letter ∈ gap ->
        letter ∈ marker :: phaseLabels earlierPhases) ->
      scanPhases
          (earlierPhases ++ [{ label := marker, doubled := true }]) gap =
        earlierPhases ++ [{ label := marker, doubled := true }]
  | [], _ => rfl
  | letter :: rest, known => by
      have letterOld :
          letter ∈ phaseLabels
            (earlierPhases ++ [{ label := marker, doubled := true }]) := by
        simpa [phaseLabels, or_comm] using
          known letter (by simp)
      have restKnown :
          forall tested, tested ∈ rest ->
            tested ∈ marker :: phaseLabels earlierPhases := by
        intro tested member
        exact known tested (List.Mem.tail letter member)
      have step :
          phaseStep
              (earlierPhases ++ [{ label := marker, doubled := true }])
              letter =
            earlierPhases ++ [{ label := marker, doubled := true }] := by
        simp [phaseStep, letterOld,
          markLastDoubled_append_singleton]
      rw [scanPhases, step]
      exact scanPhases_oldAfterDoubled
        earlierPhases marker rest restKnown

private theorem scanPhases_knownGap
    (earlierPhases : List Phase) (marker : Nat) :
    forall gap : List Nat,
      (forall letter, letter ∈ gap ->
        letter ∈ marker :: phaseLabels earlierPhases) ->
      scanPhases
          (earlierPhases ++ [{ label := marker, doubled := false }]) gap =
        earlierPhases ++
          [{ label := marker, doubled := decide (gap ≠ []) }]
  | [], _ => by
      simp [scanPhases]
  | letter :: rest, known => by
      have letterOld :
          letter ∈ phaseLabels
            (earlierPhases ++ [{ label := marker, doubled := false }]) := by
        simpa [phaseLabels, or_comm] using
          known letter (by simp)
      have restKnown :
          forall tested, tested ∈ rest ->
            tested ∈ marker :: phaseLabels earlierPhases := by
        intro tested member
        exact known tested (List.Mem.tail letter member)
      have step :
          phaseStep
              (earlierPhases ++ [{ label := marker, doubled := false }])
              letter =
            earlierPhases ++ [{ label := marker, doubled := true }] := by
        simp [phaseStep, letterOld,
          markLastDoubled_append_singleton]
      rw [scanPhases, step]
      simpa using
        scanPhases_oldAfterDoubled
          earlierPhases marker rest restKnown

private theorem scanPhases_renderGapBlocks
    {seen : List Nat} {phases : List Phase}
    {blocks : List GapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (prefixLabels : phaseLabels phases = seen.reverse) :
    scanPhases phases (renderGapBlocks blocks) =
      phases ++ blocks.map phaseOfGapBlock := by
  induction formed generalizing phases with
  | nil seen =>
      simp [renderGapBlocks, scanPhases]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      have markerFreshPhases :
          block.marker ∉ phaseLabels phases := by
        rw [prefixLabels]
        intro member
        apply markerFresh
        simpa using member
      have markerStep :
          phaseStep phases block.marker =
            phases ++ [{ label := block.marker, doubled := false }] := by
        simp [phaseStep, markerFreshPhases]
      have secondsKnown :
          forall letter, letter ∈ block.seconds ->
            letter ∈ block.marker :: phaseLabels phases := by
        intro letter member
        have old := secondsSeen letter member
        simpa [prefixLabels] using old
      have scannedGap :=
        scanPhases_knownGap phases block.marker
          block.seconds secondsKnown
      have nextLabels :
          phaseLabels (phases ++ [phaseOfGapBlock block]) =
            (block.marker :: seen).reverse := by
        simpa [phaseLabels, phaseOfGapBlock] using
          congrArg
            (fun labels => labels ++ [block.marker])
            prefixLabels
      have scannedRest :=
        induction
          (phases := phases ++ [phaseOfGapBlock block])
          nextLabels
      have scannedRest' :
          scanPhases
              (phases ++
                [⟨block.marker,
                  decide (block.seconds ≠ [])⟩])
              (renderGapBlocks rest) =
            phases ++
              [⟨block.marker,
                decide (block.seconds ≠ [])⟩] ++
              rest.map phaseOfGapBlock := by
        simpa only [phaseOfGapBlock] using scannedRest
      rw [renderGapBlocks, scanPhases, markerStep,
        scanPhases_append, scannedGap, scannedRest']
      by_cases secondsEmpty : block.seconds = []
      · simp [List.append_assoc, phaseOfGapBlock, secondsEmpty]
      · simp [List.append_assoc, phaseOfGapBlock, secondsEmpty]

private theorem scanPhases_nil_eq_phaseProfileList :
    forall letters : List Nat,
      scanPhases [] letters = phaseProfileList letters
  | [] => rfl
  | head :: tail => by
      simp [scanPhases, phaseStep, phaseLabels,
        phaseProfileList]

/-- The gap parser and the phase scanner have exactly the same markers and
doubled/nonempty bits. -/
theorem phaseGapProfileAgreement (letters : List Nat) :
    phaseProfileList letters =
      (gapBlocksList letters).map phaseOfGapBlock := by
  let blocks := gapBlocksList letters
  have formed : GapBlocksWellFormed [] blocks := by
    simpa [blocks] using gapBlocksList_wellFormed letters
  have rendered : renderGapBlocks blocks = letters := by
    simpa [blocks] using render_gapBlocksList letters
  have scanned :=
    scanPhases_renderGapBlocks
      (seen := []) (phases := []) (blocks := blocks)
      formed (by simp [phaseLabels])
  rw [rendered, scanPhases_nil_eq_phaseProfileList letters] at scanned
  simpa [blocks] using scanned

/-- In particular, the profile labels are literally the parsed marker order. -/
theorem phaseLabels_phaseProfileList_eq_gapBlockMarkers
    (letters : List Nat) :
    phaseLabels (phaseProfileList letters) =
      gapBlockMarkers (gapBlocksList letters) := by
  rw [phaseGapProfileAgreement]
  simp [phaseLabels, gapBlockMarkers, phaseOfGapBlock]

/-! ## The literal (23.3) list as gap blocks -/

def markerOnlyGapBlock (entry : PhaseParityEntry) : GapBlock where
  marker := entry.phase.label
  seconds := []

def markerOnlyGapBlocks
    (entries : List PhaseParityEntry) : List GapBlock :=
  entries.map markerOnlyGapBlock

/-- Block form of a doubled phase strictly before the last doubled phase. -/
def priorDoubledGapBlock (entry : PhaseParityEntry) : GapBlock where
  marker := entry.phase.label
  seconds :=
    if entry.parity % 2 = 0 then
      [entry.phase.label]
    else
      [entry.phase.label, entry.phase.label]

/-- Block form of the final doubled phase.  Its old-letter gap consists of
the remaining copies of its marker followed by the accumulated parity debt. -/
def lastDoubledGapBlock
    (debt : List Nat) (entry : PhaseParityEntry) : GapBlock where
  marker := entry.phase.label
  seconds :=
    if entry.parity % 2 = 0 then
      entry.phase.label :: debt
    else if debt = [] then
      [entry.phase.label, entry.phase.label]
    else
      debt

/-- Gap-block presentation of `renderLeeZhang23_3Aux`. -/
def canonicalGapBlocksAux
    (debt : List Nat) :
    List PhaseParityEntry -> List GapBlock
  | [] => []
  | entry :: rest =>
      if entry.phase.doubled then
        if hasDoubledPhase rest then
          priorDoubledGapBlock entry ::
            canonicalGapBlocksAux debt rest
        else
          lastDoubledGapBlock debt entry ::
            markerOnlyGapBlocks rest
      else if hasDoubledPhase rest then
        markerOnlyGapBlock entry ::
          canonicalGapBlocksAux
            (extendParityDebt debt entry) rest
      else
        markerOnlyGapBlocks (entry :: rest)

def canonicalGapBlocks
    (entries : List PhaseParityEntry) : List GapBlock :=
  canonicalGapBlocksAux [] entries

/-- A block strictly before the final doubled phase: doubled phases retain
their parity-selected power; undoubled phases retain only their marker. -/
def canonicalPriorGapBlock (entry : PhaseParityEntry) : GapBlock :=
  if entry.phase.doubled then
    priorDoubledGapBlock entry
  else
    markerOnlyGapBlock entry

def canonicalPriorGapBlocks
    (entries : List PhaseParityEntry) : List GapBlock :=
  entries.map canonicalPriorGapBlock

theorem render_markerOnlyGapBlocks :
    forall entries : List PhaseParityEntry,
      renderGapBlocks (markerOnlyGapBlocks entries) =
        renderPhaseMarkers entries
  | [] => rfl
  | entry :: rest => by
      change
        entry.phase.label ::
            renderGapBlocks (markerOnlyGapBlocks rest) =
          entry.phase.label :: renderPhaseMarkers rest
      exact congrArg (List.cons entry.phase.label)
        (render_markerOnlyGapBlocks rest)

theorem markers_markerOnlyGapBlocks
    (entries : List PhaseParityEntry) :
    gapBlockMarkers (markerOnlyGapBlocks entries) =
      entries.map (fun entry => entry.phase.label) := by
  simp [markerOnlyGapBlocks, markerOnlyGapBlock, gapBlockMarkers]

theorem render_canonicalGapBlocksAux
    (debt : List Nat) :
    forall entries : List PhaseParityEntry,
      renderGapBlocks (canonicalGapBlocksAux debt entries) =
        renderLeeZhang23_3Aux debt entries
  | [] => rfl
  | entry :: rest => by
      cases doubled : entry.phase.doubled <;>
        cases later : hasDoubledPhase rest <;>
          by_cases even : entry.parity % 2 = 0 <;>
            by_cases empty : debt = [] <;>
              simp [canonicalGapBlocksAux, renderLeeZhang23_3Aux,
                doubled, later, even, empty,
                priorDoubledGapBlock, lastDoubledGapBlock,
                markerOnlyGapBlock, renderGapBlocks,
                render_markerOnlyGapBlocks,
                renderPriorDoubledPower, renderLastDoubledPower,
                extendParityDebt, render_canonicalGapBlocksAux,
                List.append_assoc]

theorem render_canonicalGapBlocks
    (entries : List PhaseParityEntry) :
    renderGapBlocks (canonicalGapBlocks entries) =
      renderPhaseParityEntries entries := by
  exact render_canonicalGapBlocksAux [] entries

theorem markers_canonicalGapBlocksAux
    (debt : List Nat) :
    forall entries : List PhaseParityEntry,
      gapBlockMarkers (canonicalGapBlocksAux debt entries) =
        entries.map (fun entry => entry.phase.label)
  | [] => rfl
  | entry :: rest => by
      cases doubled : entry.phase.doubled with
      | false =>
          cases later : hasDoubledPhase rest with
          | false =>
              simpa [canonicalGapBlocksAux, doubled, later] using
                markers_markerOnlyGapBlocks (entry :: rest)
          | true =>
              simpa [canonicalGapBlocksAux, doubled, later,
                gapBlockMarkers, markerOnlyGapBlock] using
                congrArg (List.cons entry.phase.label)
                  (markers_canonicalGapBlocksAux
                    (extendParityDebt debt entry) rest)
      | true =>
          cases later : hasDoubledPhase rest with
          | false =>
              simpa [canonicalGapBlocksAux, doubled, later,
                gapBlockMarkers, lastDoubledGapBlock] using
                congrArg (List.cons entry.phase.label)
                  (markers_markerOnlyGapBlocks rest)
          | true =>
              simpa [canonicalGapBlocksAux, doubled, later,
                gapBlockMarkers, priorDoubledGapBlock] using
                congrArg (List.cons entry.phase.label)
                  (markers_canonicalGapBlocksAux debt rest)

theorem markers_canonicalGapBlocks
    (entries : List PhaseParityEntry) :
    gapBlockMarkers (canonicalGapBlocks entries) =
      entries.map (fun entry => entry.phase.label) :=
  markers_canonicalGapBlocksAux [] entries

theorem priorDoubledGapBlock_seconds_ne_nil
    (entry : PhaseParityEntry) :
    (priorDoubledGapBlock entry).seconds ≠ [] := by
  by_cases even : entry.parity % 2 = 0
  · simp [priorDoubledGapBlock, even]
  · simp [priorDoubledGapBlock, even]

theorem lastDoubledGapBlock_seconds_ne_nil
    (debt : List Nat) (entry : PhaseParityEntry) :
    (lastDoubledGapBlock debt entry).seconds ≠ [] := by
  by_cases even : entry.parity % 2 = 0
  · simp [lastDoubledGapBlock, even]
  · by_cases empty : debt = []
    · simp [lastDoubledGapBlock, even, empty]
    · simp [lastDoubledGapBlock, even, empty]

/-! ## Last doubled phase / last nonempty block -/

theorem hasDoubledPhase_eq_false_iff :
    forall entries : List PhaseParityEntry,
      hasDoubledPhase entries = false ↔
        forall entry, entry ∈ entries ->
          entry.phase.doubled = false
  | [] => by simp [hasDoubledPhase]
  | entry :: rest => by
      simp [hasDoubledPhase,
        hasDoubledPhase_eq_false_iff rest]

theorem hasDoubledPhase_eq_true_of_mem
    {entries : List PhaseParityEntry} {selected : PhaseParityEntry}
    (member : selected ∈ entries)
    (doubled : selected.phase.doubled = true) :
    hasDoubledPhase entries = true := by
  cases result : hasDoubledPhase entries with
  | false =>
      have allUndoubled :=
        (hasDoubledPhase_eq_false_iff entries).mp result
      have selectedUndoubled := allUndoubled selected member
      rw [doubled] at selectedUndoubled
      contradiction
  | true =>
      rfl

/-- When the two input streams are aligned, `phaseParityEntries` preserves
the phase stream literally. -/
theorem phases_phaseParityEntries_of_length :
    forall (phases : List Phase) (parities : List Nat),
      parities.length = phases.length ->
        (phaseParityEntries phases parities).map
            (fun entry => entry.phase) =
          phases
  | [], parities, _ => rfl
  | phase :: rest, [], lengths => by
      simp at lengths
  | phase :: rest, parity :: parities, lengths => by
      simp only [phaseParityEntries, List.map_cons,
        PhaseParityEntry.phase]
      have tailLengths : parities.length = rest.length := by
        simpa using lengths
      exact congrArg (List.cons phase)
        (phases_phaseParityEntries_of_length
          rest parities tailLengths)

theorem phases_phaseParityEntries_word (word : Word Nat) :
    (phaseParityEntries
        (phaseProfile word) (phaseParityCoordinates word)).map
        (fun entry => entry.phase) =
      phaseProfile word := by
  apply phases_phaseParityEntries_of_length
  exact phaseParityCoordinates_length word

theorem markerOnlyGapBlocks_seconds_empty
    {entries : List PhaseParityEntry} {block : GapBlock}
    (member : block ∈ markerOnlyGapBlocks entries) :
    block.seconds = [] := by
  rcases List.mem_map.mp member with
    ⟨entry, _, rfl⟩
  rfl

/-- Whether an ordinary phase stream contains a doubled phase.  This is the
phase-only analogue of `hasDoubledPhase`, whose input carries parity data. -/
def phaseListHasDoubled : List Phase -> Bool
  | [] => false
  | phase :: rest => phase.doubled || phaseListHasDoubled rest

/-- A phase stream obtained from gap blocks contains a doubled phase exactly
when one of the blocks has a nonempty old-letter gap. -/
theorem hasDoubledPhase_map_phaseOfGapBlock_eq_true_iff :
    forall blocks : List GapBlock,
      phaseListHasDoubled (blocks.map phaseOfGapBlock) = true ↔
        exists block, block ∈ blocks ∧ block.seconds ≠ []
  | [] => by simp [phaseListHasDoubled]
  | block :: rest => by
      by_cases empty : block.seconds = []
      · simp [phaseListHasDoubled, phaseOfGapBlock, empty,
          hasDoubledPhase_map_phaseOfGapBlock_eq_true_iff rest]
      · simp [phaseListHasDoubled, phaseOfGapBlock, empty]

theorem canonicalGapBlocksAux_has_nonempty_of_hasDoubled
    (debt : List Nat) :
    forall entries : List PhaseParityEntry,
      hasDoubledPhase entries = true ->
        exists block,
          block ∈ canonicalGapBlocksAux debt entries ∧
            block.seconds ≠ []
  | [], doubled => by
      simp [hasDoubledPhase] at doubled
  | entry :: rest, doubled => by
      cases entryDoubled : entry.phase.doubled with
      | false =>
        have laterDoubled : hasDoubledPhase rest = true := by
          simpa [hasDoubledPhase, entryDoubled] using doubled
        obtain ⟨block, member, nonempty⟩ :=
          canonicalGapBlocksAux_has_nonempty_of_hasDoubled
            (extendParityDebt debt entry) rest laterDoubled
        refine ⟨block, ?_, nonempty⟩
        simp [canonicalGapBlocksAux, entryDoubled,
          laterDoubled, member]
      | true =>
        cases laterDoubled : hasDoubledPhase rest with
        | false =>
          exact
            ⟨lastDoubledGapBlock debt entry,
              by simp [canonicalGapBlocksAux, entryDoubled,
                laterDoubled],
              lastDoubledGapBlock_seconds_ne_nil debt entry⟩
        | true =>
          exact
            ⟨priorDoubledGapBlock entry,
              by simp [canonicalGapBlocksAux, entryDoubled,
                laterDoubled],
              priorDoubledGapBlock_seconds_ne_nil entry⟩

/-- Any finite block list containing a nonempty gap has a final such block;
the suffix after it consists entirely of empty gaps. -/
theorem exists_last_nonempty_gap_split
    {blocks : List GapBlock}
    (nonemptyGap :
      exists block, block ∈ blocks ∧ block.seconds ≠ []) :
    exists before lastBlock after,
      blocks = before ++ lastBlock :: after ∧
      lastBlock.seconds ≠ [] ∧
      (forall block, block ∈ after -> block.seconds = []) := by
  induction blocks with
  | nil =>
      rcases nonemptyGap with ⟨block, member, _⟩
      simp at member
  | cons block rest induction =>
      by_cases restHas :
          exists later, later ∈ rest ∧ later.seconds ≠ []
      · obtain ⟨before, lastBlock, after,
          shape, lastNonempty, trailingEmpty⟩ :=
          induction restHas
        refine
          ⟨block :: before, lastBlock, after, ?_,
            lastNonempty, trailingEmpty⟩
        simp [shape]
      · have blockNonempty : block.seconds ≠ [] := by
          rcases nonemptyGap with ⟨selected, member, selectedNonempty⟩
          rcases List.mem_cons.mp member with atHead | inRest
          · simpa [atHead] using selectedNonempty
          · exact False.elim <| restHas
              ⟨selected, inRest, selectedNonempty⟩
        refine ⟨[], block, rest, by simp, blockNonempty, ?_⟩
        intro selected member
        by_cases selectedEmpty : selected.seconds = []
        · exact selectedEmpty
        · exact False.elim <| restHas
            ⟨selected, member, selectedEmpty⟩

/-- The last doubled phase of a source list is the last parsed block with a
nonempty gap; all later first-occurrence blocks have empty gaps. -/
theorem phaseProfileList_last_nonempty_gap_split
    {letters : List Nat}
    (doubled : phaseListHasDoubled (phaseProfileList letters) = true) :
    exists before lastBlock after,
      gapBlocksList letters = before ++ lastBlock :: after ∧
      lastBlock.seconds ≠ [] ∧
      (forall block, block ∈ after -> block.seconds = []) := by
  apply exists_last_nonempty_gap_split
  apply (hasDoubledPhase_map_phaseOfGapBlock_eq_true_iff
    (gapBlocksList letters)).mp
  rw [← phaseGapProfileAgreement]
  exact doubled

/-- In the canonical block presentation, a doubled phase therefore determines
a last nonempty block, and every block after it has an empty seconds field. -/
theorem canonicalGapBlocksAux_last_nonempty
    (debt : List Nat) {entries : List PhaseParityEntry}
    (doubled : hasDoubledPhase entries = true) :
    exists before lastBlock after,
      canonicalGapBlocksAux debt entries =
        before ++ lastBlock :: after ∧
      lastBlock.seconds ≠ [] ∧
      (forall block, block ∈ after -> block.seconds = []) :=
  exists_last_nonempty_gap_split
    (canonicalGapBlocksAux_has_nonempty_of_hasDoubled
      debt entries doubled)

/-! ## Parity debt -/

/-- One debt copy is retained exactly for an undoubled marker whose requested
total multiplicity is even. -/
def parityDebtContribution (entry : PhaseParityEntry) : List Nat :=
  if entry.phase.doubled then
    []
  else if entry.parity % 2 = 0 then
    [entry.phase.label]
  else
    []

def collectParityDebt : List PhaseParityEntry -> List Nat
  | [] => []
  | entry :: rest =>
      parityDebtContribution entry ++ collectParityDebt rest

theorem parityDebtContribution_of_undoubled
    (entry : PhaseParityEntry)
    (undoubled : entry.phase.doubled = false) :
    parityDebtContribution entry =
      if entry.parity % 2 = 0 then [entry.phase.label] else [] := by
  simp [parityDebtContribution, undoubled]

theorem extendParityDebt_eq_append_contribution
    (debt : List Nat) (entry : PhaseParityEntry)
    (undoubled : entry.phase.doubled = false) :
    extendParityDebt debt entry =
      debt ++ parityDebtContribution entry := by
  by_cases even : entry.parity % 2 = 0
  · simp [extendParityDebt, parityDebtContribution,
      undoubled, even]
  · simp [extendParityDebt, parityDebtContribution,
      undoubled, even]

theorem mem_collectParityDebt_iff
    (letter : Nat) :
    forall entries : List PhaseParityEntry,
      letter ∈ collectParityDebt entries ↔
        exists entry,
          entry ∈ entries ∧
          entry.phase.doubled = false ∧
          entry.parity % 2 = 0 ∧
          letter = entry.phase.label
  | [] => by simp [collectParityDebt]
  | entry :: rest => by
      by_cases phaseDoubled : entry.phase.doubled
      · simp [collectParityDebt, parityDebtContribution,
          phaseDoubled, mem_collectParityDebt_iff letter rest]
      · by_cases even : entry.parity % 2 = 0
        · simp [collectParityDebt, parityDebtContribution,
            phaseDoubled, even,
            mem_collectParityDebt_iff letter rest]
        · simp [collectParityDebt, parityDebtContribution,
            phaseDoubled, even,
            mem_collectParityDebt_iff letter rest]

/-- Exact preceding/final/trailing block shape of the literal renderer.
The debt presented to the last doubled block is the incoming debt followed,
in marker order, by exactly the even undoubled markers in `before`. -/
theorem canonicalGapBlocksAux_lastDoubled_shape
    (last : PhaseParityEntry) (after : List PhaseParityEntry)
    (lastDoubled : last.phase.doubled = true)
    (afterUndoubled :
      forall entry, entry ∈ after -> entry.phase.doubled = false) :
    forall (debt : List Nat) (before : List PhaseParityEntry),
      canonicalGapBlocksAux debt (before ++ last :: after) =
        canonicalPriorGapBlocks before ++
          lastDoubledGapBlock
              (debt ++ collectParityDebt before) last ::
            markerOnlyGapBlocks after
  | debt, [] => by
      have noLater : hasDoubledPhase after = false :=
        (hasDoubledPhase_eq_false_iff after).mpr afterUndoubled
      simp [canonicalGapBlocksAux, canonicalPriorGapBlocks,
        collectParityDebt, lastDoubled, noLater]
  | debt, entry :: rest => by
      have laterDoubled :
          hasDoubledPhase (rest ++ last :: after) = true :=
        hasDoubledPhase_eq_true_of_mem
          (entries := rest ++ last :: after) (selected := last)
          (by simp) lastDoubled
      cases entryDoubled : entry.phase.doubled with
      | false =>
        have extended :=
          extendParityDebt_eq_append_contribution
            debt entry entryDoubled
        rw [show
          (entry :: rest) ++ last :: after =
            entry :: (rest ++ last :: after) by rfl]
        simp only [canonicalGapBlocksAux, entryDoubled,
          laterDoubled]
        rw [canonicalGapBlocksAux_lastDoubled_shape
          last after lastDoubled afterUndoubled
          (extendParityDebt debt entry) rest]
        simp [canonicalPriorGapBlocks, canonicalPriorGapBlock,
          collectParityDebt, entryDoubled, extended,
          List.append_assoc]
      | true =>
        rw [show
          (entry :: rest) ++ last :: after =
            entry :: (rest ++ last :: after) by rfl]
        simp only [canonicalGapBlocksAux, entryDoubled,
          laterDoubled]
        rw [canonicalGapBlocksAux_lastDoubled_shape
          last after lastDoubled afterUndoubled debt rest]
        simp [canonicalPriorGapBlocks, canonicalPriorGapBlock,
          collectParityDebt, parityDebtContribution,
          entryDoubled, List.append_assoc]

theorem canonicalGapBlocks_lastDoubled_shape
    (before : List PhaseParityEntry) (last : PhaseParityEntry)
    (after : List PhaseParityEntry)
    (lastDoubled : last.phase.doubled = true)
    (afterUndoubled :
      forall entry, entry ∈ after -> entry.phase.doubled = false) :
    canonicalGapBlocks (before ++ last :: after) =
      canonicalPriorGapBlocks before ++
        lastDoubledGapBlock (collectParityDebt before) last ::
          markerOnlyGapBlocks after := by
  simpa [canonicalGapBlocks] using
    canonicalGapBlocksAux_lastDoubled_shape
      last after lastDoubled afterUndoubled [] before

/-! ## Key-level canonical shape -/

def phaseParityKeyGapBlocks (key : PhaseParityKey) : List GapBlock :=
  canonicalGapBlocks (phaseParityEntries key.phases key.parities)

def canonicalPhaseParityGapBlocks (word : Word Nat) : List GapBlock :=
  phaseParityKeyGapBlocks (phaseParityKey word)

theorem render_phaseParityKeyGapBlocks (key : PhaseParityKey) :
    renderGapBlocks (phaseParityKeyGapBlocks key) =
      renderPhaseParityKeyList key := by
  exact render_canonicalGapBlocks
    (phaseParityEntries key.phases key.parities)

theorem render_canonicalPhaseParityGapBlocks (word : Word Nat) :
    renderGapBlocks (canonicalPhaseParityGapBlocks word) =
      canonicalPhaseParityList word := by
  exact render_phaseParityKeyGapBlocks (phaseParityKey word)

theorem canonicalPhaseParityWord_toList_blocks (word : Word Nat) :
    (canonicalPhaseParityWord word).toList =
      renderGapBlocks (canonicalPhaseParityGapBlocks word) := by
  rw [toList_canonicalPhaseParityWord,
    render_canonicalPhaseParityGapBlocks]

theorem markers_phaseParityKeyGapBlocks (key : PhaseParityKey) :
    gapBlockMarkers (phaseParityKeyGapBlocks key) =
      (phaseParityEntries key.phases key.parities).map
        (fun entry => entry.phase.label) :=
  markers_canonicalGapBlocks _

/-- For a key coming from a word, the canonical block markers are exactly the
source phase labels, hence exactly the source first-occurrence order. -/
theorem markers_canonicalPhaseParityGapBlocks (word : Word Nat) :
    gapBlockMarkers (canonicalPhaseParityGapBlocks word) =
      phaseLabels (phaseProfile word) := by
  change
    gapBlockMarkers (phaseParityKeyGapBlocks (phaseParityKey word)) =
      phaseLabels (phaseProfile word)
  rw [markers_phaseParityKeyGapBlocks]
  change
    (phaseParityEntries
        (phaseProfile word) (phaseParityCoordinates word)).map
        (fun entry => entry.phase.label) =
      phaseLabels (phaseProfile word)
  have aligned := congrArg (List.map Phase.label)
    (phases_phaseParityEntries_word word)
  simpa [phaseLabels, List.map_map] using aligned

end Order6Hull23_1PhaseParityBlockFacts
end CoRoots
end SemigroupBasis
