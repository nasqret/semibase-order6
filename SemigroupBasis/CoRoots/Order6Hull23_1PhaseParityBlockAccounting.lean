import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
import SemigroupBasis.CoRoots.S5_870GapBlocks

/-!
# Basis-independent accounting for the Hull 23.1 phase-parity blocks

This module supplies the structural bookkeeping used by the constructive
Hull 23.1 normalizer.  It proves that the literal Lee--Zhang (23.3) block
renderer is a well-formed first-occurrence decomposition, aligns source block
splits with the corresponding phase/parity-entry splits, and records exact
support and parity-debt multiplicities.  No identity basis or derivability
relation is imported here.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityBlockAccounting

open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts

abbrev GapBlock := FirstOccurrenceGapBlock

def entryLabels (entries : List PhaseParityEntry) : List Nat :=
  entries.map (fun entry => entry.phase.label)

theorem renderPhaseMarkers_eq_entryLabels :
    forall entries : List PhaseParityEntry,
      renderPhaseMarkers entries = entryLabels entries
  | [] => rfl
  | entry :: rest => by
      simp [renderPhaseMarkers, entryLabels,
        renderPhaseMarkers_eq_entryLabels rest]

/-! ## Elementary append and support facts -/

theorem renderGapBlocks_append
    (left right : List GapBlock) :
    renderGapBlocks (left ++ right) =
      renderGapBlocks left ++ renderGapBlocks right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [renderGapBlocks, induction, List.append_assoc]

theorem gapBlockMarkers_append
    (left right : List GapBlock) :
    gapBlockMarkers (left ++ right) =
      gapBlockMarkers left ++ gapBlockMarkers right :=
  List.map_append

theorem gapBlockSeconds_append
    (left right : List GapBlock) :
    gapBlockSeconds (left ++ right) =
      gapBlockSeconds left ++ gapBlockSeconds right :=
  List.flatMap_append

theorem mem_renderGapBlocks_iff
    (letter : Nat) :
    forall blocks : List GapBlock,
      letter ∈ renderGapBlocks blocks ↔
        letter ∈ gapBlockMarkers blocks ∨
          letter ∈ gapBlockSeconds blocks
  | [] => by
      simp [renderGapBlocks, gapBlockMarkers, gapBlockSeconds]
  | block :: rest => by
      simp [renderGapBlocks, gapBlockMarkers, gapBlockSeconds,
        mem_renderGapBlocks_iff letter rest,
        or_assoc, or_left_comm, or_comm]

theorem not_mem_renderGapBlocks_of_not_mem_markers
    {blocks : List GapBlock} (formed : GapBlocksWellFormed [] blocks)
    {letter : Nat} (absent : letter ∉ gapBlockMarkers blocks) :
    letter ∉ renderGapBlocks blocks := by
  intro member
  rw [mem_renderGapBlocks_iff] at member
  rcases member with inMarkers | inSeconds
  · exact absent inMarkers
  · have inMarkers :=
      (formed.secondsInSeenOrMarkers letter inSeconds).resolve_left
        (by simp)
    exact absent inMarkers

theorem gapBlockSeconds_eq_nil_of_seconds_empty
    (blocks : List GapBlock)
    (empty : forall block, block ∈ blocks -> block.seconds = []) :
    gapBlockSeconds blocks = [] := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      have headEmpty := empty block (List.Mem.head rest)
      have restEmpty :
          forall selected, selected ∈ rest ->
            selected.seconds = [] := by
        intro selected member
        exact empty selected (List.Mem.tail block member)
      change block.seconds ++ gapBlockSeconds rest = []
      rw [headEmpty]
      exact induction restEmpty

theorem renderGapBlocks_eq_markers_of_seconds_empty
    (blocks : List GapBlock)
    (empty : forall block, block ∈ blocks -> block.seconds = []) :
    renderGapBlocks blocks = gapBlockMarkers blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest induction =>
      have headEmpty := empty block (List.Mem.head rest)
      have restEmpty :
          forall selected, selected ∈ rest ->
            selected.seconds = [] := by
        intro selected member
        exact empty selected (List.Mem.tail block member)
      simp [renderGapBlocks, gapBlockMarkers, headEmpty,
        induction restEmpty]

/-- In a well-formed decomposition, a marker cannot occur in a seconds field
strictly before the block that first introduces that marker. -/
theorem futureMarker_not_mem_gapBlockSeconds :
    forall {seen : List Nat} {before : List GapBlock}
      {block : GapBlock} {after : List GapBlock},
      GapBlocksWellFormed seen (before ++ block :: after) ->
        block.marker ∉ gapBlockSeconds before
  | seen, [], block, after, _ => by
      simp [gapBlockSeconds]
  | seen, head :: rest, block, after, formed => by
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          intro member
          simp only [gapBlockSeconds, List.flatMap_cons,
            List.mem_append] at member
          rcases member with inHead | inRest
          · have alreadySeen := secondsSeen block.marker inHead
            have markerLater :
                block.marker ∈
                  gapBlockMarkers (rest ++ block :: after) := by
              simp [gapBlockMarkers]
            exact
              (tailFormed.markersAvoidSeen
                block.marker alreadySeen) markerLater
          · exact futureMarker_not_mem_gapBlockSeconds
              tailFormed inRest

/-- If the selected block and every later block have empty seconds fields,
its marker occurs exactly once in the rendered well-formed decomposition. -/
theorem count_renderGapBlocks_marker_eq_one_of_trailing_empty
    {blocks before after : List GapBlock} {block : GapBlock}
    (formed : GapBlocksWellFormed [] blocks)
    (split : blocks = before ++ block :: after)
    (trailingEmpty :
      forall selected, selected ∈ block :: after ->
        selected.seconds = []) :
    (renderGapBlocks blocks).count block.marker = 1 := by
  have priorAbsent : block.marker ∉ gapBlockSeconds before := by
    apply futureMarker_not_mem_gapBlockSeconds
    simpa [split] using formed
  have currentEmpty : block.seconds = [] :=
    trailingEmpty block (List.Mem.head after)
  have afterEmpty :
      forall selected, selected ∈ after -> selected.seconds = [] := by
    intro selected member
    exact trailingEmpty selected (List.Mem.tail block member)
  have afterSecondsEmpty : gapBlockSeconds after = [] :=
    gapBlockSeconds_eq_nil_of_seconds_empty after afterEmpty
  have secondsAbsent : block.marker ∉ gapBlockSeconds blocks := by
    intro member
    rw [split, gapBlockSeconds_append] at member
    rcases List.mem_append.mp member with inBefore | inTail
    · exact priorAbsent inBefore
    · simp only [gapBlockSeconds, List.flatMap_cons,
        List.mem_append] at inTail
      rcases inTail with inCurrent | inAfterSeconds
      · rw [currentEmpty] at inCurrent
        simp at inCurrent
      · have impossible :
            block.marker ∈ gapBlockSeconds after := inAfterSeconds
        rw [afterSecondsEmpty] at impossible
        simp at impossible
  have markerMember : block.marker ∈ gapBlockMarkers blocks := by
    rw [split, gapBlockMarkers_append]
    simp [gapBlockMarkers]
  have markerCount :
      (gapBlockMarkers blocks).count block.marker = 1 := by
    rw [formed.markersNodup.count]
    simp [markerMember]
  have secondsCount :
      (gapBlockSeconds blocks).count block.marker = 0 :=
    List.count_eq_zero.mpr secondsAbsent
  rw [count_renderGapBlocks, markerCount, secondsCount]

theorem mem_priorDoubledGapBlock_seconds_iff
    (letter : Nat) (entry : PhaseParityEntry) :
    letter ∈ (priorDoubledGapBlock entry).seconds ↔
      letter = entry.phase.label := by
  by_cases even : entry.parity % 2 = 0
  · simp [priorDoubledGapBlock, even]
  · simp [priorDoubledGapBlock, even]

theorem mem_lastDoubledGapBlock_seconds
    {letter : Nat} {debt : List Nat} {entry : PhaseParityEntry}
    (member : letter ∈ (lastDoubledGapBlock debt entry).seconds) :
    letter = entry.phase.label ∨ letter ∈ debt := by
  by_cases even : entry.parity % 2 = 0
  · simpa [lastDoubledGapBlock, even] using member
  · by_cases empty : debt = []
    · simpa [lastDoubledGapBlock, even, empty] using member
    · exact Or.inr <| by
        simpa [lastDoubledGapBlock, even, empty] using member

theorem mem_render_canonicalPriorGapBlocks_iff
    (letter : Nat) :
    forall entries : List PhaseParityEntry,
      letter ∈ renderGapBlocks (canonicalPriorGapBlocks entries) ↔
        exists entry, entry ∈ entries ∧
          letter = entry.phase.label
  | [] => by
      simp [canonicalPriorGapBlocks, renderGapBlocks]
  | entry :: rest => by
      rw [show canonicalPriorGapBlocks (entry :: rest) =
            [canonicalPriorGapBlock entry] ++
              canonicalPriorGapBlocks rest by rfl,
          renderGapBlocks_append, List.mem_append,
          mem_render_canonicalPriorGapBlocks_iff letter rest]
      cases doubled : entry.phase.doubled <;>
        by_cases even : entry.parity % 2 = 0 <;>
          simp [canonicalPriorGapBlock,
            priorDoubledGapBlock, markerOnlyGapBlock,
            renderGapBlocks, doubled, even, or_assoc]

theorem mem_render_markerOnlyGapBlocks_iff
    (letter : Nat) :
    forall entries : List PhaseParityEntry,
      letter ∈ renderGapBlocks (markerOnlyGapBlocks entries) ↔
        exists entry, entry ∈ entries ∧
          letter = entry.phase.label
  | [] => by
      simp [markerOnlyGapBlocks, renderGapBlocks]
  | entry :: rest => by
      rw [show markerOnlyGapBlocks (entry :: rest) =
            [markerOnlyGapBlock entry] ++ markerOnlyGapBlocks rest by rfl,
          renderGapBlocks_append, List.mem_append,
          mem_render_markerOnlyGapBlocks_iff letter rest]
      simp [markerOnlyGapBlock, renderGapBlocks, or_assoc]

/-! ## Well-formedness of the canonical blocks -/

theorem markerOnlyGapBlocks_wellFormed :
    forall (seen : List Nat) (entries : List PhaseParityEntry),
      (entryLabels entries).Nodup ->
      (forall entry, entry ∈ entries ->
        entry.phase.label ∉ seen) ->
      GapBlocksWellFormed seen (markerOnlyGapBlocks entries)
  | seen, [], _, _ => by
      simpa [markerOnlyGapBlocks] using
        GapBlocksWellFormed.nil seen
  | seen, entry :: rest, labelsNodup, labelsFresh => by
      have labelData :
          entry.phase.label ∉ entryLabels rest ∧
            (entryLabels rest).Nodup := by
        simpa [entryLabels] using
          (List.nodup_cons.mp labelsNodup)
      have markerFresh : entry.phase.label ∉ seen :=
        labelsFresh entry (List.Mem.head rest)
      have tailFresh :
          forall later, later ∈ rest ->
            later.phase.label ∉ entry.phase.label :: seen := by
        intro later laterMember laterSeen
        rcases List.mem_cons.mp laterSeen with atMarker | inSeen
        · apply labelData.1
          rw [← atMarker]
          exact List.mem_map.mpr ⟨later, laterMember, rfl⟩
        · exact labelsFresh later
            (List.Mem.tail entry laterMember) inSeen
      apply GapBlocksWellFormed.cons seen
        (markerOnlyGapBlock entry) (markerOnlyGapBlocks rest)
      · simpa [markerOnlyGapBlock] using markerFresh
      · intro letter member
        simp [markerOnlyGapBlock] at member
      · exact markerOnlyGapBlocks_wellFormed
          (entry.phase.label :: seen) rest labelData.2 tailFresh

theorem canonicalGapBlocksAux_wellFormed :
    forall (seen debt : List Nat)
      (entries : List PhaseParityEntry),
      (entryLabels entries).Nodup ->
      (forall entry, entry ∈ entries ->
        entry.phase.label ∉ seen) ->
      (forall letter, letter ∈ debt -> letter ∈ seen) ->
      GapBlocksWellFormed seen
        (canonicalGapBlocksAux debt entries)
  | seen, debt, [], _, _, _ => by
      simpa [canonicalGapBlocksAux] using
        GapBlocksWellFormed.nil seen
  | seen, debt, entry :: rest, labelsNodup, labelsFresh, debtSeen => by
      have labelData :
          entry.phase.label ∉ entryLabels rest ∧
            (entryLabels rest).Nodup := by
        simpa [entryLabels] using
          (List.nodup_cons.mp labelsNodup)
      have markerFresh : entry.phase.label ∉ seen :=
        labelsFresh entry (List.Mem.head rest)
      have tailFresh :
          forall later, later ∈ rest ->
            later.phase.label ∉ entry.phase.label :: seen := by
        intro later laterMember laterSeen
        rcases List.mem_cons.mp laterSeen with atMarker | inSeen
        · apply labelData.1
          rw [← atMarker]
          exact List.mem_map.mpr ⟨later, laterMember, rfl⟩
        · exact labelsFresh later
            (List.Mem.tail entry laterMember) inSeen
      cases entryDoubled : entry.phase.doubled with
      | false =>
          cases laterDoubled : hasDoubledPhase rest with
          | false =>
              simpa [canonicalGapBlocksAux, entryDoubled,
                laterDoubled] using
                markerOnlyGapBlocks_wellFormed
                  seen (entry :: rest) labelsNodup labelsFresh
          | true =>
              have extendedDebtSeen :
                  forall letter,
                    letter ∈ extendParityDebt debt entry ->
                      letter ∈ entry.phase.label :: seen := by
                intro letter member
                by_cases even : entry.parity % 2 = 0
                · rw [extendParityDebt, if_pos even] at member
                  rcases List.mem_append.mp member with old | atMarker
                  · exact List.Mem.tail entry.phase.label
                      (debtSeen letter old)
                  · have equal : letter = entry.phase.label := by
                      simpa using atMarker
                    subst letter
                    exact List.Mem.head seen
                · rw [extendParityDebt, if_neg even] at member
                  exact List.Mem.tail entry.phase.label
                    (debtSeen letter member)
              have tailFormed :=
                canonicalGapBlocksAux_wellFormed
                  (entry.phase.label :: seen)
                  (extendParityDebt debt entry) rest
                  labelData.2 tailFresh extendedDebtSeen
              rw [canonicalGapBlocksAux, entryDoubled,
                laterDoubled]
              apply GapBlocksWellFormed.cons seen
                (markerOnlyGapBlock entry)
                (canonicalGapBlocksAux
                  (extendParityDebt debt entry) rest)
              · simpa [markerOnlyGapBlock] using markerFresh
              · intro letter member
                simp [markerOnlyGapBlock] at member
              · exact tailFormed
      | true =>
          cases laterDoubled : hasDoubledPhase rest with
          | false =>
              have tailFormed :=
                markerOnlyGapBlocks_wellFormed
                  (entry.phase.label :: seen) rest
                  labelData.2 tailFresh
              rw [canonicalGapBlocksAux, entryDoubled,
                laterDoubled]
              apply GapBlocksWellFormed.cons seen
                (lastDoubledGapBlock debt entry)
                (markerOnlyGapBlocks rest)
              · simpa [lastDoubledGapBlock] using markerFresh
              · intro letter member
                rcases mem_lastDoubledGapBlock_seconds member with
                  atMarker | inDebt
                · subst letter
                  simpa [lastDoubledGapBlock] using
                    (List.Mem.head seen :
                      entry.phase.label ∈ entry.phase.label :: seen)
                · exact List.Mem.tail entry.phase.label
                    (debtSeen letter inDebt)
              · exact tailFormed
          | true =>
              have tailDebtSeen :
                  forall letter, letter ∈ debt ->
                    letter ∈ entry.phase.label :: seen := by
                intro letter member
                exact List.Mem.tail entry.phase.label
                  (debtSeen letter member)
              have tailFormed :=
                canonicalGapBlocksAux_wellFormed
                  (entry.phase.label :: seen) debt rest
                  labelData.2 tailFresh tailDebtSeen
              rw [canonicalGapBlocksAux, entryDoubled,
                laterDoubled]
              apply GapBlocksWellFormed.cons seen
                (priorDoubledGapBlock entry)
                (canonicalGapBlocksAux debt rest)
              · simpa [priorDoubledGapBlock] using markerFresh
              · intro letter member
                have equal :=
                  (mem_priorDoubledGapBlock_seconds_iff
                    letter entry).mp member
                subst letter
                simpa [priorDoubledGapBlock] using
                  (List.Mem.head seen :
                    entry.phase.label ∈ entry.phase.label :: seen)
              · exact tailFormed

theorem canonicalGapBlocks_wellFormed
    (entries : List PhaseParityEntry)
    (labelsNodup : (entryLabels entries).Nodup) :
    GapBlocksWellFormed [] (canonicalGapBlocks entries) := by
  apply canonicalGapBlocksAux_wellFormed [] [] entries labelsNodup
  · intro entry member
    simp
  · intro letter member
    simp at member

theorem entryLabels_phaseParityEntries_word
    (word : Word Nat) :
    entryLabels
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) =
      phaseLabels (phaseProfile word) := by
  have aligned := congrArg (List.map Phase.label)
    (phases_phaseParityEntries_word word)
  simpa [entryLabels, phaseLabels, List.map_map] using aligned

theorem entryLabels_phaseParityEntries_word_nodup
    (word : Word Nat) :
    (entryLabels
      (phaseParityEntries
        (phaseProfile word) (phaseParityCoordinates word))).Nodup := by
  rw [entryLabels_phaseParityEntries_word]
  exact phaseLabels_phaseProfile_nodup word

/-- The literal canonical block list of a word is itself a valid executable
first-occurrence decomposition, starting with no previously seen marker. -/
theorem canonicalPhaseParityGapBlocks_wellFormed
    (word : Word Nat) :
    GapBlocksWellFormed [] (canonicalPhaseParityGapBlocks word) := by
  change
    GapBlocksWellFormed []
      (canonicalGapBlocks
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)))
  exact canonicalGapBlocks_wellFormed _
    (entryLabels_phaseParityEntries_word_nodup word)

/-! ## Marker/phase alignment and source last-gap linkage -/

private theorem split_entries_of_map_eq_append_cons
    {alpha beta : Type} (mapEntry : alpha -> beta)
    {entries : List alpha} (before : List beta)
    (last : beta) (after : List beta)
    (equality : entries.map mapEntry = before ++ last :: after) :
    exists beforeEntries lastEntry afterEntries,
      entries = beforeEntries ++ lastEntry :: afterEntries ∧
      beforeEntries.map mapEntry = before ∧
      mapEntry lastEntry = last ∧
      afterEntries.map mapEntry = after := by
  induction before generalizing entries with
  | nil =>
      cases entries with
      | nil =>
          simp at equality
      | cons entry rest =>
          simp only [List.map_cons, List.nil_append,
            List.cons.injEq] at equality
          exact
            ⟨[], entry, rest, rfl, rfl,
              equality.1, equality.2⟩
  | cons head tail induction =>
      cases entries with
      | nil =>
          simp at equality
      | cons entry rest =>
          simp only [List.map_cons, List.cons_append,
            List.cons.injEq] at equality
          obtain ⟨headEqual, restEqual⟩ := equality
          obtain ⟨beforeEntries, lastEntry, afterEntries,
              entryShape, beforeMap, lastMap, afterMap⟩ :=
            induction restEqual
          refine
            ⟨entry :: beforeEntries, lastEntry, afterEntries,
              ?_, ?_, lastMap, afterMap⟩
          · simp [entryShape]
          · simp [headEqual, beforeMap]

theorem phaseProfile_eq_of_entry_split
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    phaseProfile word =
      before.map (fun entry => entry.phase) ++
        last.phase :: after.map (fun entry => entry.phase) := by
  rw [← phases_phaseParityEntries_word word, split]
  simp

theorem phaseLabels_eq_of_entry_split
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    phaseLabels (phaseProfile word) =
      entryLabels before ++ last.phase.label :: entryLabels after := by
  rw [phaseProfile_eq_of_entry_split word split]
  simp [phaseLabels, entryLabels, List.map_map,
    Function.comp_def]

theorem sourceGapBlockMarkers_eq_of_entry_split
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    gapBlockMarkers (gapBlocksList word.toList) =
      entryLabels before ++ last.phase.label :: entryLabels after := by
  rw [← phaseLabels_phaseProfileList_eq_gapBlockMarkers]
  exact phaseLabels_eq_of_entry_split word split

theorem canonicalGapBlockMarkers_eq_of_entry_split
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    gapBlockMarkers (canonicalPhaseParityGapBlocks word) =
      entryLabels before ++ last.phase.label :: entryLabels after := by
  rw [markers_canonicalPhaseParityGapBlocks]
  exact phaseLabels_eq_of_entry_split word split

theorem hasDoubledPhase_eq_phaseListHasDoubled :
    forall entries : List PhaseParityEntry,
      hasDoubledPhase entries =
        phaseListHasDoubled
          (entries.map (fun entry => entry.phase))
  | [] => rfl
  | entry :: rest => by
      simp [hasDoubledPhase, phaseListHasDoubled,
        hasDoubledPhase_eq_phaseListHasDoubled rest]

theorem hasDoubledPhase_phaseParityEntries_word
    (word : Word Nat) :
    hasDoubledPhase
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) =
      phaseListHasDoubled (phaseProfile word) := by
  rw [hasDoubledPhase_eq_phaseListHasDoubled,
    phases_phaseParityEntries_word]

theorem canonicalGapBlocks_eq_markerOnly_of_noDoubled
    {entries : List PhaseParityEntry}
    (noneDoubled : hasDoubledPhase entries = false) :
    canonicalGapBlocks entries = markerOnlyGapBlocks entries := by
  cases entries with
  | nil => rfl
  | cons entry rest =>
      have allUndoubled :=
        (hasDoubledPhase_eq_false_iff (entry :: rest)).mp
          noneDoubled
      have entryUndoubled : entry.phase.doubled = false :=
        allUndoubled entry (List.Mem.head rest)
      have restUndoubled : hasDoubledPhase rest = false :=
        (hasDoubledPhase_eq_false_iff rest).mpr (by
          intro selected member
          exact allUndoubled selected
            (List.Mem.tail entry member))
      simp [canonicalGapBlocks, canonicalGapBlocksAux,
        entryUndoubled, restUndoubled]

theorem sourceGapSeconds_empty_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = false) :
    forall block, block ∈ gapBlocksList word.toList ->
      block.seconds = [] := by
  intro block blockMember
  by_cases blockEmpty : block.seconds = []
  · exact blockEmpty
  · exfalso
    have blockPhaseMember :
        phaseOfGapBlock block ∈ phaseProfile word := by
      unfold phaseProfile
      rw [phaseGapProfileAgreement]
      exact List.mem_map.mpr ⟨block, blockMember, rfl⟩
    have entryPhaseMember :
        phaseOfGapBlock block ∈
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)).map
              (fun entry => entry.phase) := by
      rw [phases_phaseParityEntries_word]
      exact blockPhaseMember
    obtain ⟨entry, entryMember, phaseEqual⟩ :=
      List.mem_map.mp entryPhaseMember
    have entryUndoubled : entry.phase.doubled = false :=
      (hasDoubledPhase_eq_false_iff _).mp noneDoubled
        entry entryMember
    have blockDoubled : (phaseOfGapBlock block).doubled = true := by
      simp [phaseOfGapBlock, blockEmpty]
    have entryDoubled : entry.phase.doubled = true := by
      exact (congrArg Phase.doubled phaseEqual).trans blockDoubled
    rw [entryUndoubled] at entryDoubled
    cases entryDoubled

theorem render_canonicalPhaseParityGapBlocks_eq_source_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = false) :
    renderGapBlocks (canonicalPhaseParityGapBlocks word) =
      word.toList := by
  let entries :=
    phaseParityEntries
      (phaseProfile word) (phaseParityCoordinates word)
  have sourceEmpty := sourceGapSeconds_empty_of_noDoubled
    word noneDoubled
  calc
    renderGapBlocks (canonicalPhaseParityGapBlocks word) =
        renderGapBlocks (canonicalGapBlocks entries) := rfl
    _ = renderGapBlocks (markerOnlyGapBlocks entries) := by
      rw [canonicalGapBlocks_eq_markerOnly_of_noDoubled
        (entries := entries) noneDoubled]
    _ = entryLabels entries := by
      rw [render_markerOnlyGapBlocks,
        renderPhaseMarkers_eq_entryLabels]
    _ = phaseLabels (phaseProfile word) :=
      entryLabels_phaseParityEntries_word word
    _ = gapBlockMarkers (gapBlocksList word.toList) :=
      phaseLabels_phaseProfileList_eq_gapBlockMarkers word.toList
    _ = renderGapBlocks (gapBlocksList word.toList) :=
      (renderGapBlocks_eq_markers_of_seconds_empty
        (gapBlocksList word.toList) sourceEmpty).symm
    _ = word.toList := render_gapBlocksList word.toList

/-- An exact last-nonempty source block split induces the split at the last
doubled aligned phase/parity entry.  The prefix, selected entry, and suffix
remain pointwise aligned with the source gap blocks. -/
theorem entrySplit_of_source_lastNonemptyGap
    (word : Word Nat)
    {beforeBlocks afterBlocks : List GapBlock}
    {lastBlock : GapBlock}
    (sourceSplit :
      gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks)
    (lastNonempty : lastBlock.seconds ≠ [])
    (afterEmpty :
      forall block, block ∈ afterBlocks -> block.seconds = []) :
    exists beforeEntries lastEntry afterEntries,
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries ∧
      beforeEntries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock ∧
      lastEntry.phase = phaseOfGapBlock lastBlock ∧
      afterEntries.map (fun entry => entry.phase) =
        afterBlocks.map phaseOfGapBlock ∧
      lastEntry.phase.doubled = true ∧
      (forall entry, entry ∈ afterEntries ->
        entry.phase.doubled = false) := by
  let entries :=
    phaseParityEntries
      (phaseProfile word) (phaseParityCoordinates word)
  have mappedSplit :
      entries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock ++
          phaseOfGapBlock lastBlock ::
            afterBlocks.map phaseOfGapBlock := by
    calc
      entries.map (fun entry => entry.phase) =
          phaseProfile word := phases_phaseParityEntries_word word
      _ = phaseProfileList word.toList := rfl
      _ = (gapBlocksList word.toList).map phaseOfGapBlock :=
        phaseGapProfileAgreement word.toList
      _ = beforeBlocks.map phaseOfGapBlock ++
          phaseOfGapBlock lastBlock ::
            afterBlocks.map phaseOfGapBlock := by
        rw [sourceSplit]
        simp
  obtain ⟨beforeEntries, lastEntry, afterEntries,
      entrySplit, beforeAligned, lastAligned, afterAligned⟩ :=
    split_entries_of_map_eq_append_cons
      (fun entry : PhaseParityEntry => entry.phase)
      (beforeBlocks.map phaseOfGapBlock)
      (phaseOfGapBlock lastBlock)
      (afterBlocks.map phaseOfGapBlock) mappedSplit
  have lastDoubled : lastEntry.phase.doubled = true := by
    rw [lastAligned]
    simp [phaseOfGapBlock, lastNonempty]
  have suffixUndoubled :
      forall entry, entry ∈ afterEntries ->
        entry.phase.doubled = false := by
    intro entry entryMember
    have phaseMember :
        entry.phase ∈ afterBlocks.map phaseOfGapBlock := by
      rw [← afterAligned]
      exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    obtain ⟨block, blockMember, phaseEqual⟩ :=
      List.mem_map.mp phaseMember
    have empty := afterEmpty block blockMember
    rw [← phaseEqual]
    simp [phaseOfGapBlock, empty]
  exact
    ⟨beforeEntries, lastEntry, afterEntries,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, suffixUndoubled⟩

/-- The active renderer branch exposes the source last-nonempty gap and the
aligned last doubled entry in one statement. -/
theorem sourceAndEntryLastDoubledSplit_of_active
    (word : Word Nat)
    (active :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = true) :
    exists beforeBlocks lastBlock afterBlocks
      beforeEntries lastEntry afterEntries,
      gapBlocksList word.toList =
          beforeBlocks ++ lastBlock :: afterBlocks ∧
      lastBlock.seconds ≠ [] ∧
      (forall block, block ∈ afterBlocks -> block.seconds = []) ∧
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries ∧
      beforeEntries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock ∧
      lastEntry.phase = phaseOfGapBlock lastBlock ∧
      afterEntries.map (fun entry => entry.phase) =
        afterBlocks.map phaseOfGapBlock ∧
      lastEntry.phase.doubled = true ∧
      (forall entry, entry ∈ afterEntries ->
        entry.phase.doubled = false) := by
  have sourceActive :
      phaseListHasDoubled (phaseProfileList word.toList) = true := by
    change phaseListHasDoubled (phaseProfile word) = true
    rw [← hasDoubledPhase_phaseParityEntries_word]
    exact active
  obtain ⟨beforeBlocks, lastBlock, afterBlocks,
      sourceSplit, lastNonempty, afterEmpty⟩ :=
    phaseProfileList_last_nonempty_gap_split sourceActive
  obtain ⟨beforeEntries, lastEntry, afterEntries,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, suffixUndoubled⟩ :=
    entrySplit_of_source_lastNonemptyGap
      word sourceSplit lastNonempty afterEmpty
  exact
    ⟨beforeBlocks, lastBlock, afterBlocks,
      beforeEntries, lastEntry, afterEntries,
      sourceSplit, lastNonempty, afterEmpty,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, suffixUndoubled⟩

/-- Active entries split at their last doubled phase, and the canonical block
list splits at the corresponding literal final doubled block. -/
theorem canonicalBlocksLastDoubledSplit_of_active
    (word : Word Nat)
    (active :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = true) :
    exists before last after,
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after ∧
      last.phase.doubled = true ∧
      (forall entry, entry ∈ after ->
        entry.phase.doubled = false) ∧
      canonicalPhaseParityGapBlocks word =
        canonicalPriorGapBlocks before ++
          lastDoubledGapBlock (collectParityDebt before) last ::
            markerOnlyGapBlocks after ∧
      gapBlockMarkers (canonicalPhaseParityGapBlocks word) =
        entryLabels before ++ last.phase.label :: entryLabels after := by
  obtain ⟨beforeBlocks, lastBlock, afterBlocks,
      before, last, after,
      sourceSplit, lastNonempty, afterEmpty,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, afterUndoubled⟩ :=
    sourceAndEntryLastDoubledSplit_of_active word active
  have canonicalSplit :
      canonicalPhaseParityGapBlocks word =
        canonicalPriorGapBlocks before ++
          lastDoubledGapBlock (collectParityDebt before) last ::
            markerOnlyGapBlocks after := by
    change
      canonicalGapBlocks
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = _
    rw [entrySplit]
    exact canonicalGapBlocks_lastDoubled_shape
      before last after lastDoubled afterUndoubled
  have markerSplit :=
    canonicalGapBlockMarkers_eq_of_entry_split word entrySplit
  exact
    ⟨before, last, after, entrySplit, lastDoubled,
      afterUndoubled, canonicalSplit, markerSplit⟩

/-! ## Entry parities and exact debt multiplicities -/

private theorem phaseParityCoordinates_eq_map_count
    (word : Word Nat) :
    phaseParityCoordinates word =
      (phaseProfile word).map
        (fun phase => word.toList.count phase.label % 2) := by
  simp [phaseParityCoordinates, phaseLabels, List.map_map,
    Function.comp_def]

private theorem mem_phaseParityEntries_selfCoordinates
    (counts : Nat -> Nat) :
    forall (phases : List Phase) (entry : PhaseParityEntry),
      entry ∈
          phaseParityEntries phases
            (phases.map (fun phase => counts phase.label % 2)) ->
        entry.parity = counts entry.phase.label % 2
  | [], entry, member => by
      simp [phaseParityEntries] at member
  | phase :: rest, entry, member => by
      simp only [List.map_cons, phaseParityEntries,
        List.mem_cons] at member
      rcases member with atHead | inRest
      · subst entry
        simp
      · exact mem_phaseParityEntries_selfCoordinates
          counts rest entry inRest

/-- Every aligned entry carries exactly the source count parity of its own
phase marker. -/
theorem phaseParityEntry_parity_eq_source_count
    (word : Word Nat) {entry : PhaseParityEntry}
    (member :
      entry ∈
        phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) :
    entry.parity = word.toList.count entry.phase.label % 2 := by
  rw [phaseParityCoordinates_eq_map_count] at member
  exact mem_phaseParityEntries_selfCoordinates
    (fun letter => word.toList.count letter)
    (phaseProfile word) entry member

theorem mem_collectParityDebt_entryLabels
    {letter : Nat} {entries : List PhaseParityEntry}
    (member : letter ∈ collectParityDebt entries) :
    letter ∈ entryLabels entries := by
  rw [mem_collectParityDebt_iff] at member
  obtain ⟨entry, entryMember, _, _, rfl⟩ := member
  exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩

theorem collectParityDebt_nodup :
    forall entries : List PhaseParityEntry,
      (entryLabels entries).Nodup ->
        (collectParityDebt entries).Nodup
  | [], _ => by
      simp [collectParityDebt]
  | entry :: rest, labelsNodup => by
      have labelData :
          entry.phase.label ∉ entryLabels rest ∧
            (entryLabels rest).Nodup := by
        simpa [entryLabels] using
          (List.nodup_cons.mp labelsNodup)
      have tailNodup := collectParityDebt_nodup rest labelData.2
      cases doubled : entry.phase.doubled with
      | true =>
          simpa [collectParityDebt, parityDebtContribution,
            doubled] using tailNodup
      | false =>
          by_cases even : entry.parity % 2 = 0
          · have markerAbsent :
                entry.phase.label ∉ collectParityDebt rest := by
              intro member
              apply labelData.1
              exact mem_collectParityDebt_entryLabels member
            simpa [collectParityDebt, parityDebtContribution,
              doubled, even, markerAbsent] using tailNodup
          · simpa [collectParityDebt, parityDebtContribution,
              doubled, even] using tailNodup

/-- Debt is a set, not a multiset: each selected even undoubled marker occurs
exactly once and every other letter occurs zero times. -/
theorem count_collectParityDebt
    (entries : List PhaseParityEntry)
    (labelsNodup : (entryLabels entries).Nodup)
    (letter : Nat) :
    (collectParityDebt entries).count letter =
      if exists entry,
          entry ∈ entries ∧
          entry.phase.doubled = false ∧
          entry.parity % 2 = 0 ∧
          letter = entry.phase.label
      then 1 else 0 := by
  rw [(collectParityDebt_nodup entries labelsNodup).count]
  by_cases member : letter ∈ collectParityDebt entries
  · have selected := (mem_collectParityDebt_iff letter entries).mp member
    simp [member, selected]
  · have noSelected :
        ¬ exists entry,
          entry ∈ entries ∧
          entry.phase.doubled = false ∧
          entry.parity % 2 = 0 ∧
          letter = entry.phase.label := by
      intro selected
      exact member <|
        (mem_collectParityDebt_iff letter entries).mpr selected
    simp [member, noSelected]

theorem count_collectParityDebt_mod_two
    (entries : List PhaseParityEntry)
    (labelsNodup : (entryLabels entries).Nodup)
    (letter : Nat) :
    (collectParityDebt entries).count letter % 2 =
      if exists entry,
          entry ∈ entries ∧
          entry.phase.doubled = false ∧
          entry.parity % 2 = 0 ∧
          letter = entry.phase.label
      then 1 else 0 := by
  rw [count_collectParityDebt entries labelsNodup letter]
  split <;> simp

theorem collectParityDebt_seen_in_prefix
    {seen : List Nat} {entries : List PhaseParityEntry}
    (labelsSeen :
      forall entry, entry ∈ entries ->
        entry.phase.label ∈ seen) :
    forall letter, letter ∈ collectParityDebt entries ->
      letter ∈ seen := by
  intro letter member
  rw [mem_collectParityDebt_iff] at member
  obtain ⟨entry, entryMember, _, _, rfl⟩ := member
  exact labelsSeen entry entryMember

theorem entryLabels_split_nodup
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    (entryLabels before ++
      last.phase.label :: entryLabels after).Nodup := by
  rw [← phaseLabels_eq_of_entry_split word split]
  exact phaseLabels_phaseProfile_nodup word

theorem entryLabels_before_nodup
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    (entryLabels before).Nodup :=
  (List.nodup_append.mp
    (entryLabels_split_nodup word split)).1

theorem lastLabel_not_mem_entryLabels_before
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    last.phase.label ∉ entryLabels before := by
  have disjoint :=
    (List.nodup_append.mp
      (entryLabels_split_nodup word split)).2.2
  intro member
  exact disjoint last.phase.label member last.phase.label
    (List.Mem.head (entryLabels after)) rfl

theorem lastLabel_not_mem_collectParityDebt_before
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    last.phase.label ∉ collectParityDebt before := by
  intro member
  exact lastLabel_not_mem_entryLabels_before word split
    (mem_collectParityDebt_entryLabels member)

/-! ## Per-letter renderer accounting -/

theorem count_render_canonicalPhaseParityGapBlocks
    (word : Word Nat) (letter : Nat) :
    (canonicalPhaseParityList word).count letter =
      (gapBlockMarkers
          (canonicalPhaseParityGapBlocks word)).count letter +
        (gapBlockSeconds
          (canonicalPhaseParityGapBlocks word)).count letter := by
  rw [← render_canonicalPhaseParityGapBlocks]
  exact count_renderGapBlocks letter
    (canonicalPhaseParityGapBlocks word)

theorem count_mod_two_render_canonicalPhaseParityGapBlocks
    (word : Word Nat) (letter : Nat) :
    (canonicalPhaseParityList word).count letter % 2 =
      ((gapBlockMarkers
          (canonicalPhaseParityGapBlocks word)).count letter +
        (gapBlockSeconds
          (canonicalPhaseParityGapBlocks word)).count letter) % 2 := by
  rw [count_render_canonicalPhaseParityGapBlocks]

theorem count_render_sourceGapBlocks
    (word : Word Nat) (letter : Nat) :
    word.toList.count letter =
      (gapBlockMarkers (gapBlocksList word.toList)).count letter +
        (gapBlockSeconds (gapBlocksList word.toList)).count letter := by
  let blocks := gapBlocksList word.toList
  calc
    word.toList.count letter =
        (renderGapBlocks blocks).count letter := by
      rw [render_gapBlocksList]
    _ = (gapBlockMarkers blocks).count letter +
        (gapBlockSeconds blocks).count letter :=
      count_renderGapBlocks letter blocks

theorem count_mod_two_render_sourceGapBlocks
    (word : Word Nat) (letter : Nat) :
    word.toList.count letter % 2 =
      ((gapBlockMarkers (gapBlocksList word.toList)).count letter +
        (gapBlockSeconds (gapBlocksList word.toList)).count letter) % 2 := by
  rw [count_render_sourceGapBlocks]

theorem render_markerOnlyGapBlocks_eq_entryLabels
    (entries : List PhaseParityEntry) :
    renderGapBlocks (markerOnlyGapBlocks entries) =
      entryLabels entries := by
  rw [render_markerOnlyGapBlocks,
    renderPhaseMarkers_eq_entryLabels]

theorem count_render_markerOnlyGapBlocks_of_mem
    {entries : List PhaseParityEntry}
    (labelsNodup : (entryLabels entries).Nodup)
    {entry : PhaseParityEntry} (member : entry ∈ entries) :
    (renderGapBlocks (markerOnlyGapBlocks entries)).count
        entry.phase.label = 1 := by
  rw [render_markerOnlyGapBlocks_eq_entryLabels,
    labelsNodup.count]
  have labelMember : entry.phase.label ∈ entryLabels entries :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  simp [labelMember]

theorem canonicalPriorGapBlock_debtContribution_parity
    (entry : PhaseParityEntry) :
    ((renderGapBlocks [canonicalPriorGapBlock entry]).count
          entry.phase.label +
        (parityDebtContribution entry).count entry.phase.label) % 2 =
      entry.parity % 2 := by
  have parityBound : entry.parity % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  cases doubled : entry.phase.doubled with
  | false =>
      by_cases even : entry.parity % 2 = 0
      · simp [canonicalPriorGapBlock, markerOnlyGapBlock,
          parityDebtContribution, renderGapBlocks,
          doubled, even]
      · have odd : entry.parity % 2 = 1 := by omega
        simp [canonicalPriorGapBlock, markerOnlyGapBlock,
          parityDebtContribution, renderGapBlocks,
          doubled, even, odd]
  | true =>
      by_cases even : entry.parity % 2 = 0
      · simp [canonicalPriorGapBlock, priorDoubledGapBlock,
          parityDebtContribution, renderGapBlocks,
          doubled, even]
      · have odd : entry.parity % 2 = 1 := by omega
        simp [canonicalPriorGapBlock, priorDoubledGapBlock,
          parityDebtContribution, renderGapBlocks,
          doubled, even, odd]

theorem count_render_canonicalPriorGapBlock_of_ne
    (entry : PhaseParityEntry) {letter : Nat}
    (different : letter ≠ entry.phase.label) :
    (renderGapBlocks [canonicalPriorGapBlock entry]).count letter = 0 := by
  have reverse : entry.phase.label ≠ letter := Ne.symm different
  cases doubled : entry.phase.doubled <;>
    by_cases even : entry.parity % 2 = 0 <;>
      simp [canonicalPriorGapBlock, priorDoubledGapBlock,
        markerOnlyGapBlock, renderGapBlocks,
        doubled, even, different, reverse]

theorem count_parityDebtContribution_of_ne
    (entry : PhaseParityEntry) {letter : Nat}
    (different : letter ≠ entry.phase.label) :
    (parityDebtContribution entry).count letter = 0 := by
  have reverse : entry.phase.label ≠ letter := Ne.symm different
  cases doubled : entry.phase.doubled <;>
    by_cases even : entry.parity % 2 = 0 <;>
      simp [parityDebtContribution, doubled, even,
        different, reverse]

/-- For every prefix entry, the parity selected by its own prior block plus
its possible one-copy terminal debt is exactly its stored parity. -/
theorem canonicalPriorGapBlocks_debt_parity_of_mem :
    forall {entries : List PhaseParityEntry},
      (entryLabels entries).Nodup ->
      forall {selected : PhaseParityEntry}, selected ∈ entries ->
        ((renderGapBlocks (canonicalPriorGapBlocks entries)).count
              selected.phase.label +
            (collectParityDebt entries).count
              selected.phase.label) % 2 =
          selected.parity % 2
  | [], _, selected, member => by
      simp at member
  | entry :: rest, labelsNodup, selected, member => by
      have labelData :
          entry.phase.label ∉ entryLabels rest ∧
            (entryLabels rest).Nodup := by
        simpa [entryLabels] using
          (List.nodup_cons.mp labelsNodup)
      rcases List.mem_cons.mp member with atHead | inRest
      · subst selected
        have tailRenderAbsent :
            entry.phase.label ∉
              renderGapBlocks (canonicalPriorGapBlocks rest) := by
          intro inRendered
          rw [mem_render_canonicalPriorGapBlocks_iff] at inRendered
          obtain ⟨later, laterMember, equal⟩ := inRendered
          apply labelData.1
          exact List.mem_map.mpr
            ⟨later, laterMember, equal.symm⟩
        have tailDebtAbsent :
            entry.phase.label ∉ collectParityDebt rest := by
          intro inDebt
          exact labelData.1
            (mem_collectParityDebt_entryLabels inDebt)
        have tailRenderCount :
            (renderGapBlocks (canonicalPriorGapBlocks rest)).count
                entry.phase.label = 0 :=
          List.count_eq_zero.mpr tailRenderAbsent
        have tailDebtCount :
            (collectParityDebt rest).count entry.phase.label = 0 :=
          List.count_eq_zero.mpr tailDebtAbsent
        rw [show canonicalPriorGapBlocks (entry :: rest) =
              [canonicalPriorGapBlock entry] ++
                canonicalPriorGapBlocks rest by rfl,
            renderGapBlocks_append, List.count_append,
            collectParityDebt, List.count_append,
            tailRenderCount, tailDebtCount]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          canonicalPriorGapBlock_debtContribution_parity entry
      · have different :
            selected.phase.label ≠ entry.phase.label := by
          intro equal
          apply labelData.1
          rw [← equal]
          exact List.mem_map.mpr ⟨selected, inRest, rfl⟩
        have headRenderCount :=
          count_render_canonicalPriorGapBlock_of_ne
            entry different
        have headDebtCount :=
          count_parityDebtContribution_of_ne entry different
        have tailAccounting :=
          canonicalPriorGapBlocks_debt_parity_of_mem
            labelData.2 inRest
        rw [show canonicalPriorGapBlocks (entry :: rest) =
              [canonicalPriorGapBlock entry] ++
                canonicalPriorGapBlocks rest by rfl,
            renderGapBlocks_append, List.count_append,
            collectParityDebt, List.count_append,
            headRenderCount, headDebtCount]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          tailAccounting

theorem count_render_priorDoubledGapBlock_self
    (entry : PhaseParityEntry) :
    (renderGapBlocks [priorDoubledGapBlock entry]).count
        entry.phase.label =
      if entry.parity % 2 = 0 then 2 else 3 := by
  by_cases even : entry.parity % 2 = 0 <;>
    simp [priorDoubledGapBlock, renderGapBlocks, even]

theorem count_render_priorDoubledGapBlock_of_ne
    (entry : PhaseParityEntry) {letter : Nat}
    (different : letter ≠ entry.phase.label) :
    (renderGapBlocks [priorDoubledGapBlock entry]).count letter = 0 := by
  have reverse : entry.phase.label ≠ letter := Ne.symm different
  by_cases even : entry.parity % 2 = 0 <;>
    simp [priorDoubledGapBlock, renderGapBlocks,
      even, different, reverse]

theorem count_render_lastDoubledGapBlock_self
    (debt : List Nat) (entry : PhaseParityEntry) :
    (renderGapBlocks [lastDoubledGapBlock debt entry]).count
        entry.phase.label =
      if entry.parity % 2 = 0 then
        2 + debt.count entry.phase.label
      else if debt = [] then
        3
      else
        1 + debt.count entry.phase.label := by
  by_cases even : entry.parity % 2 = 0
  · simp [lastDoubledGapBlock, renderGapBlocks, even]
    omega
  · by_cases empty : debt = []
    · simp [lastDoubledGapBlock, renderGapBlocks, even, empty]
    · simp [lastDoubledGapBlock, renderGapBlocks, even, empty]
      omega

theorem count_render_lastDoubledGapBlock_of_ne
    (debt : List Nat) (entry : PhaseParityEntry)
    {letter : Nat} (different : letter ≠ entry.phase.label) :
    (renderGapBlocks [lastDoubledGapBlock debt entry]).count letter =
      debt.count letter := by
  have reverse : entry.phase.label ≠ letter := Ne.symm different
  by_cases even : entry.parity % 2 = 0
  · simp [lastDoubledGapBlock, renderGapBlocks,
      even, different, reverse]
  · by_cases empty : debt = []
    · simp [lastDoubledGapBlock, renderGapBlocks,
        even, empty, different, reverse]
    · simp [lastDoubledGapBlock, renderGapBlocks,
        even, empty, different, reverse]

theorem lastDoubledGapBlock_self_parity
    (debt : List Nat) (entry : PhaseParityEntry)
    (markerAbsent : entry.phase.label ∉ debt) :
    (renderGapBlocks [lastDoubledGapBlock debt entry]).count
        entry.phase.label % 2 = entry.parity % 2 := by
  have debtCountZero : debt.count entry.phase.label = 0 :=
    List.count_eq_zero.mpr markerAbsent
  have parityBound : entry.parity % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  by_cases even : entry.parity % 2 = 0
  · simp [lastDoubledGapBlock, renderGapBlocks,
      even, debtCountZero]
  · have odd : entry.parity % 2 = 1 := by omega
    by_cases empty : debt = []
    · simp [lastDoubledGapBlock, renderGapBlocks,
        even, odd, empty]
    · simp [lastDoubledGapBlock, renderGapBlocks,
        even, odd, empty, debtCountZero]

theorem lastDoubledGapBlock_entrySplit_parity
    (word : Word Nat)
    {before after : List PhaseParityEntry}
    {last : PhaseParityEntry}
    (split :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        before ++ last :: after) :
    (renderGapBlocks
        [lastDoubledGapBlock (collectParityDebt before) last]).count
          last.phase.label % 2 =
      last.parity % 2 :=
  lastDoubledGapBlock_self_parity
    (collectParityDebt before) last
    (lastLabel_not_mem_collectParityDebt_before word split)

theorem render_canonicalGapBlocks_lastDoubled_shape
    (before : List PhaseParityEntry) (last : PhaseParityEntry)
    (after : List PhaseParityEntry)
    (lastDoubled : last.phase.doubled = true)
    (afterUndoubled :
      forall entry, entry ∈ after -> entry.phase.doubled = false) :
    renderGapBlocks (canonicalGapBlocks (before ++ last :: after)) =
      renderGapBlocks (canonicalPriorGapBlocks before) ++
        renderGapBlocks
          [lastDoubledGapBlock (collectParityDebt before) last] ++
        renderGapBlocks (markerOnlyGapBlocks after) := by
  rw [canonicalGapBlocks_lastDoubled_shape
    before last after lastDoubled afterUndoubled]
  rw [show
      canonicalPriorGapBlocks before ++
          lastDoubledGapBlock (collectParityDebt before) last ::
            markerOnlyGapBlocks after =
        (canonicalPriorGapBlocks before ++
          [lastDoubledGapBlock (collectParityDebt before) last]) ++
            markerOnlyGapBlocks after by
      simp [List.append_assoc]]
  rw [renderGapBlocks_append, renderGapBlocks_append]

/-- Entrywise parity accounting for the complete last-doubled renderer.  The
only semantic input is that trailing undoubled entries have odd marker
parity; the source-block linkage below supplies this fact for word keys. -/
theorem canonicalGapBlocks_entry_parity_of_lastDoubled_split
    {before after : List PhaseParityEntry}
    {last selected : PhaseParityEntry}
    (labelsNodup :
      (entryLabels before ++
        last.phase.label :: entryLabels after).Nodup)
    (lastDoubled : last.phase.doubled = true)
    (afterUndoubled :
      forall entry, entry ∈ after -> entry.phase.doubled = false)
    (afterParity :
      forall entry, entry ∈ after -> entry.parity % 2 = 1)
    (selectedMember : selected ∈ before ++ last :: after) :
    (renderGapBlocks
        (canonicalGapBlocks (before ++ last :: after))).count
          selected.phase.label % 2 =
      selected.parity % 2 := by
  have splitNodup := List.nodup_append.mp labelsNodup
  have beforeNodup : (entryLabels before).Nodup := splitNodup.1
  have restNodup :
      (last.phase.label :: entryLabels after).Nodup :=
    splitNodup.2.1
  have cross := splitNodup.2.2
  have lastNotAfter : last.phase.label ∉ entryLabels after :=
    (List.nodup_cons.mp restNodup).1
  rw [render_canonicalGapBlocks_lastDoubled_shape
    before last after lastDoubled afterUndoubled,
    List.count_append, List.count_append]
  rcases List.mem_append.mp selectedMember with inBefore | atLastOrAfter
  · have selectedLabelInBefore :
        selected.phase.label ∈ entryLabels before :=
      List.mem_map.mpr ⟨selected, inBefore, rfl⟩
    have differentLast :
        selected.phase.label ≠ last.phase.label := by
      intro equal
      exact cross selected.phase.label selectedLabelInBefore
        last.phase.label (List.Mem.head (entryLabels after)) equal
    have selectedNotAfter :
        selected.phase.label ∉ entryLabels after := by
      intro inAfter
      exact cross selected.phase.label selectedLabelInBefore
        selected.phase.label
        (List.Mem.tail last.phase.label inAfter) rfl
    have afterCountZero :
        (renderGapBlocks (markerOnlyGapBlocks after)).count
            selected.phase.label = 0 := by
      rw [render_markerOnlyGapBlocks_eq_entryLabels]
      exact List.count_eq_zero.mpr selectedNotAfter
    rw [count_render_lastDoubledGapBlock_of_ne
      (collectParityDebt before) last differentLast,
      afterCountZero]
    simpa [Nat.add_assoc] using
      canonicalPriorGapBlocks_debt_parity_of_mem
        beforeNodup inBefore
  · rcases List.mem_cons.mp atLastOrAfter with atLast | inAfter
    · subst selected
      have lastNotBefore : last.phase.label ∉ entryLabels before := by
        intro inBeforeLabels
        exact cross last.phase.label inBeforeLabels
          last.phase.label (List.Mem.head (entryLabels after)) rfl
      have beforeRenderCountZero :
          (renderGapBlocks (canonicalPriorGapBlocks before)).count
              last.phase.label = 0 := by
        apply List.count_eq_zero.mpr
        intro inRendered
        rw [mem_render_canonicalPriorGapBlocks_iff] at inRendered
        obtain ⟨entry, entryMember, equal⟩ := inRendered
        exact lastNotBefore <|
          List.mem_map.mpr ⟨entry, entryMember, equal.symm⟩
      have afterCountZero :
          (renderGapBlocks (markerOnlyGapBlocks after)).count
              last.phase.label = 0 := by
        rw [render_markerOnlyGapBlocks_eq_entryLabels]
        exact List.count_eq_zero.mpr lastNotAfter
      have debtAbsent :
          last.phase.label ∉ collectParityDebt before := by
        intro member
        exact lastNotBefore
          (mem_collectParityDebt_entryLabels member)
      rw [beforeRenderCountZero, afterCountZero]
      simpa using
        lastDoubledGapBlock_self_parity
          (collectParityDebt before) last debtAbsent
    · have selectedLabelInAfter :
          selected.phase.label ∈ entryLabels after :=
        List.mem_map.mpr ⟨selected, inAfter, rfl⟩
      have differentLast :
          selected.phase.label ≠ last.phase.label := by
        intro equal
        apply lastNotAfter
        rw [← equal]
        exact selectedLabelInAfter
      have selectedNotBefore :
          selected.phase.label ∉ entryLabels before := by
        intro inBeforeLabels
        exact cross selected.phase.label inBeforeLabels
          selected.phase.label
          (List.Mem.tail last.phase.label selectedLabelInAfter) rfl
      have beforeRenderCountZero :
          (renderGapBlocks (canonicalPriorGapBlocks before)).count
              selected.phase.label = 0 := by
        apply List.count_eq_zero.mpr
        intro inRendered
        rw [mem_render_canonicalPriorGapBlocks_iff] at inRendered
        obtain ⟨entry, entryMember, equal⟩ := inRendered
        exact selectedNotBefore <|
          List.mem_map.mpr ⟨entry, entryMember, equal.symm⟩
      have debtCountZero :
          (collectParityDebt before).count selected.phase.label = 0 := by
        apply List.count_eq_zero.mpr
        intro inDebt
        exact selectedNotBefore
          (mem_collectParityDebt_entryLabels inDebt)
      have lastCountZero :
          (renderGapBlocks
            [lastDoubledGapBlock (collectParityDebt before) last]).count
              selected.phase.label = 0 := by
        rw [count_render_lastDoubledGapBlock_of_ne
          (collectParityDebt before) last differentLast]
        exact debtCountZero
      have afterCountOne :=
        count_render_markerOnlyGapBlocks_of_mem
          (List.nodup_cons.mp restNodup).2 inAfter
      rw [beforeRenderCountZero, lastCountZero, afterCountOne,
        afterParity selected inAfter]

/-- In a source last-nonempty-gap split, every aligned entry after the last
doubled one has source multiplicity one, hence stored parity one. -/
theorem afterEntry_parity_one_of_source_lastNonemptyGap
    (word : Word Nat)
    {beforeBlocks afterBlocks : List GapBlock}
    {lastBlock : GapBlock}
    {beforeEntries afterEntries : List PhaseParityEntry}
    {lastEntry selected : PhaseParityEntry}
    (sourceSplit :
      gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks)
    (afterEmpty :
      forall block, block ∈ afterBlocks -> block.seconds = [])
    (entrySplit :
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries)
    (afterAligned :
      afterEntries.map (fun entry => entry.phase) =
        afterBlocks.map phaseOfGapBlock)
    (selectedMember : selected ∈ afterEntries) :
    selected.parity % 2 = 1 := by
  have selectedPhaseMember :
      selected.phase ∈ afterBlocks.map phaseOfGapBlock := by
    rw [← afterAligned]
    exact List.mem_map.mpr ⟨selected, selectedMember, rfl⟩
  obtain ⟨selectedBlock, selectedBlockMember, phaseEqual⟩ :=
    List.mem_map.mp selectedPhaseMember
  obtain ⟨blockPrefix, blockSuffix, afterShape⟩ :=
    List.mem_iff_append.mp selectedBlockMember
  have fullSplit :
      gapBlocksList word.toList =
        (beforeBlocks ++ lastBlock :: blockPrefix) ++
          selectedBlock :: blockSuffix := by
    calc
      gapBlocksList word.toList =
          beforeBlocks ++ lastBlock :: afterBlocks := sourceSplit
      _ = (beforeBlocks ++ lastBlock :: blockPrefix) ++
          selectedBlock :: blockSuffix := by
        rw [afterShape]
        simp [List.append_assoc]
  have selectedTrailingEmpty :
      forall block, block ∈ selectedBlock :: blockSuffix ->
        block.seconds = [] := by
    intro block member
    apply afterEmpty block
    rw [afterShape]
    exact List.mem_append.mpr (Or.inr member)
  have selectedBlockCount :=
    count_renderGapBlocks_marker_eq_one_of_trailing_empty
      (gapBlocksList_wellFormed word.toList)
      fullSplit selectedTrailingEmpty
  have markerEqual :
      selectedBlock.marker = selected.phase.label := by
    have labelsEqual := congrArg Phase.label phaseEqual
    simpa [phaseOfGapBlock] using labelsEqual
  have sourceCount :
      word.toList.count selected.phase.label = 1 := by
    rw [← render_gapBlocksList word.toList, ← markerEqual]
    exact selectedBlockCount
  have selectedInEntries :
      selected ∈
        phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) := by
    rw [entrySplit]
    exact List.mem_append.mpr <|
      Or.inr <| List.Mem.tail lastEntry selectedMember
  have storedParity :=
    phaseParityEntry_parity_eq_source_count
      word selectedInEntries
  rw [sourceCount] at storedParity
  rw [storedParity]

private theorem count_render_canonicalPhaseParityGapBlocks_mod_two_of_active
    (word : Word Nat) (letter : Nat)
    (active :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = true) :
    (renderGapBlocks (canonicalPhaseParityGapBlocks word)).count
        letter % 2 = word.toList.count letter % 2 := by
  obtain ⟨beforeBlocks, lastBlock, afterBlocks,
      beforeEntries, lastEntry, afterEntries,
      sourceSplit, lastNonempty, afterEmpty,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, afterUndoubled⟩ :=
    sourceAndEntryLastDoubledSplit_of_active word active
  have labelsNodup := entryLabels_split_nodup word entrySplit
  have afterParity :
      forall entry, entry ∈ afterEntries ->
        entry.parity % 2 = 1 := by
    intro entry member
    exact afterEntry_parity_one_of_source_lastNonemptyGap
      word sourceSplit afterEmpty entrySplit afterAligned member
  let allEntries := beforeEntries ++ lastEntry :: afterEntries
  by_cases supported : letter ∈ entryLabels allEntries
  · change
      letter ∈
        allEntries.map (fun entry => entry.phase.label) at supported
    obtain ⟨selected, selectedMember, labelEqual⟩ :=
      List.mem_map.mp supported
    have selectedTarget :=
      canonicalGapBlocks_entry_parity_of_lastDoubled_split
        labelsNodup lastDoubled afterUndoubled afterParity
        selectedMember
    have selectedInWordEntries :
        selected ∈
          phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word) := by
      rw [entrySplit]
      exact selectedMember
    have selectedSource :=
      phaseParityEntry_parity_eq_source_count
        word selectedInWordEntries
    change
      (renderGapBlocks
        (canonicalGapBlocks
          (phaseParityEntries
            (phaseProfile word)
            (phaseParityCoordinates word)))).count letter % 2 =
          word.toList.count letter % 2
    rw [entrySplit]
    rw [← labelEqual]
    simpa [selectedSource] using selectedTarget
  · have sourceMarkers :
        gapBlockMarkers (gapBlocksList word.toList) =
          entryLabels allEntries := by
      calc
        gapBlockMarkers (gapBlocksList word.toList) =
            phaseLabels (phaseProfile word) := by
          exact
            (phaseLabels_phaseProfileList_eq_gapBlockMarkers
              word.toList).symm
        _ = entryLabels
            (phaseParityEntries
              (phaseProfile word) (phaseParityCoordinates word)) :=
          (entryLabels_phaseParityEntries_word word).symm
        _ = entryLabels allEntries := by
          rw [entrySplit]
    have canonicalMarkers :
        gapBlockMarkers (canonicalPhaseParityGapBlocks word) =
          entryLabels allEntries := by
      calc
        gapBlockMarkers (canonicalPhaseParityGapBlocks word) =
            phaseLabels (phaseProfile word) :=
          markers_canonicalPhaseParityGapBlocks word
        _ = entryLabels
            (phaseParityEntries
              (phaseProfile word) (phaseParityCoordinates word)) :=
          (entryLabels_phaseParityEntries_word word).symm
        _ = entryLabels allEntries := by
          rw [entrySplit]
    have sourceMarkerAbsent :
        letter ∉ gapBlockMarkers (gapBlocksList word.toList) := by
      rw [sourceMarkers]
      exact supported
    have canonicalMarkerAbsent :
        letter ∉
          gapBlockMarkers (canonicalPhaseParityGapBlocks word) := by
      rw [canonicalMarkers]
      exact supported
    have sourceRenderedAbsent :
        letter ∉ renderGapBlocks (gapBlocksList word.toList) :=
      not_mem_renderGapBlocks_of_not_mem_markers
        (gapBlocksList_wellFormed word.toList) sourceMarkerAbsent
    have canonicalRenderedAbsent :
        letter ∉ renderGapBlocks
          (canonicalPhaseParityGapBlocks word) :=
      not_mem_renderGapBlocks_of_not_mem_markers
        (canonicalPhaseParityGapBlocks_wellFormed word)
        canonicalMarkerAbsent
    have sourceAbsent : letter ∉ word.toList := by
      rw [← render_gapBlocksList word.toList]
      exact sourceRenderedAbsent
    rw [List.count_eq_zero.mpr canonicalRenderedAbsent,
      List.count_eq_zero.mpr sourceAbsent]

/-- The exact downstream parity gate: the literal canonical gap-block
renderer preserves every source count modulo two. -/
theorem count_render_canonicalPhaseParityGapBlocks_mod_two
    (word : Word Nat) (letter : Nat) :
    (renderGapBlocks (canonicalPhaseParityGapBlocks word)).count
        letter % 2 = word.toList.count letter % 2 := by
  cases doubled :
      hasDoubledPhase
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) with
  | false =>
      rw [render_canonicalPhaseParityGapBlocks_eq_source_of_noDoubled
        word doubled]
  | true =>
      exact
        count_render_canonicalPhaseParityGapBlocks_mod_two_of_active
          word letter doubled

end Order6Hull23_1PhaseParityBlockAccounting
end CoRoots
end SemigroupBasis
