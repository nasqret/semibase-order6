import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPostSweepAssembly

/-!
# Hull 23.1 phase-parity normalization assembly

This module is the assembly boundary for the Proposition 23.1 normalizer.
It contains no theorem transported from the Proposition 21.1 hull.  The
inactive branch (no doubled phase) is closed directly from the executable gap
parser, and the word-level and two-sided parts are reduced to a single active
list-normalization contract.

The active contract is deliberately stated at list level.  Its proof has to
use the B15 moves from `Order6Hull23_1PhaseParityMoves` and
`Order6Hull23_1PhaseParityDebtMoves`; merely retargeting a normalizer for a
different hull would not inhabit this contract.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityNormalization

open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityInvariant
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-! ## The branch with no doubled phase -/

private theorem renderGapBlocks_eq_markers_of_seconds_empty :
    forall blocks : List GapBlock,
      (forall block, block ∈ blocks -> block.seconds = []) ->
        renderGapBlocks blocks = gapBlockMarkers blocks
  | [], _ => rfl
  | block :: rest, empty => by
      have headEmpty : block.seconds = [] :=
        empty block (List.Mem.head rest)
      have tailEmpty :
          forall selected, selected ∈ rest -> selected.seconds = [] := by
        intro selected member
        exact empty selected (List.Mem.tail block member)
      simp [renderGapBlocks, gapBlockMarkers, headEmpty,
        renderGapBlocks_eq_markers_of_seconds_empty rest tailEmpty]

private theorem renderPhaseMarkers_eq_map_labels :
    forall entries : List PhaseParityEntry,
      renderPhaseMarkers entries =
        entries.map (fun entry => entry.phase.label)
  | [] => rfl
  | entry :: rest => by
      simp [renderPhaseMarkers,
        renderPhaseMarkers_eq_map_labels rest]

private theorem renderLeeZhang23_3Aux_eq_markers_of_noDoubled
    (debt : List Nat) :
    forall entries : List PhaseParityEntry,
      hasDoubledPhase entries = false ->
        renderLeeZhang23_3Aux debt entries =
          renderPhaseMarkers entries
  | [], _ => rfl
  | entry :: rest, noneDoubled => by
      have allUndoubled :=
        (hasDoubledPhase_eq_false_iff (entry :: rest)).mp
          noneDoubled
      have entryUndoubled : entry.phase.doubled = false :=
        allUndoubled entry (by simp)
      have restUndoubled : hasDoubledPhase rest = false :=
        (hasDoubledPhase_eq_false_iff rest).mpr (by
          intro selected member
          exact allUndoubled selected
            (List.Mem.tail entry member))
      simp [renderLeeZhang23_3Aux, entryUndoubled,
        restUndoubled, renderPhaseMarkers]

private theorem renderPhaseParityEntries_eq_markers_of_noDoubled
    {entries : List PhaseParityEntry}
    (noneDoubled : hasDoubledPhase entries = false) :
    renderPhaseParityEntries entries = renderPhaseMarkers entries := by
  exact renderLeeZhang23_3Aux_eq_markers_of_noDoubled
    [] entries noneDoubled

/-- If the aligned entry stream has no doubled phase, every source parser
gap is empty. -/
private theorem sourceGapSeconds_empty_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) =
        false) :
    forall block,
      block ∈ gapBlocksList word.toList -> block.seconds = [] := by
  intro block member
  apply Classical.byContradiction
  intro blockNonempty
  have phaseMember :
      phaseOfGapBlock block ∈ phaseProfile word := by
    unfold phaseProfile
    rw [phaseGapProfileAgreement]
    exact List.mem_map.mpr ⟨block, member, rfl⟩
  have entryPhaseMember :
      phaseOfGapBlock block ∈
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)).map
            (fun entry => entry.phase) := by
    rw [phases_phaseParityEntries_word]
    exact phaseMember
  rcases List.mem_map.mp entryPhaseMember with
    ⟨entry, entryMember, entryPhase⟩
  have entryUndoubled : entry.phase.doubled = false :=
    (hasDoubledPhase_eq_false_iff _).mp noneDoubled
      entry entryMember
  have blockDoubled : (phaseOfGapBlock block).doubled = true := by
    simp [phaseOfGapBlock, blockNonempty]
  have entryDoubled : entry.phase.doubled = true := by
    rw [entryPhase]
    exact blockDoubled
  rw [entryUndoubled] at entryDoubled
  contradiction

private theorem sourceList_eq_phaseLabels_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) =
        false) :
    word.toList = phaseLabels (phaseProfile word) := by
  let blocks := gapBlocksList word.toList
  have gapsEmpty :
      forall block, block ∈ blocks -> block.seconds = [] := by
    intro block member
    exact sourceGapSeconds_empty_of_noDoubled
      word noneDoubled block member
  calc
    word.toList = renderGapBlocks blocks := by
      simpa [blocks] using (render_gapBlocksList word.toList).symm
    _ = gapBlockMarkers blocks :=
      renderGapBlocks_eq_markers_of_seconds_empty blocks gapsEmpty
    _ = phaseLabels (phaseProfile word) := by
      unfold phaseProfile
      simpa [blocks] using
        (phaseLabels_phaseProfileList_eq_gapBlockMarkers
          word.toList).symm

private theorem canonicalList_eq_phaseLabels_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) =
        false) :
    canonicalPhaseParityList word =
      phaseLabels (phaseProfile word) := by
  let entries :=
    phaseParityEntries
      (phaseProfile word) (phaseParityCoordinates word)
  have rendered :=
    renderPhaseParityEntries_eq_markers_of_noDoubled
      (entries := entries) noneDoubled
  have aligned := congrArg (List.map Phase.label)
    (phases_phaseParityEntries_word word)
  unfold canonicalPhaseParityList renderPhaseParityKeyList
    phaseParityKey
  change renderPhaseParityEntries entries =
    phaseLabels (phaseProfile word)
  rw [rendered, renderPhaseMarkers_eq_map_labels]
  simpa [entries, phaseLabels, List.map_map] using aligned

/-- A source with no doubled phase is already the literal phase-parity
renderer, so this entire branch is reflexive. -/
theorem hullListDerivesCanonical_of_noDoubled
    (word : Word Nat)
    (noneDoubled :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) =
        false) :
    HullListDerives word.toList
      (canonicalPhaseParityList word) := by
  have sourceShape :=
    sourceList_eq_phaseLabels_of_noDoubled word noneDoubled
  have targetShape :=
    canonicalList_eq_phaseLabels_of_noDoubled word noneDoubled
  rw [sourceShape, targetShape]
  exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _

/-! ## Exact active-branch boundary -/

/-- The literal intermediate list produced by the direct B15 gap sweep.
The final nonempty gap has been rotated to expose `anchor`, the final phase
marker has acquired an explicit square, and all earlier old-letter gaps have
been moved across that square with their exact emitted debt retained. -/
def activeSkeletonList
    (before : List GapBlock) (last : GapBlock) (after : List GapBlock)
    (anchor : Nat) (remaining : List Nat) : List Nat :=
  SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves.renderSweptPriorBlocks
      before ++
    [last.marker] ++ remaining ++ [anchor, last.marker, last.marker] ++
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves.sweptPriorDebt
      before ++
    gapBlockMarkers after

/-- The exact last-doubled split of the canonical Lee--Zhang renderer. -/
def activeCanonicalSplitList
    (before : List PhaseParityEntry) (last : PhaseParityEntry)
    (after : List PhaseParityEntry) : List Nat :=
  renderGapBlocks (canonicalPriorGapBlocks before) ++
    renderGapBlocks
      [lastDoubledGapBlock (collectParityDebt before) last] ++
    renderGapBlocks (markerOnlyGapBlocks after)

/-- Closed active-branch front half.  This theorem joins three independently
proved interfaces:

* the source parser's final nonempty-gap split;
* the aligned phase/parity-entry split and canonical target shape; and
* the direct B15 gap sweep ending at an explicit terminal square.

Consequently the only remaining active obligation is a derivation from
`activeSkeletonList` to `activeCanonicalSplitList`; no parser, invariant, or
word/list conversion debt remains hidden in that obligation. -/
theorem hullListDerivesActiveSkeleton
    (word : Word Nat)
    (active :
      hasDoubledPhase
          (phaseParityEntries
            (phaseProfile word) (phaseParityCoordinates word)) = true) :
    exists (beforeBlocks : List GapBlock) (lastBlock : GapBlock)
        (afterBlocks : List GapBlock)
        (beforeEntries : List PhaseParityEntry)
        (lastEntry : PhaseParityEntry)
        (afterEntries : List PhaseParityEntry)
        (anchor : Nat) (remaining : List Nat),
      gapBlocksList word.toList =
          beforeBlocks ++ lastBlock :: afterBlocks /\
      lastBlock.seconds = anchor :: remaining /\
      lastBlock.seconds ≠ [] /\
      (forall block, block ∈ afterBlocks -> block.seconds = []) /\
      phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word) =
        beforeEntries ++ lastEntry :: afterEntries /\
      beforeEntries.map (fun entry => entry.phase) =
        beforeBlocks.map phaseOfGapBlock /\
      lastEntry.phase = phaseOfGapBlock lastBlock /\
      afterEntries.map (fun entry => entry.phase) =
        afterBlocks.map phaseOfGapBlock /\
      lastEntry.phase.doubled = true /\
      (forall entry, entry ∈ afterEntries ->
        entry.phase.doubled = false) /\
      canonicalPhaseParityList word =
        activeCanonicalSplitList beforeEntries lastEntry afterEntries /\
      HullListDerives word.toList
        (activeSkeletonList
          beforeBlocks lastBlock afterBlocks anchor remaining) := by
  have sourceActive :
      phaseListHasDoubled (phaseProfileList word.toList) = true := by
    change phaseListHasDoubled (phaseProfile word) = true
    rw [← SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.hasDoubledPhase_phaseParityEntries_word]
    exact active
  obtain ⟨beforeBlocks, lastBlock, afterBlocks, anchor, remaining,
      sourceSplit, lastShape, lastNonempty, afterEmpty, swept⟩ :=
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityGapMoves.hullListDerivesParsedListLastDoubledSkeleton
      [] [] word.toList sourceActive
  obtain ⟨beforeEntries, lastEntry, afterEntries,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, afterUndoubled⟩ :=
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.entrySplit_of_source_lastNonemptyGap
      word sourceSplit lastNonempty afterEmpty
  have canonicalShape :
      canonicalPhaseParityList word =
        activeCanonicalSplitList beforeEntries lastEntry afterEntries := by
    rw [← render_canonicalPhaseParityGapBlocks]
    change
      renderGapBlocks
          (canonicalGapBlocks
            (phaseParityEntries
              (phaseProfile word) (phaseParityCoordinates word))) = _
    rw [entrySplit]
    exact
      SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockAccounting.render_canonicalGapBlocks_lastDoubled_shape
        beforeEntries lastEntry afterEntries lastDoubled afterUndoubled
  refine
    ⟨beforeBlocks, lastBlock, afterBlocks,
      beforeEntries, lastEntry, afterEntries, anchor, remaining,
      sourceSplit, lastShape, lastNonempty, afterEmpty,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, afterUndoubled, canonicalShape, ?_⟩
  simpa [activeSkeletonList, List.append_assoc] using swept

/-! ## Active list contract and word-level assembly -/

/-- The sole remaining constructive obligation.  The hypothesis selects the
branch containing a last nonempty first-occurrence gap. -/
def ActivePhaseParityListNormalization : Prop :=
  forall word : Word Nat,
    hasDoubledPhase
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) = true ->
      HullListDerives word.toList
        (canonicalPhaseParityList word)

/-- The exact, strictly smaller constructive debt left after
`hullListDerivesActiveSkeleton`.  In addition to the displayed source and
target lists, the contract exposes every source/entry alignment fact needed
to instantiate the power, exceptional-parity, and Condition-V moves. -/
def ActivePhaseParitySkeletonCompletion : Prop :=
  forall (word : Word Nat)
      (beforeBlocks : List GapBlock) (lastBlock : GapBlock)
      (afterBlocks : List GapBlock)
      (beforeEntries : List PhaseParityEntry)
      (lastEntry : PhaseParityEntry)
      (afterEntries : List PhaseParityEntry)
      (anchor : Nat) (remaining : List Nat),
    gapBlocksList word.toList =
        beforeBlocks ++ lastBlock :: afterBlocks ->
    lastBlock.seconds = anchor :: remaining ->
    lastBlock.seconds ≠ [] ->
    (forall block, block ∈ afterBlocks -> block.seconds = []) ->
    phaseParityEntries
        (phaseProfile word) (phaseParityCoordinates word) =
      beforeEntries ++ lastEntry :: afterEntries ->
    beforeEntries.map (fun entry => entry.phase) =
      beforeBlocks.map phaseOfGapBlock ->
    lastEntry.phase = phaseOfGapBlock lastBlock ->
    afterEntries.map (fun entry => entry.phase) =
      afterBlocks.map phaseOfGapBlock ->
    lastEntry.phase.doubled = true ->
    (forall entry, entry ∈ afterEntries ->
      entry.phase.doubled = false) ->
    HullListDerives
      (activeSkeletonList
        beforeBlocks lastBlock afterBlocks anchor remaining)
      (activeCanonicalSplitList
        beforeEntries lastEntry afterEntries)

/-- The explicit post-sweep assembly discharges the complete active-skeleton
contract using only the literal Proposition 23.1 basis. -/
theorem activePhaseParitySkeletonCompletion_proved :
    ActivePhaseParitySkeletonCompletion := by
  intro word beforeBlocks lastBlock afterBlocks
    beforeEntries lastEntry afterEntries anchor remaining
    sourceSplit lastShape lastNonempty afterEmpty entrySplit
    beforeAligned lastAligned afterAligned lastDoubled afterUndoubled
  simpa [activeSkeletonList, activeCanonicalSplitList] using
    SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityPowerNormalization.hullListDerivesPostSweepCanonical
      word beforeBlocks lastBlock afterBlocks
      beforeEntries lastEntry afterEntries anchor remaining
      sourceSplit lastShape lastNonempty afterEmpty entrySplit
      beforeAligned lastAligned afterAligned lastDoubled afterUndoubled

/-- Supplying only the post-sweep skeleton completion closes the original
active list-normalization contract. -/
theorem activePhaseParityListNormalization_of_skeletonCompletion
    (complete : ActivePhaseParitySkeletonCompletion) :
    ActivePhaseParityListNormalization := by
  intro word active
  obtain ⟨beforeBlocks, lastBlock, afterBlocks,
      beforeEntries, lastEntry, afterEntries, anchor, remaining,
      sourceSplit, lastShape, lastNonempty, afterEmpty,
      entrySplit, beforeAligned, lastAligned, afterAligned,
      lastDoubled, afterUndoubled, canonicalShape, swept⟩ :=
    hullListDerivesActiveSkeleton word active
  have finished :=
    complete word
      beforeBlocks lastBlock afterBlocks
      beforeEntries lastEntry afterEntries anchor remaining
      sourceSplit lastShape lastNonempty afterEmpty
      entrySplit beforeAligned lastAligned afterAligned
      lastDoubled afterUndoubled
  rw [canonicalShape]
  exact swept.trans finished

/-- Total one-sided list normalization, packaged independently of the
two-sided endpoint. -/
def PhaseParityListNormalization : Prop :=
  forall word : Word Nat,
    HullListDerives word.toList
      (canonicalPhaseParityList word)

theorem phaseParityListNormalization_of_active
    (active : ActivePhaseParityListNormalization) :
    PhaseParityListNormalization := by
  intro word
  cases doubled :
      hasDoubledPhase
        (phaseParityEntries
          (phaseProfile word) (phaseParityCoordinates word)) with
  | false =>
      exact hullListDerivesCanonical_of_noDoubled word doubled
  | true =>
      exact active word doubled

theorem phaseParityListNormalization_of_skeletonCompletion
    (complete : ActivePhaseParitySkeletonCompletion) :
    PhaseParityListNormalization :=
  phaseParityListNormalization_of_active
    (activePhaseParityListNormalization_of_skeletonCompletion complete)

/-- Convert the list-level renderer derivation into a derivation between the
source word and the nonempty rendered word. -/
theorem derivesCanonicalPhaseParityWord_of_list
    (word : Word Nat)
    (normalized :
      HullListDerives word.toList
        (canonicalPhaseParityList word)) :
    Derives basis word (canonicalPhaseParityWord word) := by
  cases word with
  | mk head tail =>
      have listed :
          HullListDerives (head :: tail)
            (canonicalPhaseParityList (Word.mk head tail)) := by
        simpa [Word.toList] using normalized
      obtain ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.from_cons listed
      have targetWordEq :
          SemigroupBasis.CoRoots.S5_107.listWordOfCons
              targetHead targetTail =
            canonicalPhaseParityWord (Word.mk head tail) := by
        apply Word.toList_injective
        rw [toList_canonicalPhaseParityWord]
        simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
          targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
        wordDerivation

theorem derivesCanonicalPhaseParityWord_of_normalization
    (normalize : PhaseParityListNormalization)
    (word : Word Nat) :
    Derives basis word (canonicalPhaseParityWord word) :=
  derivesCanonicalPhaseParityWord_of_list word (normalize word)

/-- Once the one-sided B15 normalizer is supplied, equal phase profiles and
pointwise count parity give a direct two-sided derivation. -/
theorem phaseParityNormalization_of_oneSided
    (normalize : PhaseParityListNormalization)
    {left right : Word Nat}
    (phase : S5_831.phaseProfile left = S5_831.phaseProfile right)
    (parity : forall z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives
      SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis
      left right := by
  have leftNormal :=
    derivesCanonicalPhaseParityWord_of_normalization
      normalize left
  have rightNormal :=
    derivesCanonicalPhaseParityWord_of_normalization
      normalize right
  have sameCanonical :=
    canonicalPhaseParityWord_eq_of_invariants phase parity
  exact leftNormal.trans <| by
    simpa [sameCanonical] using rightNormal.symm

/-- Equivalent assembly from just the genuinely active branch. -/
theorem phaseParityNormalization_of_active
    (active : ActivePhaseParityListNormalization)
    {left right : Word Nat}
    (phase : S5_831.phaseProfile left = S5_831.phaseProfile right)
    (parity : forall z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives
      SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis
      left right :=
  phaseParityNormalization_of_oneSided
    (phaseParityListNormalization_of_active active) phase parity

/-- Exact two-sided assembly from the reduced post-sweep obligation.  This is
the closest closed predecessor of the required unconditional theorem: no
invariant or word-level premise beyond the final skeleton completion remains. -/
theorem phaseParityNormalization_of_skeletonCompletion
    (complete : ActivePhaseParitySkeletonCompletion)
    {left right : Word Nat}
    (phase : S5_831.phaseProfile left = S5_831.phaseProfile right)
    (parity : forall z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives
      SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis
      left right :=
  phaseParityNormalization_of_oneSided
    (phaseParityListNormalization_of_skeletonCompletion complete)
    phase parity

/-- Unconditional phase-parity normalization for the literal fifteen-law
Proposition 23.1 basis. -/
theorem phaseParityNormalization
    {left right : Word Nat}
    (phase : S5_831.phaseProfile left = S5_831.phaseProfile right)
    (parity : forall z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives
      SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis
      left right :=
  phaseParityNormalization_of_skeletonCompletion
    activePhaseParitySkeletonCompletion_proved phase parity

end Order6Hull23_1PhaseParityNormalization
end CoRoots
end SemigroupBasis
