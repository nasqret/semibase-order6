import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves
import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityMoves
import SemigroupBasis.CoRoots.S5_870GapBlocks

/-!
# Hull 23.1 gap sweep

This module formalizes the first structural half of Lee--Zhang Lemma 23.5
directly over the fifteen identities of Proposition 23.1.  A well-formed
first-occurrence gap is first permuted, using (23.1e), into copies of its
marker followed by old-letter debt.  The old-letter debt is then moved across
an explicit terminal square by (23.1f).  The terminal square itself is exposed
at the final nonempty gap by reversing (23.1b), exactly as in the published
proof.

No derivational theorem from the Proposition 21.1 hull is imported.  The
functions below retain the literal multiplicity accounting of every Balance
step; in particular, the debt emitted after the square is not silently
identified modulo parity.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityGapMoves

open SemigroupBasis.CoRoots.S5_870
open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityBlockFacts
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityMoves

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

abbrev GapBlock := FirstOccurrenceGapBlock

/-! ## Exact marker/debt partition of one gap -/

/-- The old-letter part of a gap after all copies of its own marker have been
removed.  Well-formedness implies that every letter in this list was witnessed
strictly before the current marker. -/
def gapDebt (block : GapBlock) : List Nat :=
  block.seconds.filter (fun letter => letter != block.marker)

/-- Marker power obtained by grouping the marker copies already present in a
gap.  The final singleton is the first occurrence that starts the block; this
append presentation is chosen so that the following Balance induction can use
that singleton as its displayed active marker. -/
def groupedGapMarkerPower (block : GapBlock) : List Nat :=
  List.replicate (block.seconds.count block.marker) block.marker ++
    [block.marker]

/-- Marker power left before the terminal square after all non-marker debt in
the block has been swept. -/
def sweptGapMarkerPower (block : GapBlock) : List Nat :=
  List.replicate (block.seconds.count block.marker) block.marker ++
    List.replicate ((gapDebt block).length + 1) block.marker

/-- Exact marker/debt contribution emitted after the terminal square by one
block. -/
def sweptGapDebt (block : GapBlock) : List Nat :=
  List.replicate (gapDebt block).length block.marker ++ gapDebt block

private theorem replicate_add_gap
    (left right : Nat) (letter : Nat) :
    List.replicate (left + right) letter =
      List.replicate left letter ++ List.replicate right letter := by
  induction left with
  | zero => simp
  | succ copies induction =>
      have shift : copies + 1 + right = (copies + right) + 1 := by
        omega
      rw [shift, List.replicate_succ, List.replicate_succ,
        List.cons_append, induction]

private theorem perm_cons_to_end (letter : Nat) :
    forall letters : List Nat,
      (letter :: letters).Perm (letters ++ [letter])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.swap head letter tail).trans <|
        List.Perm.cons head (perm_cons_to_end letter tail)

private theorem replicate_append_singleton (letter : Nat) :
    forall copies : Nat,
      List.replicate copies letter ++ [letter] =
        letter :: List.replicate copies letter
  | 0 => rfl
  | copies + 1 => by
      simp [List.replicate_succ,
        replicate_append_singleton letter copies]

private theorem letters_perm_markerCopies_append_debt
    (marker : Nat) :
    forall letters : List Nat,
      letters.Perm
        (List.replicate (letters.count marker) marker ++
          letters.filter (fun letter => letter != marker))
  | [] => List.Perm.refl _
  | head :: rest => by
      by_cases equal : head = marker
      · subst head
        simpa [List.replicate_succ] using
          List.Perm.cons marker
            (letters_perm_markerCopies_append_debt marker rest)
      · have withHead :=
          List.Perm.cons head
            (letters_perm_markerCopies_append_debt marker rest)
        have moveHead :=
          List.Perm.append_right
            (rest.filter (fun letter => letter != marker))
            (perm_cons_to_end head
              (List.replicate (rest.count marker) marker))
        have moved :
            (head ::
                (List.replicate (rest.count marker) marker ++
                  rest.filter (fun letter => letter != marker))).Perm
              (List.replicate (rest.count marker) marker ++
                head :: rest.filter (fun letter => letter != marker)) := by
          simpa [List.append_assoc] using moveHead
        simpa [equal] using withHead.trans moved

/-- Exact permutation accounting for the marker/debt partition of a gap. -/
theorem gapSeconds_perm_markerCopies_append_debt
    (block : GapBlock) :
    block.seconds.Perm
      (List.replicate (block.seconds.count block.marker) block.marker ++
        gapDebt block) := by
  exact letters_perm_markerCopies_append_debt
    block.marker block.seconds

/-- The marker copies and non-marker debt partition the original gap without
loss or duplication. -/
theorem gapMarkerCount_add_debtLength
    (block : GapBlock) :
    block.seconds.count block.marker + (gapDebt block).length =
      block.seconds.length := by
  have lengths :=
    (gapSeconds_perm_markerCopies_append_debt block).length_eq
  simpa using lengths.symm

/-- The leading power left by a swept gap contains exactly one marker for the
first occurrence and one for every letter of the original seconds field. -/
theorem sweptGapMarkerPower_eq_replicate (block : GapBlock) :
    sweptGapMarkerPower block =
      List.replicate (block.seconds.length + 1) block.marker := by
  simp only [sweptGapMarkerPower]
  rw [← replicate_add_gap, ← Nat.add_assoc,
    gapMarkerCount_add_debtLength]

theorem sweptGapMarkerPower_length (block : GapBlock) :
    (sweptGapMarkerPower block).length = block.seconds.length + 1 := by
  have accounting := gapMarkerCount_add_debtLength block
  simp only [sweptGapMarkerPower, List.length_append,
    List.length_replicate]
  omega

theorem sweptGapDebt_length (block : GapBlock) :
    (sweptGapDebt block).length = 2 * (gapDebt block).length := by
  simp only [sweptGapDebt, List.length_append,
    List.length_replicate]
  omega

/-- Group all later copies of the block marker immediately after its first
occurrence.  Every other gap letter already has a witness in the fixed prefix,
so (23.1e) realizes the exact marker/debt permutation. -/
theorem hullListDerivesGroupGapMarkerCopies
    (stem suffix : List Nat) (block : GapBlock)
    (secondsSeen :
      forall letter, letter ∈ block.seconds ->
        letter ∈ stem ++ [block.marker]) :
    HullListDerives
      (stem ++ [block.marker] ++ block.seconds ++ suffix)
      (stem ++ groupedGapMarkerPower block ++ gapDebt block ++ suffix) := by
  have grouped :=
    hullListDerivesWitnessedTailPermutation
      (stem ++ [block.marker]) suffix secondsSeen
      (gapSeconds_perm_markerCopies_append_debt block)
  simpa [groupedGapMarkerPower,
    replicate_append_singleton, List.append_assoc] using grouped

/-- Render every block after its own marker copies have been grouped and its
non-marker old-letter debt has been retained verbatim. -/
def renderGroupedGapBlocks : List GapBlock -> List Nat
  | [] => []
  | block :: rest =>
      groupedGapMarkerPower block ++ gapDebt block ++
        renderGroupedGapBlocks rest

/-- Simultaneously realize the marker/debt partition of every gap in a
well-formed decomposition.  This is the direct block-level formalization of
the first permutation step in Lee--Zhang Lemma 23.5. -/
theorem hullListDerivesGroupWellFormedGaps
    (stem suffix : List Nat)
    {seen : List Nat} {blocks : List GapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (historicalSeen :
      forall letter, letter ∈ seen -> letter ∈ stem) :
    HullListDerives
      (stem ++ renderGapBlocks blocks ++ suffix)
      (stem ++ renderGroupedGapBlocks blocks ++ suffix) := by
  induction formed generalizing stem suffix with
  | nil seen =>
      simpa [renderGapBlocks, renderGroupedGapBlocks] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (stem ++ suffix))
  | cons seen block rest markerFresh secondsSeen tail tailInduction =>
      have currentSecondsSeen :
          forall letter, letter ∈ block.seconds ->
            letter ∈ stem ++ [block.marker] := by
        intro letter member
        rcases List.mem_cons.mp (secondsSeen letter member) with
          atMarker | old
        · subst letter
          simp
        · have inStem := historicalSeen letter old
          simp [inStem]
      have grouped :=
        hullListDerivesGroupGapMarkerCopies
          stem (renderGapBlocks rest ++ suffix)
          block currentSecondsSeen
      have groupedFromHead :
          HullListDerives
            (stem ++ [block.marker] ++ block.seconds ++
              renderGapBlocks rest ++ suffix)
            (stem ++ groupedGapMarkerPower block ++ gapDebt block ++
              renderGapBlocks rest ++ suffix) := by
        simpa [List.append_assoc] using grouped
      have tailHistorical :
          forall letter, letter ∈ block.marker :: seen ->
            letter ∈
              stem ++ groupedGapMarkerPower block ++ gapDebt block := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | old
        · subst letter
          simp [groupedGapMarkerPower]
        · have inStem := historicalSeen letter old
          simp [inStem]
      have groupedTail :=
        tailInduction
          (stem :=
            stem ++ groupedGapMarkerPower block ++ gapDebt block)
          (suffix := suffix) tailHistorical
      have groupedTailFromHead :
          HullListDerives
            (stem ++ groupedGapMarkerPower block ++ gapDebt block ++
              renderGapBlocks rest ++ suffix)
            (stem ++ groupedGapMarkerPower block ++ gapDebt block ++
              renderGroupedGapBlocks rest ++ suffix) := by
        simpa [List.append_assoc] using groupedTail
      have combined := groupedFromHead.trans groupedTailFromHead
      simpa [renderGapBlocks, renderGroupedGapBlocks,
        List.append_assoc] using combined

/-! ## One block across a terminal square -/

/-- Published Lemma 23.5's one-gap move.  Marker copies are grouped by
(23.1e), and every non-marker debt letter is moved by (23.1f).  The result
records both copies of the active marker introduced per debt letter: one in
the leading power and one in the terminal debt. -/
theorem hullListDerivesSweepGapAcrossTerminalSquare
    (stem middle suffix : List Nat) (block : GapBlock)
    (squareMarker : Nat)
    (debtSeen :
      forall letter, letter ∈ gapDebt block -> letter ∈ stem) :
    HullListDerives
      (stem ++ [block.marker] ++ block.seconds ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (stem ++ sweptGapMarkerPower block ++ middle ++
        [squareMarker, squareMarker] ++ sweptGapDebt block ++ suffix) := by
  have secondsSeen :
      forall letter, letter ∈ block.seconds ->
        letter ∈ stem ++ [block.marker] := by
    intro letter member
    by_cases equal : letter = block.marker
    · subst letter
      simp
    · have inDebt : letter ∈ gapDebt block := by
        exact List.mem_filter.mpr <| by
          constructor
          · exact member
          · simpa using equal
      exact List.mem_append.mpr <| Or.inl <| debtSeen letter inDebt
  have grouped :=
    hullListDerivesGroupGapMarkerCopies
      stem (middle ++ [squareMarker, squareMarker] ++ suffix)
      block secondsSeen
  by_cases debtEmpty : gapDebt block = []
  · simpa [sweptGapMarkerPower, sweptGapDebt,
      groupedGapMarkerPower, debtEmpty, List.append_assoc] using grouped
  · have moved :=
      hullListDerivesMoveWitnessedDebtBlockCanonical
        (stem ++
          List.replicate
            (block.seconds.count block.marker) block.marker)
        middle suffix (gapDebt block) block.marker squareMarker
        debtEmpty
        (by
          intro letter member
          exact List.mem_append.mpr <|
            Or.inl <| debtSeen letter member)
    have movedFromGrouped :
        HullListDerives
          (stem ++ groupedGapMarkerPower block ++ gapDebt block ++ middle ++
            [squareMarker, squareMarker] ++ suffix)
          (stem ++ sweptGapMarkerPower block ++ middle ++
            [squareMarker, squareMarker] ++ sweptGapDebt block ++ suffix) := by
      simpa [groupedGapMarkerPower, sweptGapMarkerPower,
        sweptGapDebt, List.append_assoc] using moved
    have groupedForMove :
        HullListDerives
          (stem ++ [block.marker] ++ block.seconds ++ middle ++
            [squareMarker, squareMarker] ++ suffix)
          (stem ++ groupedGapMarkerPower block ++ gapDebt block ++ middle ++
            [squareMarker, squareMarker] ++ suffix) := by
      simpa [List.append_assoc] using grouped
    exact groupedForMove.trans movedFromGrouped

/-! ## Iteration over all blocks before the final doubled block -/

/-- Leading marker powers after sweeping a list of pre-final blocks. -/
def renderSweptPriorBlocks : List GapBlock -> List Nat
  | [] => []
  | block :: rest =>
      sweptGapMarkerPower block ++ renderSweptPriorBlocks rest

/-- Terminal debt after sweeping pre-final blocks.  The induction processes
the tail first, so these contributions remain in the original marker order,
as in the displayed product in Lee--Zhang Lemma 23.5. -/
def sweptPriorDebt : List GapBlock -> List Nat
  | [] => []
  | block :: rest => sweptGapDebt block ++ sweptPriorDebt rest

/-- Sweep every old-letter gap in a well-formed pre-final block list across a
fixed terminal square.  The theorem is fully contextual and keeps the exact
prefix, middle, suffix, marker powers, and emitted debt visible. -/
theorem hullListDerivesSweepPriorBlocks
    (stem middle suffix : List Nat) (squareMarker : Nat)
    {seen : List Nat} {blocks : List GapBlock}
    (formed : GapBlocksWellFormed seen blocks)
    (historicalSeen :
      forall letter, letter ∈ seen -> letter ∈ stem) :
    HullListDerives
      (stem ++ renderGapBlocks blocks ++ middle ++
        [squareMarker, squareMarker] ++ suffix)
      (stem ++ renderSweptPriorBlocks blocks ++ middle ++
        [squareMarker, squareMarker] ++ sweptPriorDebt blocks ++ suffix) := by
  induction formed generalizing stem suffix with
  | nil seen =>
      simpa [renderGapBlocks, renderSweptPriorBlocks,
        sweptPriorDebt, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (stem ++ middle ++ [squareMarker, squareMarker] ++ suffix))
  | cons seen block rest markerFresh secondsSeen tail tailInduction =>
      have tailHistorical :
          forall letter, letter ∈ block.marker :: seen ->
            letter ∈ stem ++ [block.marker] ++ block.seconds := by
        intro letter member
        rcases List.mem_cons.mp member with atMarker | old
        · subst letter
          simp
        · have inStem := historicalSeen letter old
          simp [inStem]
      have tailSweep :=
        tailInduction
          (stem := stem ++ [block.marker] ++ block.seconds)
          (suffix := suffix) tailHistorical
      have debtSeen :
          forall letter, letter ∈ gapDebt block -> letter ∈ stem := by
        intro letter member
        rcases List.mem_filter.mp member with
          ⟨inSeconds, different⟩
        have notMarker : letter ≠ block.marker := by
          simpa using different
        rcases List.mem_cons.mp (secondsSeen letter inSeconds) with
          atMarker | old
        · exact False.elim <| notMarker atMarker
        · exact historicalSeen letter old
      have headSweep :=
        hullListDerivesSweepGapAcrossTerminalSquare
          stem (renderSweptPriorBlocks rest ++ middle)
          (sweptPriorDebt rest ++ suffix) block squareMarker debtSeen
      have headSweepFromTail :
          HullListDerives
            ((stem ++ [block.marker] ++ block.seconds) ++
              renderSweptPriorBlocks rest ++ middle ++
              [squareMarker, squareMarker] ++
              sweptPriorDebt rest ++ suffix)
            (stem ++ sweptGapMarkerPower block ++
              renderSweptPriorBlocks rest ++ middle ++
              [squareMarker, squareMarker] ++
              sweptGapDebt block ++ sweptPriorDebt rest ++ suffix) := by
        simpa [List.append_assoc] using headSweep
      have tailSweepToHead :
          HullListDerives
            (stem ++ [block.marker] ++ block.seconds ++
              renderGapBlocks rest ++ middle ++
              [squareMarker, squareMarker] ++ suffix)
            ((stem ++ [block.marker] ++ block.seconds) ++
              renderSweptPriorBlocks rest ++ middle ++
              [squareMarker, squareMarker] ++
              sweptPriorDebt rest ++ suffix) := by
        simpa [List.append_assoc] using tailSweep
      have combined := tailSweepToHead.trans headSweepFromTail
      simpa [renderGapBlocks, renderSweptPriorBlocks,
        sweptPriorDebt, List.append_assoc] using combined

/-! ## The final nonempty gap and its terminal square -/

/-- Reverse (23.1b) at a later witnessed occurrence, adjoining the two copies
used as the terminal square in the published proof. -/
theorem hullListDerivesExpandWitnessedOccurrence
    (witnesses between suffix : List Nat) (letter : Nat)
    (witnessed : letter ∈ witnesses) :
    HullListDerives
      (witnesses ++ between ++ [letter] ++ suffix)
      (witnesses ++ between ++ [letter, letter, letter] ++ suffix) := by
  obtain ⟨before, after, witnessShape⟩ :=
    List.mem_iff_append.mp witnessed
  simpa [witnessShape, List.append_assoc] using
    (hullListDerivesPowerContract
      before suffix (after ++ between) letter).symm

/-- Rotate the head of a nonempty final gap to its end by (23.1e), reverse
(23.1b) there, and use (23.1c) backwards to transfer the two new copies to
the final block marker.  The result ends in a literal square of that marker,
while retaining one occurrence of the selected old-letter anchor. -/
theorem hullListDerivesExposeLastGapSquare
    (witnesses suffix : List Nat) (block : GapBlock)
    (gapNonempty : block.seconds ≠ [])
    (secondsSeen :
      forall letter, letter ∈ block.seconds ->
        letter ∈ witnesses ++ [block.marker]) :
    exists anchor remaining,
      block.seconds = anchor :: remaining /\
      anchor ∈ block.seconds /\
      HullListDerives
        (witnesses ++ [block.marker] ++ block.seconds ++ suffix)
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor, block.marker, block.marker] ++ suffix) := by
  obtain ⟨anchor, remaining, secondsShape⟩ :
      ∃ anchor remaining, block.seconds = anchor :: remaining := by
    cases split : block.seconds with
    | nil =>
        exact False.elim <| gapNonempty split
    | cons anchor remaining =>
        exact ⟨anchor, remaining, rfl⟩
  rw [secondsShape] at secondsSeen ⊢
  have anchorInSeconds : anchor ∈ anchor :: remaining :=
    List.Mem.head remaining
  have anchorWitnessed :
      anchor ∈ witnesses ++ [block.marker] :=
    secondsSeen anchor anchorInSeconds
  have rotated :=
    hullListDerivesWitnessedTailPermutation
      (witnesses ++ [block.marker]) suffix secondsSeen
      (perm_cons_to_end anchor remaining)
  have expanded :=
    hullListDerivesExpandWitnessedOccurrence
      (witnesses ++ [block.marker]) remaining suffix
      anchor anchorWitnessed
  have markerSquare :=
    (hullListDerivesParityTransfer
      witnesses suffix remaining block.marker anchor).symm
  refine ⟨anchor, remaining, rfl, anchorInSeconds, ?_⟩
  have rotatedToEnd :
      HullListDerives
        (witnesses ++ [block.marker] ++
          (anchor :: remaining) ++ suffix)
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor] ++ suffix) := by
    simpa [List.append_assoc] using rotated
  have expandedFromRotated :
      HullListDerives
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor] ++ suffix)
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor, anchor, anchor] ++ suffix) := by
    simpa [List.append_assoc] using expanded
  have markerSquareFromExpanded :
      HullListDerives
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor, anchor, anchor] ++ suffix)
        (witnesses ++ [block.marker] ++ remaining ++
          [anchor, block.marker, block.marker] ++ suffix) := by
    simpa [List.append_assoc] using markerSquare
  exact rotatedToEnd.trans <|
    expandedFromRotated.trans markerSquareFromExpanded

/-- Close the terminal marker square once the retained anchor has an earlier
witness.  First (23.1c) transfers the marker pair to the anchor; then (23.1b)
contracts the resulting anchor cube. -/
theorem hullListDerivesCloseExposedLastGapSquare
    (witnesses middle suffix : List Nat) (marker anchor : Nat)
    (anchorSeen : anchor ∈ witnesses ++ [marker]) :
    HullListDerives
      (witnesses ++ [marker] ++ middle ++
        [anchor, marker, marker] ++ suffix)
      (witnesses ++ [marker] ++ middle ++ [anchor] ++ suffix) := by
  have transferred :=
    hullListDerivesParityTransfer
      witnesses suffix middle marker anchor
  obtain ⟨before, after, witnessShape⟩ :=
    List.mem_iff_append.mp anchorSeen
  have contracted :=
    hullListDerivesPowerContract
      before suffix (after ++ middle) anchor
  have transferredToAnchorCube :
      HullListDerives
        (witnesses ++ [marker] ++ middle ++
          [anchor, marker, marker] ++ suffix)
        (witnesses ++ [marker] ++ middle ++
          [anchor, anchor, anchor] ++ suffix) := by
    simpa [List.append_assoc] using transferred
  have contractedFromAnchorCube :
      HullListDerives
        (witnesses ++ [marker] ++ middle ++
          [anchor, anchor, anchor] ++ suffix)
        (witnesses ++ [marker] ++ middle ++ [anchor] ++ suffix) := by
    simpa [witnessShape, List.append_assoc] using contracted
  exact transferredToAnchorCube.trans contractedFromAnchorCube

/-! ## Basis-independent list support used by the final assembly -/

theorem renderGapBlocks_append (left right : List GapBlock) :
    renderGapBlocks (left ++ right) =
      renderGapBlocks left ++ renderGapBlocks right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [renderGapBlocks, induction, List.append_assoc]

def seenAfterGapBlocks
    (seen : List Nat) (blocks : List GapBlock) : List Nat :=
  (gapBlockMarkers blocks).reverse ++ seen

/-- Every prior first-occurrence marker remains present in the exact swept
prefix. -/
theorem gapBlockMarker_mem_renderSweptPriorBlocks
    (letter : Nat) :
    forall {blocks : List GapBlock},
      letter ∈ gapBlockMarkers blocks ->
        letter ∈ renderSweptPriorBlocks blocks
  | [], member => by
      simp [gapBlockMarkers] at member
  | block :: rest, member => by
      simp only [gapBlockMarkers, List.map_cons, List.mem_cons] at member
      rcases member with atMarker | later
      · subst letter
        simp [renderSweptPriorBlocks,
          sweptGapMarkerPower_eq_replicate]
      · exact List.mem_append.mpr <| Or.inr <|
          gapBlockMarker_mem_renderSweptPriorBlocks letter later

theorem gapBlocksWellFormed_append
    {seen : List Nat} {left right : List GapBlock}
    (formed : GapBlocksWellFormed seen (left ++ right)) :
    GapBlocksWellFormed seen left /\
      GapBlocksWellFormed (seenAfterGapBlocks seen left) right := by
  induction left generalizing seen with
  | nil =>
      exact
        ⟨GapBlocksWellFormed.nil seen,
          by simpa [seenAfterGapBlocks] using formed⟩
  | cons block rest induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          obtain ⟨restFormed, rightFormed⟩ := induction tailFormed
          refine
            ⟨GapBlocksWellFormed.cons
                seen block rest markerFresh secondsSeen restFormed,
              ?_⟩
          simpa [seenAfterGapBlocks, gapBlockMarkers,
            List.append_assoc] using rightFormed

/-- Every letter in the selected last gap has a witness in the swept prefix:
either it is the selected marker itself or it is one of the earlier block
markers retained by `renderSweptPriorBlocks`. -/
theorem lastGapSecondsSeenInSweptPrefix
    {before : List GapBlock} {lastBlock : GapBlock}
    {after : List GapBlock}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after))
    {letter : Nat} (member : letter ∈ lastBlock.seconds) :
    letter ∈ renderSweptPriorBlocks before ++ [lastBlock.marker] := by
  obtain ⟨_, lastAndAfterFormed⟩ :=
    gapBlocksWellFormed_append formed
  have seen :
      letter ∈ lastBlock.marker :: seenAfterGapBlocks [] before := by
    cases lastAndAfterFormed with
    | cons _ _ _ _ secondsSeen _ =>
        exact secondsSeen letter member
  rcases List.mem_cons.mp seen with atMarker | historical
  · subst letter
    simp
  · have inMarkers : letter ∈ gapBlockMarkers before := by
      simpa [seenAfterGapBlocks] using historical
    have inSwept :=
      gapBlockMarker_mem_renderSweptPriorBlocks letter inMarkers
    exact List.mem_append.mpr <| Or.inl inSwept

/-- In particular, the anchor selected as the head of the last nonempty gap
is witnessed in the swept prefix. -/
theorem lastGapAnchorSeenInSweptPrefix
    {before : List GapBlock} {lastBlock : GapBlock}
    {after : List GapBlock} {anchor : Nat} {remaining : List Nat}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after))
    (lastGapShape : lastBlock.seconds = anchor :: remaining) :
    anchor ∈ renderSweptPriorBlocks before ++ [lastBlock.marker] := by
  apply lastGapSecondsSeenInSweptPrefix formed
  rw [lastGapShape]
  exact List.Mem.head remaining

/-- Regroup and sweep the selected final gap after its exposed marker square.
The displayed rotation `remaining ++ [anchor]` is first returned to the
literal seconds field using witnessed exchanges.  The ordinary one-gap sweep
then gathers every final-marker copy and moves every non-marker debt letter
behind the square. -/
theorem hullListDerivesSweepSelectedLastGapAcrossExposedSquare
    (suffix : List Nat)
    {before : List GapBlock} {lastBlock : GapBlock}
    {after : List GapBlock} {anchor : Nat} {remaining : List Nat}
    (formed :
      GapBlocksWellFormed [] (before ++ lastBlock :: after))
    (lastShape : lastBlock.seconds = anchor :: remaining) :
    HullListDerives
      (renderSweptPriorBlocks before ++ [lastBlock.marker] ++
        remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
        sweptPriorDebt before ++ suffix)
      (renderSweptPriorBlocks before ++ sweptGapMarkerPower lastBlock ++
        [lastBlock.marker, lastBlock.marker] ++ sweptGapDebt lastBlock ++
        sweptPriorDebt before ++ suffix) := by
  let witnesses :=
    renderSweptPriorBlocks before ++ [lastBlock.marker]
  have secondsSeen :
      forall letter, letter ∈ lastBlock.seconds ->
        letter ∈ witnesses := by
    intro letter member
    simpa [witnesses] using
      lastGapSecondsSeenInSweptPrefix formed member
  have rotationBack :
      (remaining ++ [anchor]).Perm lastBlock.seconds := by
    rw [lastShape]
    exact (perm_cons_to_end anchor remaining).symm
  have rotatedSeen :
      forall letter, letter ∈ remaining ++ [anchor] ->
        letter ∈ witnesses := by
    intro letter member
    exact secondsSeen letter <| (rotationBack.mem_iff).mp member
  have rotatedBack :=
    hullListDerivesWitnessedTailPermutation
      witnesses
      ([lastBlock.marker, lastBlock.marker] ++
        sweptPriorDebt before ++ suffix)
      rotatedSeen rotationBack
  have rotatedBackFromSource :
      HullListDerives
        (renderSweptPriorBlocks before ++ [lastBlock.marker] ++
          remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++ suffix)
        (renderSweptPriorBlocks before ++ [lastBlock.marker] ++
          lastBlock.seconds ++ [lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++ suffix) := by
    simpa [witnesses, List.append_assoc] using rotatedBack
  have finalDebtSeen :
      forall letter, letter ∈ gapDebt lastBlock ->
        letter ∈ renderSweptPriorBlocks before := by
    intro letter member
    rcases List.mem_filter.mp member with
      ⟨inSeconds, different⟩
    have notMarker : letter ≠ lastBlock.marker := by
      simpa using different
    have seen :=
      lastGapSecondsSeenInSweptPrefix formed inSeconds
    rcases List.mem_append.mp seen with inPrior | atMarker
    · exact inPrior
    · have equal : letter = lastBlock.marker := by
        simpa using atMarker
      exact False.elim <| notMarker equal
  have swept :=
    hullListDerivesSweepGapAcrossTerminalSquare
      (renderSweptPriorBlocks before) []
      (sweptPriorDebt before ++ suffix)
      lastBlock lastBlock.marker finalDebtSeen
  have sweptFromRegrouped :
      HullListDerives
        (renderSweptPriorBlocks before ++ [lastBlock.marker] ++
          lastBlock.seconds ++ [lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++ suffix)
        (renderSweptPriorBlocks before ++ sweptGapMarkerPower lastBlock ++
          [lastBlock.marker, lastBlock.marker] ++ sweptGapDebt lastBlock ++
          sweptPriorDebt before ++ suffix) := by
    simpa [List.append_assoc] using swept
  exact rotatedBackFromSource.trans sweptFromRegrouped

theorem gapBlockMarker_mem_renderGapBlocks
    (letter : Nat) :
    forall {blocks : List GapBlock},
      letter ∈ gapBlockMarkers blocks ->
        letter ∈ renderGapBlocks blocks
  | [], member => by
      simp [gapBlockMarkers] at member
  | block :: rest, member => by
      simp only [gapBlockMarkers, List.map_cons, List.mem_cons] at member
      rcases member with atMarker | later
      · subst letter
        simp [renderGapBlocks]
      · simp [renderGapBlocks,
          gapBlockMarker_mem_renderGapBlocks letter later]

theorem renderGapBlocks_eq_markers_of_seconds_empty :
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

/-! ## Last-doubled skeleton -/

/-- Structural output of the first half of Lee--Zhang Lemma 23.5.

For any well-formed parsed list with a nonempty gap, the final such block is
selected.  All later blocks are literal singleton markers.  The final gap is
rotated to expose a witnessed anchor, and a square of the final block marker
is adjoined immediately after that anchor.  Every earlier block is then swept
across that square, leaving exact leading marker powers and exact terminal
debt.

The outer contexts are arbitrary and remain unchanged. -/
theorem hullListDerivesLastDoubledSkeleton
    (pre post : List Nat) {blocks : List GapBlock}
    (formed : GapBlocksWellFormed [] blocks)
    (nonemptyGap :
      exists block, block ∈ blocks /\ block.seconds ≠ []) :
    exists before lastBlock after anchor remaining,
      blocks = before ++ lastBlock :: after /\
      lastBlock.seconds = anchor :: remaining /\
      lastBlock.seconds ≠ [] /\
      (forall block, block ∈ after -> block.seconds = []) /\
      HullListDerives
        (pre ++ renderGapBlocks blocks ++ post)
        (pre ++ renderSweptPriorBlocks before ++
          [lastBlock.marker] ++ remaining ++
          [anchor, lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++
          gapBlockMarkers after ++ post) := by
  obtain ⟨before, lastBlock, after,
      blocksShape, lastNonempty, afterEmpty⟩ :=
    exists_last_nonempty_gap_split nonemptyGap
  have formedAtSplit :
      GapBlocksWellFormed [] (before ++ lastBlock :: after) := by
    simpa [blocksShape] using formed
  obtain ⟨beforeFormed, lastAndAfterFormed⟩ :=
    gapBlocksWellFormed_append formedAtSplit
  have lastSecondsSeen :
      forall letter, letter ∈ lastBlock.seconds ->
        letter ∈ lastBlock.marker :: seenAfterGapBlocks [] before := by
    cases lastAndAfterFormed with
    | cons _ _ _ _ secondsSeen _ =>
        exact secondsSeen
  have secondsWitnessed :
      forall letter, letter ∈ lastBlock.seconds ->
        letter ∈ (pre ++ renderGapBlocks before) ++ [lastBlock.marker] := by
    intro letter member
    rcases List.mem_cons.mp (lastSecondsSeen letter member) with
      atMarker | historical
    · subst letter
      simp
    · have inMarkers : letter ∈ gapBlockMarkers before := by
        simpa [seenAfterGapBlocks] using historical
      have inRendered :=
        gapBlockMarker_mem_renderGapBlocks letter inMarkers
      simp [inRendered]
  obtain ⟨anchor, remaining, lastGapShape,
      anchorInGap, exposed⟩ :=
    hullListDerivesExposeLastGapSquare
      (pre ++ renderGapBlocks before)
      (renderGapBlocks after ++ post) lastBlock
      lastNonempty secondsWitnessed
  have afterRender :
      renderGapBlocks after = gapBlockMarkers after :=
    renderGapBlocks_eq_markers_of_seconds_empty after afterEmpty
  have exposedFromSource :
      HullListDerives
        (pre ++ renderGapBlocks blocks ++ post)
        (pre ++ renderGapBlocks before ++ [lastBlock.marker] ++
          remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
          gapBlockMarkers after ++ post) := by
    simpa [blocksShape, renderGapBlocks_append, renderGapBlocks,
      lastGapShape, afterRender, List.append_assoc] using exposed
  have swept :=
    hullListDerivesSweepPriorBlocks
      pre ([lastBlock.marker] ++ remaining ++ [anchor])
      (gapBlockMarkers after ++ post) lastBlock.marker beforeFormed
      (by simp)
  have sweptFromExposed :
      HullListDerives
        (pre ++ renderGapBlocks before ++ [lastBlock.marker] ++
          remaining ++ [anchor, lastBlock.marker, lastBlock.marker] ++
          gapBlockMarkers after ++ post)
        (pre ++ renderSweptPriorBlocks before ++
          [lastBlock.marker] ++ remaining ++
          [anchor, lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++
          gapBlockMarkers after ++ post) := by
    simpa [List.append_assoc] using swept
  refine
    ⟨before, lastBlock, after, anchor, remaining,
      blocksShape, lastGapShape, lastNonempty, afterEmpty, ?_⟩
  exact exposedFromSource.trans sweptFromExposed

/-- Parser-facing form of `hullListDerivesLastDoubledSkeleton`.  The phase
scanner's doubled branch supplies the nonempty-gap witness, and the parser's
render theorem restores the literal source list in the conclusion. -/
theorem hullListDerivesParsedListLastDoubledSkeleton
    (pre post letters : List Nat)
    (doubled : phaseListHasDoubled (phaseProfileList letters) = true) :
    exists before lastBlock after anchor remaining,
      gapBlocksList letters = before ++ lastBlock :: after /\
      lastBlock.seconds = anchor :: remaining /\
      lastBlock.seconds ≠ [] /\
      (forall block, block ∈ after -> block.seconds = []) /\
      HullListDerives
        (pre ++ letters ++ post)
        (pre ++ renderSweptPriorBlocks before ++
          [lastBlock.marker] ++ remaining ++
          [anchor, lastBlock.marker, lastBlock.marker] ++
          sweptPriorDebt before ++
          gapBlockMarkers after ++ post) := by
  have nonemptyGap :
      exists block,
        block ∈ gapBlocksList letters /\ block.seconds ≠ [] := by
    apply (hasDoubledPhase_map_phaseOfGapBlock_eq_true_iff
      (gapBlocksList letters)).mp
    rw [← phaseGapProfileAgreement]
    exact doubled
  obtain ⟨before, lastBlock, after, anchor, remaining,
      blocksShape, lastGapShape, lastNonempty, afterEmpty, derived⟩ :=
    hullListDerivesLastDoubledSkeleton
      pre post (gapBlocksList_wellFormed letters) nonemptyGap
  refine
    ⟨before, lastBlock, after, anchor, remaining,
      blocksShape, lastGapShape, lastNonempty, afterEmpty, ?_⟩
  simpa [render_gapBlocksList] using derived

end Order6Hull23_1PhaseParityGapMoves
end CoRoots
end SemigroupBasis
