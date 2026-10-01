import SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves

/-!
# Hull 23.1 terminal-square and power moves

This module contains the power bookkeeping used after the Proposition 23.1
Balance sweep.  It stays over the literal fifteen-law basis.  In particular,
the block version of the Seed law below is obtained by substituting one
nonempty word into (23.1a), and all later rewrites are compositions of the
six B15 move schemes exposed by `Order6Hull23_1PhaseParityMoves`.

The final section packages the exceptional step in Lee--Zhang Lemma 23.5.
In the paper's notation, the terminal occurrence with `f_i = 1` is moved
next to the `x_i`-power, Seed absorbs it into that power, two copied tail
words are grouped and contracted to one displayed pair per block, those
pairs are transferred to the final tail marker, and the surplus final-marker
pairs are contracted.  The theorem records this literal
Exchange--Seed--Exchange--PowerContract--ParityTransfer--PowerContract
chain without importing a derivation from Hull 21.1.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityPowerMoves

open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityMoves
open SemigroupBasis.CoRoots.Order6Hull23_1PhaseParityDebtMoves

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-! ## Word-valued Seed and terminal-square preparation -/

/-- Substitution of a nonempty block for `y` in (23.1a):
`xx T x = xxx T T T`. -/
theorem hullListDerivesSeedBlock
    (pre post : List Nat) (x tailHead : Nat) (tailRest : List Nat) :
    HullListDerives
      (pre ++ [x, x] ++ (tailHead :: tailRest) ++ [x] ++ post)
      (pre ++ [x, x, x] ++
        (tailHead :: tailRest) ++
        (tailHead :: tailRest) ++
        (tailHead :: tailRest) ++ post) := by
  let tailWord : Word Nat := Word.mk tailHead tailRest
  have member :
      (Identity.mk (Word.mk 0 [0, 1, 0])
        (Word.mk 0 [0, 0, 1, 1, 1])) ∈ basis := by
    decide
  have law := Derives.fromBasis member
  let substitution : Nat -> Word Nat :=
    fun index =>
      if index = 0 then Word.singleton x
      else tailWord
  have derived :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (Derives.subst law substitution)
  simpa [Word.toList, Word.bind, substitution, tailWord,
    List.append_assoc] using derived.context pre post

/-- Total list wrapper around `hullListDerivesSeedBlock`.  The nonempty
hypothesis is exactly the semigroup-word side condition on the substituted
tail block. -/
theorem hullListDerivesSeedNonemptyBlock
    (pre post block : List Nat) (x : Nat)
    (blockNonempty : block ≠ []) :
    HullListDerives
      (pre ++ [x, x] ++ block ++ [x] ++ post)
      (pre ++ [x, x, x] ++ block ++ block ++ block ++ post) := by
  cases block with
  | nil =>
      exact False.elim (blockNonempty rfl)
  | cons head tail =>
      exact hullListDerivesSeedBlock pre post x head tail

/-- A final old letter can expose a terminal square of the active marker.
First (23.1b) is used backwards to triple the selected old letter, using its
earlier witness.  Then (23.1c) is used backwards to transfer the last two
copies to the active marker. -/
theorem hullListDerivesExposeTerminalMarkerSquare
    (pre post history : List Nat) (marker terminal : Nat)
    (terminalSeen : terminal ∈ marker :: history) :
    HullListDerives
      (pre ++ [marker] ++ history ++ [terminal] ++ post)
      (pre ++ [marker] ++ history ++
        [terminal, marker, marker] ++ post) := by
  obtain ⟨before, after, witnessSplit⟩ :=
    List.mem_iff_append.mp terminalSeen
  have expandTerminal :
      HullListDerives
        (pre ++ [marker] ++ history ++ [terminal] ++ post)
        (pre ++ [marker] ++ history ++
          [terminal, terminal, terminal] ++ post) := by
    simpa [witnessSplit, List.append_assoc] using
      (hullListDerivesPowerContract
        (pre ++ before) post after terminal).symm
  have transferSquare :
      HullListDerives
        (pre ++ [marker] ++ history ++
          [terminal, terminal, terminal] ++ post)
        (pre ++ [marker] ++ history ++
          [terminal, marker, marker] ++ post) := by
    simpa [List.append_assoc] using
      (hullListDerivesParityTransfer
        pre post history marker terminal).symm
  exact expandTerminal.trans transferSquare

private theorem exists_append_singleton_of_ne_nil :
    forall {letters : List Nat}, letters ≠ [] ->
      exists initial terminal, letters = initial ++ [terminal]
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => by
      cases tail with
      | nil =>
          exact ⟨[], head, by simp⟩
      | cons next rest =>
          obtain ⟨initial, terminal, shape⟩ :=
            exists_append_singleton_of_ne_nil
              (letters := next :: rest) (by simp)
          exact ⟨head :: initial, terminal, by simp [shape]⟩

/-- A nonempty final gap whose letters are all old admits a derivation that
leaves the gap in place and appends an explicit square of its marker.  The
witness includes the chosen final gap letter for consumers that need the
literal cut. -/
theorem hullListDerivesExposeTerminalMarkerSquareOfNonemptyGap
    (pre post history gap : List Nat) (marker : Nat)
    (gapNonempty : gap ≠ [])
    (gapSeen :
      forall letter, letter ∈ gap -> letter ∈ marker :: history) :
    exists gapPrefix terminal,
      gap = gapPrefix ++ [terminal] ∧
      HullListDerives
        (pre ++ [marker] ++ history ++ gap ++ post)
        (pre ++ [marker] ++ history ++ gap ++
          [marker, marker] ++ post) := by
  obtain ⟨gapPrefix, terminal, gapShape⟩ :=
    exists_append_singleton_of_ne_nil gapNonempty
  have terminalOld : terminal ∈ marker :: (history ++ gapPrefix) := by
    have earlier : terminal ∈ marker :: history :=
      gapSeen terminal <| by
        rw [gapShape]
        simp
    simpa [List.mem_append] using
      List.mem_append_left gapPrefix earlier
  refine ⟨gapPrefix, terminal, gapShape, ?_⟩
  rw [gapShape]
  simpa [List.append_assoc] using
    hullListDerivesExposeTerminalMarkerSquare
      pre post (history ++ gapPrefix) marker terminal terminalOld

/-! ## Pair renderers and marker-power normalization -/

/-- One displayed adjacent pair for each marker in a list. -/
def displayedMarkerPairs : List Nat -> List Nat
  | [] => []
  | marker :: rest =>
      [marker, marker] ++ displayedMarkerPairs rest

theorem displayedMarkerPairs_append
    (left right : List Nat) :
    displayedMarkerPairs (left ++ right) =
      displayedMarkerPairs left ++ displayedMarkerPairs right := by
  induction left with
  | nil => rfl
  | cons marker rest induction =>
      simp [displayedMarkerPairs, induction, List.append_assoc]

/-- A number of adjacent pairs of one fixed marker, indexed by an arbitrary
list whose elements are irrelevant.  Keeping the structural index avoids
arithmetic side conditions in the derivational inductions. -/
def markerPairTail (marker : Nat) : List Nat -> List Nat
  | [] => []
  | _ :: rest => [marker, marker] ++ markerPairTail marker rest

/-- A fixed-marker pair commutes past any structurally indexed fixed-marker
pair tail.  This is literal list equality, not a semigroup rewrite. -/
theorem markerPairTail_append_pair
    (marker : Nat) :
    forall indices : List Nat,
      markerPairTail marker indices ++ [marker, marker] =
        [marker, marker] ++ markerPairTail marker indices
  | [] => rfl
  | index :: rest => by
      simp [markerPairTail, markerPairTail_append_pair marker rest,
        List.append_assoc]

/-- A fixed-marker cube commutes past a structurally indexed fixed-marker
pair tail.  This equality aligns the Seed-created active power with the
even/odd power-normalizer interfaces. -/
theorem markerPairTail_append_triple
    (marker : Nat) :
    forall indices : List Nat,
      markerPairTail marker indices ++ [marker, marker, marker] =
        [marker, marker, marker] ++ markerPairTail marker indices
  | [] => rfl
  | index :: rest => by
      simp [markerPairTail, markerPairTail_append_triple marker rest,
        List.append_assoc]

/-- Contract an even power `2 + 2k` to the displayed square.  Each induction
step is one forward use of (23.1b) with empty optional context. -/
theorem hullListDerivesNormalizeEvenMarkerPower
    (pre post indices : List Nat) (marker : Nat) :
    HullListDerives
      (pre ++ [marker, marker] ++
        markerPairTail marker indices ++ post)
      (pre ++ [marker, marker] ++ post) := by
  induction indices with
  | nil =>
      simpa only [markerPairTail, List.append_nil,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (pre ++ [marker, marker] ++ post))
  | cons index rest induction =>
      have contractFirst :
          HullListDerives
            (pre ++ [marker, marker] ++
              markerPairTail marker (index :: rest) ++ post)
            (pre ++ [marker, marker] ++
              markerPairTail marker rest ++ post) := by
        simpa only [markerPairTail, List.append_assoc] using
          hullListDerivesPowerContract
            pre (markerPairTail marker rest ++ post) [] marker
      exact contractFirst.trans induction

/-- Contract an odd power `3 + 2k` to the displayed cube.  The retained
middle copy is the optional context in (23.1b). -/
theorem hullListDerivesNormalizeOddMarkerPower
    (pre post indices : List Nat) (marker : Nat) :
    HullListDerives
      (pre ++ [marker, marker, marker] ++
        markerPairTail marker indices ++ post)
      (pre ++ [marker, marker, marker] ++ post) := by
  induction indices with
  | nil =>
      simpa only [markerPairTail, List.append_nil,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (pre ++ [marker, marker, marker] ++ post))
  | cons index rest induction =>
      have contractFirst :
          HullListDerives
            (pre ++ [marker, marker, marker] ++
              markerPairTail marker (index :: rest) ++ post)
            (pre ++ [marker, marker, marker] ++
              markerPairTail marker rest ++ post) := by
        simpa only [markerPairTail, List.append_assoc] using
          hullListDerivesPowerContract
            pre (markerPairTail marker rest ++ post)
            [marker] marker
      exact contractFirst.trans induction

/-- One grouped even power arising from the two copied tail words in the
exceptional Seed expansion.  `extraPairs` records the exponent minus one:
the rendered block has exponent `2 + 2 * extraPairs.length`. -/
structure EvenPowerBlock where
  marker : Nat
  extraPairs : List Nat

def renderEvenPowerBlock (block : EvenPowerBlock) : List Nat :=
  [block.marker, block.marker] ++
    markerPairTail block.marker block.extraPairs

def renderEvenPowerBlocks : List EvenPowerBlock -> List Nat
  | [] => []
  | block :: rest =>
      renderEvenPowerBlock block ++ renderEvenPowerBlocks rest

def powerBlockMarkers (blocks : List EvenPowerBlock) : List Nat :=
  blocks.map EvenPowerBlock.marker

def displayedPowerBlockPairs : List EvenPowerBlock -> List Nat
  | [] => []
  | block :: rest =>
      [block.marker, block.marker] ++ displayedPowerBlockPairs rest

theorem displayedPowerBlockPairs_append
    (left right : List EvenPowerBlock) :
    displayedPowerBlockPairs (left ++ right) =
      displayedPowerBlockPairs left ++ displayedPowerBlockPairs right := by
  induction left with
  | nil => rfl
  | cons block rest induction =>
      simp [displayedPowerBlockPairs, induction, List.append_assoc]

theorem displayedPowerBlockPairs_eq_displayedMarkerPairs :
    forall blocks : List EvenPowerBlock,
      displayedPowerBlockPairs blocks =
        displayedMarkerPairs (powerBlockMarkers blocks)
  | [] => rfl
  | block :: rest => by
      simp [displayedPowerBlockPairs, displayedMarkerPairs,
        powerBlockMarkers,
        displayedPowerBlockPairs_eq_displayedMarkerPairs rest]

/-- Normalize every grouped copied-tail power to one pair.  This is the
PowerContract stage following the second Exchange in Lemma 23.5. -/
theorem hullListDerivesNormalizeEvenPowerBlocks
    (pre post : List Nat) :
    forall blocks : List EvenPowerBlock,
      HullListDerives
        (pre ++ renderEvenPowerBlocks blocks ++ post)
        (pre ++ displayedPowerBlockPairs blocks ++ post)
  | [] => by
      simpa only [renderEvenPowerBlocks,
        displayedPowerBlockPairs, List.append_nil] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (pre ++ post))
  | block :: rest => by
      have normalizeHead :=
        hullListDerivesNormalizeEvenMarkerPower
          pre (renderEvenPowerBlocks rest ++ post)
          block.extraPairs block.marker
      have normalizeRest :=
        hullListDerivesNormalizeEvenPowerBlocks
          (pre ++ [block.marker, block.marker]) post rest
      have normalizeHeadAligned :
          HullListDerives
            (pre ++ renderEvenPowerBlocks (block :: rest) ++ post)
            ((pre ++ [block.marker, block.marker]) ++
              renderEvenPowerBlocks rest ++ post) := by
        simpa only [renderEvenPowerBlocks, renderEvenPowerBlock,
          List.append_assoc] using normalizeHead
      have normalizeRestAligned :
          HullListDerives
            ((pre ++ [block.marker, block.marker]) ++
              renderEvenPowerBlocks rest ++ post)
            (pre ++ displayedPowerBlockPairs (block :: rest) ++
              post) := by
        simpa only [displayedPowerBlockPairs,
          List.append_assoc] using normalizeRest
      exact normalizeHeadAligned.trans normalizeRestAligned

/-! ## ParityTransfer sweep to the last tail marker -/

/-- Transfer one adjacent pair to a displayed terminal marker.  The donor
has an earlier occurrence in `stem`; (23.1c) changes
`donor ... terminal donor^2` to
`donor ... terminal^3`. -/
theorem hullListDerivesTransferPairToTerminal
    (stem suffix : List Nat) (donor terminal : Nat)
    (donorSeen : donor ∈ stem) :
    HullListDerives
      (stem ++ [terminal, donor, donor] ++ suffix)
      (stem ++ [terminal, terminal, terminal] ++ suffix) := by
  obtain ⟨before, after, stemSplit⟩ :=
    List.mem_iff_append.mp donorSeen
  simpa [stemSplit, List.append_assoc] using
    hullListDerivesParityTransfer
      before suffix after donor terminal

/-- Repeatedly transfer one pair for each displayed donor to the terminal
marker.  The already accumulated terminal copies are folded into `stem` at
the recursive call, so every step is literally one (23.1c) rewrite. -/
theorem hullListDerivesTransferDisplayedPairsToTerminal
    (stem suffix markers : List Nat) (terminal : Nat)
    (markersSeen :
      forall marker, marker ∈ markers -> marker ∈ stem) :
    HullListDerives
      (stem ++ [terminal] ++ displayedMarkerPairs markers ++ suffix)
      (stem ++ [terminal] ++ markerPairTail terminal markers ++ suffix) := by
  induction markers generalizing stem with
  | nil =>
      simpa only [displayedMarkerPairs, markerPairTail,
        List.append_nil] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (stem ++ [terminal] ++ suffix))
  | cons marker rest induction =>
      have markerSeen : marker ∈ stem :=
        markersSeen marker (by simp)
      have transferHead :=
        hullListDerivesTransferPairToTerminal
          stem (displayedMarkerPairs rest ++ suffix)
          marker terminal markerSeen
      have restSeen :
          forall tested, tested ∈ rest ->
            tested ∈ stem ++ [terminal, terminal] := by
        intro tested member
        exact List.mem_append.mpr <| Or.inl <|
          markersSeen tested (List.Mem.tail marker member)
      have transferRest :=
        induction
          (stem := stem ++ [terminal, terminal])
          restSeen
      have transferHeadAligned :
          HullListDerives
            (stem ++ [terminal] ++
              displayedMarkerPairs (marker :: rest) ++ suffix)
            ((stem ++ [terminal, terminal]) ++ [terminal] ++
              displayedMarkerPairs rest ++ suffix) := by
        simpa only [displayedMarkerPairs,
          List.append_assoc] using transferHead
      have transferred := transferHeadAligned.trans transferRest
      simpa only [markerPairTail,
        List.append_assoc] using transferred

/-- After the pair-transfer sweep, contract all but one of the accumulated
pairs.  The result retains a cube at the selected last occurrence; relative
to the original terminal block this is exactly the paper's `e_r + 2`. -/
theorem hullListDerivesContractTransferredTerminalPairs
    (stem post markers : List Nat) (terminal : Nat) :
    HullListDerives
      (stem ++ [terminal] ++ markerPairTail terminal markers ++
        [terminal, terminal] ++ post)
      (stem ++ [terminal, terminal, terminal] ++ post) := by
  induction markers generalizing stem with
  | nil =>
      simpa only [markerPairTail, List.append_nil,
        List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (stem ++ [terminal, terminal, terminal] ++ post))
  | cons marker rest induction =>
      have commute := markerPairTail_append_pair terminal rest
      have contractFirst :
          HullListDerives
            (stem ++ [terminal] ++
              markerPairTail terminal (marker :: rest) ++
              [terminal, terminal] ++ post)
            (stem ++ [terminal] ++ markerPairTail terminal rest ++
              [terminal, terminal] ++ post) := by
        have contract :=
          hullListDerivesPowerContract
            stem (markerPairTail terminal rest ++ post)
            [terminal] terminal
        simpa [markerPairTail, commute, List.append_assoc] using
          contract
      have finish := induction (stem := stem)
      exact contractFirst.trans finish

/-! ## The exceptional `e_i > 1`, `f_i = 1` chain -/

/-- Literal list-level form of the exceptional repair in Lee--Zhang
Lemma 23.5.

`tail` is the block word `T = x_{i+1}^{e_{i+1}} ... x_r^{e_r}`.
`blocks` describes the grouped powers in the two copied occurrences of `T`;
thus `copiedTailOrder` is the second Exchange stage.  `earlierBlocks` are all
those blocks except the final `terminalBlock`, and `tailStem` ends immediately
before the selected last occurrence of `x_r`.

The source displays the exceptional terminal `x_i` after `debt`; the target
has absorbed it into the initial `x_i` power and has raised the final
`x_r` power by two.  The six proof terms below occur in the published order:
Exchange, Seed, Exchange, PowerContract, ParityTransfer, PowerContract.

This theorem intentionally stops at that six-step boundary: its target still
contains the Seed-created `x_i^(e_i+1)` run.  It is not the canonical
Condition-IV completion.  Consumers that need the capped active power should
use `hullListDerivesExceptionalTerminalRepairConditionIV` below. -/
theorem hullListDerivesExceptionalTerminalRepair
    (pre suffix debt tail tailStem : List Nat)
    (active terminal : Nat)
    (blocks earlierBlocks : List EvenPowerBlock)
    (terminalBlock : EvenPowerBlock)
    (tailNonempty : tail ≠ [])
    (tailShape : tail = tailStem ++ [terminal])
    (blocksShape : blocks = earlierBlocks ++ [terminalBlock])
    (terminalBlockMarker : terminalBlock.marker = terminal)
    (debtSeen :
      forall letter, letter ∈ debt ->
        letter ∈ pre ++ [active, active] ++ tail)
    (copiedTailOrder :
      (tail ++ tail).Perm (renderEvenPowerBlocks blocks))
    (earlierMarkersSeen :
      forall block, block ∈ earlierBlocks ->
        block.marker ∈ tailStem) :
    HullListDerives
      (pre ++ [active, active] ++ tail ++ debt ++
        [active] ++ suffix)
      (pre ++ [active, active, active] ++ tailStem ++
        [terminal, terminal, terminal] ++ debt ++ suffix) := by
  let firstWitnesses := pre ++ [active, active] ++ tail
  have firstCovered :
      forall letter, letter ∈ debt ++ [active] ->
        letter ∈ firstWitnesses := by
    intro letter member
    rcases List.mem_append.mp member with inDebt | atActive
    · exact debtSeen letter inDebt
    · have equal : letter = active := by simpa using atActive
      subst letter
      simp [firstWitnesses]
  have firstExchange :
      HullListDerives
        (pre ++ [active, active] ++ tail ++ debt ++
          [active] ++ suffix)
        (pre ++ [active, active] ++ tail ++ [active] ++
          debt ++ suffix) := by
    have moved :=
      hullListDerivesWitnessedTailPermutation
        firstWitnesses suffix firstCovered
          (List.perm_append_comm
            (l₁ := debt) (l₂ := [active]))
    simpa [firstWitnesses, List.append_assoc] using moved
  have seed :
      HullListDerives
        (pre ++ [active, active] ++ tail ++ [active] ++
          debt ++ suffix)
        (pre ++ [active, active, active] ++ tail ++ tail ++
          tail ++ debt ++ suffix) := by
    simpa [List.append_assoc] using
      hullListDerivesSeedNonemptyBlock
        pre (debt ++ suffix) tail active tailNonempty
  let copiedWitnesses :=
    pre ++ [active, active, active] ++ tail
  have copiedCovered :
      forall letter, letter ∈ tail ++ tail ->
        letter ∈ copiedWitnesses := by
    intro letter member
    have inTail : letter ∈ tail := by
      rcases List.mem_append.mp member with first | second
      · exact first
      · exact second
    simp [copiedWitnesses, inTail]
  have secondExchange :
      HullListDerives
        (pre ++ [active, active, active] ++ tail ++ tail ++
          tail ++ debt ++ suffix)
        (pre ++ [active, active, active] ++ tail ++
          renderEvenPowerBlocks blocks ++ debt ++ suffix) := by
    have reordered :=
      hullListDerivesWitnessedTailPermutation
        copiedWitnesses (debt ++ suffix)
        copiedCovered copiedTailOrder
    simpa [copiedWitnesses, List.append_assoc] using reordered
  have contractCopiedPowers :
      HullListDerives
        (pre ++ [active, active, active] ++ tail ++
          renderEvenPowerBlocks blocks ++ debt ++ suffix)
        (pre ++ [active, active, active] ++ tail ++
          displayedPowerBlockPairs blocks ++ debt ++ suffix) := by
    simpa [copiedWitnesses, List.append_assoc] using
      hullListDerivesNormalizeEvenPowerBlocks
        copiedWitnesses (debt ++ suffix) blocks
  let transferStem :=
    pre ++ [active, active, active] ++ tailStem
  have earlierSeen :
      forall marker,
        marker ∈ powerBlockMarkers earlierBlocks ->
          marker ∈ transferStem := by
    intro marker member
    obtain ⟨block, blockMember, markerEq⟩ :=
      List.mem_map.mp member
    have inTailStem := earlierMarkersSeen block blockMember
    simpa [powerBlockMarkers, markerEq, transferStem] using
      List.mem_append_right
        (pre ++ [active, active, active]) inTailStem
  have transferPairs :
      HullListDerives
        (pre ++ [active, active, active] ++ tail ++
          displayedPowerBlockPairs blocks ++ debt ++ suffix)
        (transferStem ++ [terminal] ++
          markerPairTail terminal (powerBlockMarkers earlierBlocks) ++
          [terminal, terminal] ++ debt ++ suffix) := by
    have transferred :=
      hullListDerivesTransferDisplayedPairsToTerminal
        transferStem ([terminal, terminal] ++ debt ++ suffix)
        (powerBlockMarkers earlierBlocks) terminal earlierSeen
    have earlierPairs :
        displayedPowerBlockPairs earlierBlocks =
          displayedMarkerPairs (powerBlockMarkers earlierBlocks) :=
      displayedPowerBlockPairs_eq_displayedMarkerPairs earlierBlocks
    rw [blocksShape, tailShape,
      displayedPowerBlockPairs_append,
      earlierPairs]
    simp only [displayedPowerBlockPairs, terminalBlockMarker]
    simpa [transferStem, List.append_assoc] using transferred
  have contractTransferredPairs :
      HullListDerives
        (transferStem ++ [terminal] ++
          markerPairTail terminal (powerBlockMarkers earlierBlocks) ++
          [terminal, terminal] ++ debt ++ suffix)
        (pre ++ [active, active, active] ++ tailStem ++
          [terminal, terminal, terminal] ++ debt ++ suffix) := by
    simpa [transferStem, List.append_assoc] using
      hullListDerivesContractTransferredTerminalPairs
        transferStem (debt ++ suffix)
        (powerBlockMarkers earlierBlocks) terminal
  exact firstExchange.trans <|
    seed.trans <| secondExchange.trans <|
      contractCopiedPowers.trans <|
        transferPairs.trans contractTransferredPairs

/-! ## Canonical Condition-IV completion of the exceptional chain -/

/-- Which parity-selected active power remains after the exceptional
terminal occurrence has been absorbed.  An initially odd `e_i > 1` becomes
even and caps to a square; an initially even `e_i > 1` becomes odd and caps
to a cube. -/
inductive ConditionIVActiveResult
  | square
  | cube
deriving Repr, DecidableEq

/-- The part of the initial active run preceding the final two copies used
by Seed.  `square` records an odd prefix of length `1 + 2k`, hence an initial
active exponent `3 + 2k`.  `cube` records a pair tail of length `2k`, hence
an initial active exponent `2 + 2k`; in particular it includes the minimum
exceptional case `e_i = 2`. -/
def conditionIVExceptionalPrefix
    (result : ConditionIVActiveResult)
    (stable : List Nat) (active : Nat)
    (excessPairs : List Nat) : List Nat :=
  match result with
  | .square =>
      stable ++ [active] ++ markerPairTail active excessPairs
  | .cube =>
      stable ++ markerPairTail active excessPairs

/-- The canonical active power selected by the parity of `e_i + 1`. -/
def renderConditionIVActivePower
    (result : ConditionIVActiveResult) (active : Nat) : List Nat :=
  match result with
  | .square => [active, active]
  | .cube => [active, active, active]

/-- Canonical Condition-IV completion of the exceptional `e_i > 1`,
`f_i = 1` repair required to enforce the published condition
`e_i > 1 -> f_i = 0`.

The source prefix explicitly represents every excess active-marker pair.
The theorem first invokes the literal
Exchange--Seed--Exchange--PowerContract--ParityTransfer--PowerContract
chain, then applies one of the ordinary active-power normalizers:

* an odd initial exponent `3 + 2k` becomes `4 + 2k` after Seed and contracts
  to the canonical square;
* an even initial exponent `2 + 2k` becomes `3 + 2k` after Seed and contracts
  to the canonical cube.

Thus this theorem, unlike `hullListDerivesExceptionalTerminalRepair`, has no
uncapped Seed-created active run in its target. -/
theorem hullListDerivesExceptionalTerminalRepairConditionIV
    (stable suffix debt tail tailStem excessPairs : List Nat)
    (active terminal : Nat)
    (result : ConditionIVActiveResult)
    (blocks earlierBlocks : List EvenPowerBlock)
    (terminalBlock : EvenPowerBlock)
    (tailNonempty : tail ≠ [])
    (tailShape : tail = tailStem ++ [terminal])
    (blocksShape : blocks = earlierBlocks ++ [terminalBlock])
    (terminalBlockMarker : terminalBlock.marker = terminal)
    (debtSeen :
      forall letter, letter ∈ debt ->
        letter ∈
          conditionIVExceptionalPrefix
              result stable active excessPairs ++
            [active, active] ++ tail)
    (copiedTailOrder :
      (tail ++ tail).Perm (renderEvenPowerBlocks blocks))
    (earlierMarkersSeen :
      forall block, block ∈ earlierBlocks ->
        block.marker ∈ tailStem) :
    HullListDerives
      (conditionIVExceptionalPrefix
          result stable active excessPairs ++
        [active, active] ++ tail ++ debt ++ [active] ++ suffix)
      (stable ++ renderConditionIVActivePower result active ++
        tailStem ++ [terminal, terminal, terminal] ++
        debt ++ suffix) := by
  cases result with
  | square =>
      have repaired :=
        hullListDerivesExceptionalTerminalRepair
          (conditionIVExceptionalPrefix
            .square stable active excessPairs)
          suffix debt tail tailStem active terminal
          blocks earlierBlocks terminalBlock tailNonempty
          tailShape blocksShape terminalBlockMarker
          debtSeen copiedTailOrder earlierMarkersSeen
      have capActive :=
        hullListDerivesNormalizeEvenMarkerPower
          stable
          (tailStem ++ [terminal, terminal, terminal] ++
            debt ++ suffix)
          (active :: excessPairs) active
      have capped :
          HullListDerives
            (conditionIVExceptionalPrefix
                .square stable active excessPairs ++
              [active, active, active] ++ tailStem ++
              [terminal, terminal, terminal] ++ debt ++ suffix)
            (stable ++ renderConditionIVActivePower .square active ++
              tailStem ++ [terminal, terminal, terminal] ++
              debt ++ suffix) := by
        simpa [conditionIVExceptionalPrefix,
          renderConditionIVActivePower, markerPairTail,
          markerPairTail_append_triple, List.append_assoc] using
            capActive
      exact repaired.trans capped
  | cube =>
      have repaired :=
        hullListDerivesExceptionalTerminalRepair
          (conditionIVExceptionalPrefix
            .cube stable active excessPairs)
          suffix debt tail tailStem active terminal
          blocks earlierBlocks terminalBlock tailNonempty
          tailShape blocksShape terminalBlockMarker
          debtSeen copiedTailOrder earlierMarkersSeen
      have capActive :=
        hullListDerivesNormalizeOddMarkerPower
          stable
          (tailStem ++ [terminal, terminal, terminal] ++
            debt ++ suffix)
          excessPairs active
      have capped :
          HullListDerives
            (conditionIVExceptionalPrefix
                .cube stable active excessPairs ++
              [active, active, active] ++ tailStem ++
              [terminal, terminal, terminal] ++ debt ++ suffix)
            (stable ++ renderConditionIVActivePower .cube active ++
              tailStem ++ [terminal, terminal, terminal] ++
              debt ++ suffix) := by
        simpa [conditionIVExceptionalPrefix,
          renderConditionIVActivePower, markerPairTail,
          markerPairTail_append_triple, List.append_assoc] using
            capActive
      exact repaired.trans capped

/-! ## ReturnContract / Condition-V repair -/

/-- If a nonempty final debt begins after a terminal cube and every debt
letter already has a witness, (23.1d) contracts that cube to one terminal
copy while retaining the debt.  Choosing the debt head supplies the return
letter required by the law.  This is the Condition-V repair used when the
published block analysis exposes nonempty debt at the final boundary. -/
theorem hullListDerivesConditionVReturnRepair
    (witnesses suffix debt : List Nat) (terminal : Nat)
    (debtNonempty : debt ≠ [])
    (debtSeen :
      forall letter, letter ∈ debt -> letter ∈ witnesses) :
    HullListDerives
      (witnesses ++ [terminal, terminal, terminal] ++ debt ++ suffix)
      (witnesses ++ [terminal] ++ debt ++ suffix) := by
  cases debt with
  | nil =>
      exact False.elim (debtNonempty rfl)
  | cons returnLetter rest =>
      have returnSeen : returnLetter ∈ witnesses :=
        debtSeen returnLetter (by simp)
      obtain ⟨before, after, witnessSplit⟩ :=
        List.mem_iff_append.mp returnSeen
      simpa [witnessSplit, List.append_assoc] using
        hullListDerivesReturnContract
          before (rest ++ suffix) after returnLetter terminal

end Order6Hull23_1PhaseParityPowerMoves
end CoRoots
end SemigroupBasis
