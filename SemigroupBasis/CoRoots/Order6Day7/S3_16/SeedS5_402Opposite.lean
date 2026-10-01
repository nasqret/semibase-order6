import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091FirstOrderPredecessorBridge

/-!
# Prefix-generalized rank-091 first-order predecessor assembly

This source follows fable's exact `msg-0296` assembly cut. Historical
successor-factor scanning is first exposed through independently named
one-step clauses with the WHOLE source list fixed. Final decoration remains
separate from the undecorated streaming state throughout the owner proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 18000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner
open SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091.FirstOrderPredecessorBridge

universe u v

/-- Concatenating unprocessed suffixes resumes the historical terminated
scanner with its honest reverse-accumulator state. -/
theorem terminatedBlockScan_append
    (whole : List Nat) :
    ∀ (before current after : List Nat),
      SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
          whole current (before ++ after) =
        let first :=
          SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
            whole current before
        let second :=
          SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
            whole first.2.reverse after
        (first.1 ++ second.1, second.2) := by
  intro before
  induction before with
  | nil =>
      intro current after
      simp [SemigroupBasis.CoRoots.S5_107.terminatedBlockScan]
  | cons letter rest inductionHypothesis =>
      intro current after
      by_cases simple : whole.count letter = 1
      · simpa [SemigroupBasis.CoRoots.S5_107.terminatedBlockScan,
          simple] using
            inductionHypothesis (letter :: current) after
      · have resumed := inductionHypothesis [] after
        have factorProjection := congrArg Prod.fst resumed
        have finalProjection := congrArg Prod.snd resumed
        simpa [SemigroupBasis.CoRoots.S5_107.terminatedBlockScan,
          simple, List.append_assoc] using
            And.intro factorProjection finalProjection

/-- Appending one globally simple source letter extends exactly the pending
simple block and emits no additional terminated factor. -/
theorem terminatedBlockScan_append_simple
    (whole before current : List Nat) (letter : Nat)
    (simple : whole.count letter = 1) :
    SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
        whole current (before ++ [letter]) =
      ((SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
          whole current before).1,
        (SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
          whole current before).2 ++ [letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.terminatedBlockScan,
    simple, List.reverse_cons] using
      terminatedBlockScan_append whole before current [letter]

/-- Appending one globally repeated source letter closes the pending simple
block into one independently explicit terminated factor. -/
theorem terminatedBlockScan_append_repeated
    (whole before current : List Nat) (letter : Nat)
    (repeated : whole.count letter ≠ 1) :
    SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
        whole current (before ++ [letter]) =
      ((SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
          whole current before).1 ++
        [((SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
          whole current before).2, letter)], []) := by
  simpa [SemigroupBasis.CoRoots.S5_107.terminatedBlockScan,
    repeated] using
      terminatedBlockScan_append whole before current [letter]

/-- Source-facing factorization with WHOLE-word multiplicities fixed while
an arbitrary unprocessed suffix is varied. -/
def sourceFacingFactorScan
    (whole remaining : List Nat) : List Nat × List SuccessorFactor :=
  let reversed :=
    SemigroupBasis.CoRoots.S5_107.terminatedBlockScan
      whole.reverse [] remaining.reverse
  (reversed.2.reverse,
    reversed.1.reverse.map reverseTerminatedFactor)

/-- Empty source-facing state has neither an initial block nor factors. -/
@[simp] theorem sourceFacingFactorScan_nil
    (whole : List Nat) :
    sourceFacingFactorScan whole [] = ([], []) := by
  simp [sourceFacingFactorScan,
    SemigroupBasis.CoRoots.S5_107.terminatedBlockScan]

/-- Explicit fable-cut head case: a globally simple letter extends the
initial block and does not alter the already-determined successor factors. -/
theorem sourceFacingFactorScan_simple_cons
    (whole remaining : List Nat) (letter : Nat)
    (simple : whole.count letter = 1) :
    sourceFacingFactorScan whole (letter :: remaining) =
      (letter :: (sourceFacingFactorScan whole remaining).1,
        (sourceFacingFactorScan whole remaining).2) := by
  have reversedSimple : whole.reverse.count letter = 1 := by
    simpa using simple
  unfold sourceFacingFactorScan
  rw [List.reverse_cons,
    terminatedBlockScan_append_simple
      whole.reverse remaining.reverse [] letter reversedSimple]
  simp [List.reverse_append]

/-- Explicit fable-cut head case: a repeated marker closes the entire
immediately following simple block into exactly one successor factor. -/
theorem sourceFacingFactorScan_repeated_cons
    (whole remaining : List Nat) (letter : Nat)
    (repeated : whole.count letter ≠ 1) :
    sourceFacingFactorScan whole (letter :: remaining) =
      ([], (letter, (sourceFacingFactorScan whole remaining).1) ::
        (sourceFacingFactorScan whole remaining).2) := by
  have reversedRepeated : whole.reverse.count letter ≠ 1 := by
    simpa using repeated
  unfold sourceFacingFactorScan
  rw [List.reverse_cons,
    terminatedBlockScan_append_repeated
      whole.reverse remaining.reverse [] letter reversedRepeated]
  simp [List.reverse_append, reverseTerminatedFactor]

/-- At the genuine whole-word state, the generalized source-facing scanner
is literally the established historical initial-block/factor decomposition. -/
theorem sourceFacingFactorScan_whole
    (letters : List Nat) :
    sourceFacingFactorScan letters letters =
      (initialSimpleBlock letters, successorFactors letters) := by
  rfl

/-- Emit a repeated marker unless the already-emitted prefix ends in the
same marker; this is the exact adjacent-equal correction. -/
def emittedMarkerSquare (last : Option Nat) (marker : Nat) : List Nat :=
  if last = some marker then [] else [marker, marker]

/-- Render a normalized factor suffix relative to the literal final symbol
of the already-emitted prefix. Only its first factor can merge backwards. -/
def renderSquaredFactorsAfter
    (last : Option Nat) : List SuccessorFactor → List Nat
  | [] => []
  | (marker, block) :: rest =>
      emittedMarkerSquare last marker ++ block ++
        renderSquaredSuccessorFactors rest

/-- Empty emitted state recovers the exact established squared-factor output. -/
@[simp] theorem renderSquaredFactorsAfter_none
    (factors : List SuccessorFactor) :
    renderSquaredFactorsAfter none factors =
      renderSquaredSuccessorFactors factors := by
  cases factors with
  | nil => rfl
  | cons factor rest =>
      rcases factor with ⟨marker, block⟩
      simp [renderSquaredFactorsAfter, emittedMarkerSquare,
        renderSquaredSuccessorFactors]

/-- Collapsing adjacent equal empty-marker factors never invents a factor. -/
theorem mem_collapseAdjacentEmptySameFactors
    (factor : SuccessorFactor) :
    ∀ factors : List SuccessorFactor,
      factor ∈ collapseAdjacentEmptySameFactors factors → factor ∈ factors
  | [] => by
      simp [collapseAdjacentEmptySameFactors]
  | (marker, block) :: rest => by
      intro member
      cases normalized : collapseAdjacentEmptySameFactors rest with
      | nil =>
          have same : factor = (marker, block) := by
            simpa [collapseAdjacentEmptySameFactors, normalized] using member
          exact List.mem_cons.mpr (Or.inl same)
      | cons next tail =>
          rcases next with ⟨nextMarker, nextBlock⟩
          by_cases collapsible : block = [] ∧ marker = nextMarker
          · have tailMember : factor ∈
                collapseAdjacentEmptySameFactors rest := by
              simpa [collapseAdjacentEmptySameFactors,
                normalized, collapsible] using member
            exact List.mem_cons_of_mem _ <|
              mem_collapseAdjacentEmptySameFactors factor rest tailMember
          · have alternatives :
                factor = (marker, block) ∨
                  factor ∈ collapseAdjacentEmptySameFactors rest := by
              simpa [collapseAdjacentEmptySameFactors,
                normalized, collapsible] using member
            rcases alternatives with same | later
            · exact List.mem_cons.mpr (Or.inl same)
            · exact List.mem_cons_of_mem _ <|
                mem_collapseAdjacentEmptySameFactors factor rest later

/-- Retaining first, simple-bearing, or final factors never invents a factor. -/
theorem mem_retainFirstBlockOrFinalFactors
    (factor : SuccessorFactor) :
    ∀ (factors : List SuccessorFactor) (seen : List Nat),
      factor ∈ retainFirstBlockOrFinalFactors seen factors → factor ∈ factors
  | [], _ => by
      simp [retainFirstBlockOrFinalFactors]
  | [only], _ => by
      simp [retainFirstBlockOrFinalFactors]
  | (marker, block) :: next :: rest, seen => by
      intro member
      by_cases drop : block = [] ∧ marker ∈ seen
      · have tailMember :
            factor ∈ retainFirstBlockOrFinalFactors seen (next :: rest) := by
          simpa [retainFirstBlockOrFinalFactors, drop] using member
        exact List.mem_cons_of_mem _ <|
          mem_retainFirstBlockOrFinalFactors factor (next :: rest)
            seen tailMember
      · have alternatives :
            factor = (marker, block) ∨
              factor ∈ retainFirstBlockOrFinalFactors
                (seen ++ [marker]) (next :: rest) := by
          simpa [retainFirstBlockOrFinalFactors, drop] using member
        rcases alternatives with same | later
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ <|
            mem_retainFirstBlockOrFinalFactors factor (next :: rest)
              (seen ++ [marker]) later

/-- A nonempty simple block ends in one of its actual source letters. -/
theorem getLastD_mem_of_nonempty
    (block : List Nat) (fallback : Nat)
    (nonempty : block ≠ []) :
    block.getLastD fallback ∈ block := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simpa only [List.getLastD_cons] using
    (List.getLastD_mem_cons (l := tail) (a := head))

/-- Named adjacent-equal unfolding: prepending one genuine successor factor
to a normalized suffix emits exactly its relative square and simple block.
Global simplicity prevents a nonempty block from merging with any marker. -/
theorem renderSquaredFactorsAfter_collapse_cons
    (whole : List Nat) (last : Option Nat)
    (marker : Nat) (block : List Nat) (factors : List SuccessorFactor)
    (blockSimple :
      ∀ letter ∈ block, whole.count letter = 1)
    (tailMarkersRepeated :
      ∀ factor ∈ factors, whole.count factor.1 ≠ 1) :
    renderSquaredFactorsAfter last
        (collapseAdjacentEmptySameFactors
          ((marker, block) :: factors)) =
      emittedMarkerSquare last marker ++ block ++
        renderSquaredFactorsAfter (some (block.getLastD marker))
          (collapseAdjacentEmptySameFactors factors) := by
  cases normalized : collapseAdjacentEmptySameFactors factors with
  | nil =>
      simp [collapseAdjacentEmptySameFactors, normalized,
        renderSquaredFactorsAfter, renderSquaredSuccessorFactors]
  | cons next tail =>
      rcases next with ⟨nextMarker, nextBlock⟩
      by_cases empty : block = []
      · subst block
        by_cases same : marker = nextMarker
        · subst nextMarker
          simp [collapseAdjacentEmptySameFactors, normalized,
            renderSquaredFactorsAfter, emittedMarkerSquare,
            List.append_assoc]
        · simp [collapseAdjacentEmptySameFactors, normalized,
            renderSquaredFactorsAfter, emittedMarkerSquare,
            renderSquaredSuccessorFactors, same]
      · have nextMember : (nextMarker, nextBlock) ∈ factors :=
          mem_collapseAdjacentEmptySameFactors
            (nextMarker, nextBlock) factors (by simp [normalized])
        have lastSimple : whole.count (block.getLastD marker) = 1 :=
          blockSimple (block.getLastD marker)
            (getLastD_mem_of_nonempty block marker empty)
        have nextRepeated : whole.count nextMarker ≠ 1 :=
          tailMarkersRepeated (nextMarker, nextBlock) nextMember
        have different : block.getLastD marker ≠ nextMarker := by
          intro same
          rw [same] at lastSimple
          exact nextRepeated lastSimple
        have differentOption : block.getLast?.getD marker ≠ nextMarker := by
          simpa only [List.getLastD_eq_getLast?] using different
        simp [collapseAdjacentEmptySameFactors, normalized,
          renderSquaredFactorsAfter, emittedMarkerSquare,
          renderSquaredSuccessorFactors, empty, differentOption,
          List.append_assoc]

/-- Prefix-state factor continuation. Seen empty NONFINAL markers disappear,
while the actual final factor remains explicit even when previously seen. -/
def finalFactorFold
    (seen : List Nat) (last : Option Nat) :
    List SuccessorFactor → List Nat
  | [] => []
  | [(marker, block)] =>
      emittedMarkerSquare last marker ++ block
  | (marker, block) :: next :: rest =>
      if block = [] ∧ marker ∈ seen then
        finalFactorFold seen last (next :: rest)
      else
        emittedMarkerSquare last marker ++ block ++
          finalFactorFold
            (seen ++ [marker]) (some (block.getLastD marker))
            (next :: rest)

/-- Exact prefix-generalized unfolding of the corrected retained-factor
canonical. No final letter is erased and no raw recursion is hidden. -/
theorem finalFactorFold_eq_relativeCanonical
    (whole : List Nat) :
    ∀ (factors : List SuccessorFactor)
      (seen : List Nat) (last : Option Nat),
      (∀ factor ∈ factors, whole.count factor.1 ≠ 1) →
      (∀ factor ∈ factors,
        ∀ letter ∈ factor.2, whole.count letter = 1) →
      renderSquaredFactorsAfter last
          (collapseAdjacentEmptySameFactors
            (retainFirstBlockOrFinalFactors seen factors)) =
        finalFactorFold seen last factors
  | [], _, _, _, _ => by
      simp [retainFirstBlockOrFinalFactors,
        collapseAdjacentEmptySameFactors,
        renderSquaredFactorsAfter, finalFactorFold]
  | [(marker, block)], _, last, _, _ => by
      simp [retainFirstBlockOrFinalFactors,
        collapseAdjacentEmptySameFactors,
        renderSquaredFactorsAfter,
        renderSquaredSuccessorFactors, finalFactorFold]
  | (marker, block) :: next :: rest,
      seen, last, markersRepeated, blocksSimple => by
      have tailRepeated :
          ∀ factor ∈ next :: rest, whole.count factor.1 ≠ 1 := by
        intro factor member
        exact markersRepeated factor (by simp [member])
      have tailSimple :
          ∀ factor ∈ next :: rest,
            ∀ letter ∈ factor.2, whole.count letter = 1 := by
        intro factor member letter letterMember
        exact blocksSimple factor (by simp [member]) letter letterMember
      by_cases drop : block = [] ∧ marker ∈ seen
      · have tail :=
          finalFactorFold_eq_relativeCanonical
            whole (next :: rest) seen last tailRepeated tailSimple
        simpa [retainFirstBlockOrFinalFactors,
          finalFactorFold, drop] using tail
      · have currentSimple :
            ∀ letter ∈ block, whole.count letter = 1 := by
          intro letter member
          exact blocksSimple (marker, block) (by simp) letter member
        have retainedTailRepeated :
            ∀ factor ∈
                retainFirstBlockOrFinalFactors
                  (seen ++ [marker]) (next :: rest),
              whole.count factor.1 ≠ 1 := by
          intro factor member
          exact tailRepeated factor <|
            mem_retainFirstBlockOrFinalFactors factor (next :: rest)
              (seen ++ [marker]) member
        have prepend :=
          renderSquaredFactorsAfter_collapse_cons
            whole last marker block
            (retainFirstBlockOrFinalFactors
              (seen ++ [marker]) (next :: rest))
            currentSimple retainedTailRepeated
        have tail :=
          finalFactorFold_eq_relativeCanonical
            whole (next :: rest) (seen ++ [marker])
              (some (block.getLastD marker))
              tailRepeated tailSimple
        rw [retainFirstBlockOrFinalFactors, if_neg drop]
        rw [finalFactorFold, if_neg drop]
        exact prepend.trans <|
          congrArg
            (fun output : List Nat =>
              emittedMarkerSquare last marker ++ block ++ output)
            tail

/-- The complete historical scan satisfies the global repeated-marker and
globally-simple-block hypotheses needed by the relative canonical assembly. -/
theorem finalFactorFold_eq_ownerCanonical
    (letters : List Nat) :
    finalFactorFold [] none (successorFactors letters) =
      renderSquaredSuccessorFactors
        (collapseAdjacentEmptySameFactors
          (retainFirstBlockOrFinalFactors []
            (successorFactors letters))) := by
  have markersRepeated :
      ∀ factor ∈ successorFactors letters,
        letters.count factor.1 ≠ 1 := by
    intro factor member
    have multiple :=
      successorFactor_marker_multiple letters factor.2 factor.1 member
    omega
  have blocksSimple :
      ∀ factor ∈ successorFactors letters,
        ∀ letter ∈ factor.2, letters.count letter = 1 := by
    intro factor member letter letterMember
    exact successorFactor_block_letter_simple
      letters factor.2 factor.1 letter member letterMember
  have assembled :=
    finalFactorFold_eq_relativeCanonical letters
      (successorFactors letters) [] none markersRepeated blocksSimple
  simpa using assembled.symm

/-- The already-proved raw streaming scanner depends only on membership in
its repeated-marker support, never on duplicate support entries. -/
theorem stablePredecessorStreamingFold_seen_congr
    (word : Word Nat) :
    ∀ (remaining before leftSeen rightSeen : List Nat)
      (last : Option Nat),
      (∀ marker, marker ∈ leftSeen ↔ marker ∈ rightSeen) →
      stablePredecessorStreamingFold
          word before leftSeen last remaining =
        stablePredecessorStreamingFold
          word before rightSeen last remaining := by
  intro remaining
  induction remaining with
  | nil =>
      intro before leftSeen rightSeen last _
      simp [stablePredecessorStreamingFold]
  | cons letter rest inductionHypothesis =>
      intro before leftSeen rightSeen last equivalent
      by_cases simple : word.toList.count letter = 1
      · simp only [stablePredecessorStreamingFold, simple, ↓reduceIte]
        exact congrArg
          (fun output : List Nat =>
            prefixPredecessorDecoration word before last ++
              [letter] ++ output)
          (inductionHypothesis
            (before ++ [letter]) leftSeen rightSeen (some letter)
            equivalent)
      · by_cases leftPresent : letter ∈ leftSeen
        · have rightPresent : letter ∈ rightSeen :=
            (equivalent letter).mp leftPresent
          simpa [stablePredecessorStreamingFold, simple,
            leftPresent, rightPresent] using
              inductionHypothesis
                (before ++ [letter]) leftSeen rightSeen last equivalent
        · have rightAbsent : letter ∉ rightSeen := by
            intro member
            exact leftPresent ((equivalent letter).mpr member)
          have appendedEquivalent :
              ∀ marker,
                marker ∈ leftSeen ++ [letter] ↔
                  marker ∈ rightSeen ++ [letter] := by
            intro marker
            simp [equivalent marker]
          simp only [stablePredecessorStreamingFold, simple,
            leftPresent, rightAbsent, ↓reduceIte]
          exact congrArg (fun output : List Nat => [letter, letter] ++ output)
            (inductionHypothesis
              (before ++ [letter]) (leftSeen ++ [letter])
                (rightSeen ++ [letter]) (some letter)
                appendedEquivalent)

/-- Once the raw predecessor is globally simple, an arbitrary globally
simple suffix emits its letters directly and cannot add a marker square. -/
theorem stablePredecessorStreamingFold_simpleTail
    (word : Word Nat) :
    ∀ (tail before seen : List Nat) (previous : Nat)
      (remaining : List Nat),
      word.toList.count previous = 1 →
      (∀ letter ∈ tail, word.toList.count letter = 1) →
      stablePredecessorStreamingFold
          word (before ++ [previous]) seen (some previous)
            (tail ++ remaining) =
        tail ++
          stablePredecessorStreamingFold
            word ((before ++ [previous]) ++ tail) seen
              (some (tail.getLastD previous)) remaining := by
  intro tail
  induction tail with
  | nil =>
      intro before seen previous remaining _ _
      simp
  | cons letter rest inductionHypothesis =>
      intro before seen previous remaining previousSimple tailSimple
      have letterSimple : word.toList.count letter = 1 :=
        tailSimple letter (by simp)
      have restSimple :
          ∀ candidate ∈ rest, word.toList.count candidate = 1 := by
        intro candidate member
        exact tailSimple candidate (by simp [member])
      have noDecoration :
          prefixPredecessorDecoration
            word (before ++ [previous]) (some previous) = [] := by
        simp [prefixPredecessorDecoration,
          List.reverse_append, previousSimple]
      have tailStep :=
        inductionHypothesis
          (before ++ [previous]) seen letter remaining
          letterSimple restSimple
      rw [List.getLastD_cons]
      simpa [stablePredecessorStreamingFold, letterSimple,
        noDecoration, List.append_assoc] using
          congrArg (fun output : List Nat => letter :: output) tailStep

/-- Exact block case: after a globally repeated raw marker, a nonempty
globally simple block emits precisely the missing predecessor square once. -/
theorem stablePredecessorStreamingFold_simpleBlock_afterMarker
    (word : Word Nat) (before seen : List Nat)
    (last : Option Nat) (marker : Nat)
    (block remaining : List Nat)
    (markerRepeated : word.toList.count marker ≠ 1)
    (blockSimple :
      ∀ letter ∈ block, word.toList.count letter = 1) :
    stablePredecessorStreamingFold
        word (before ++ [marker]) seen last
          (block ++ remaining) =
      (if block = [] then [] else emittedMarkerSquare last marker) ++
        block ++
          stablePredecessorStreamingFold
            word ((before ++ [marker]) ++ block) seen
              (if block = [] then last else some (block.getLastD marker))
              remaining := by
  cases block with
  | nil =>
      simp
  | cons letter tail =>
      have letterSimple : word.toList.count letter = 1 :=
        blockSimple letter (by simp)
      have tailSimple :
          ∀ candidate ∈ tail,
            word.toList.count candidate = 1 := by
        intro candidate member
        exact blockSimple candidate (by simp [member])
      have decoration :
          prefixPredecessorDecoration
            word (before ++ [marker]) last =
              emittedMarkerSquare last marker := by
        simp [prefixPredecessorDecoration, emittedMarkerSquare,
          List.reverse_append, markerRepeated]
      have tailStep :=
        stablePredecessorStreamingFold_simpleTail
          word tail (before ++ [marker]) seen letter remaining
          letterSimple tailSimple
      simp only [List.cons_append, stablePredecessorStreamingFold,
        letterSimple, ↓reduceIte]
      rw [decoration, tailStep]
      simp only [List.cons_ne_nil, if_false, List.getLastD_cons]
      simp [List.append_assoc]

/-- The final element of a nonempty appended suffix is independent of the
arbitrary earlier prefix and fallback. -/
theorem getLastD_append_cons
    (before : List Nat) (head fallback : Nat)
    (after : List Nat) :
    (before ++ head :: after).getLastD fallback =
      after.getLastD head := by
  induction before generalizing fallback with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest inductionHypothesis =>
      simp only [List.cons_append, List.getLastD_cons]
      exact inductionHypothesis letter

/-- A literal nonempty source suffix determines the actual `Word.final`;
no globally dropped final guard is assumed. -/
theorem final_eq_getLastD_of_split
    (word : Word Nat) (before after : List Nat) (head : Nat)
    (split : word.toList = before ++ head :: after) :
    word.final = after.getLastD head := by
  cases word with
  | mk actualHead actualTail =>
      have final :=
        congrArg
          (fun letters : List Nat => letters.getLastD actualHead)
          split
      simpa only [Word.toList, Word.final,
        List.getLastD_cons, getLastD_append_cons] using final

/-- For a genuinely repeated final letter, the already-proved signature
decoration is exactly the relative missing-square emission. -/
theorem signatureFinalDecoration_eq_emittedMarkerSquare
    (word : Word Nat) (last : Option Nat) (marker : Nat)
    (final : word.final = marker)
    (repeated : word.toList.count marker ≠ 1) :
    signatureFinalDecoration word last =
      emittedMarkerSquare last marker := by
  simp [signatureFinalDecoration, emittedMarkerSquare,
    final, repeated]

/-- For a globally simple actual final letter, final decoration is empty. -/
theorem signatureFinalDecoration_eq_nil_of_simple
    (word : Word Nat) (last : Option Nat)
    (simple : word.toList.count word.final = 1) :
    signatureFinalDecoration word last = [] := by
  simp [signatureFinalDecoration, simple]

/-- Every already-emitted repeated final symbol belongs to scanner support. -/
def LastRepeatedSeenInvariant
    (word : Word Nat) (seen : List Nat) (last : Option Nat) : Prop :=
  ∀ marker,
    word.toList.count marker ≠ 1 →
      last = some marker → marker ∈ seen

/-- Advancing past a repeated marker and a globally simple block preserves
the precise emitted-last / repeated-support state relation. -/
theorem lastRepeatedSeen_after_factor
    (word : Word Nat) (seen : List Nat)
    (marker : Nat) (block : List Nat)
    (blockSimple :
      ∀ letter ∈ block, word.toList.count letter = 1) :
    LastRepeatedSeenInvariant word
      (seen ++ [marker]) (some (block.getLastD marker)) := by
  intro candidate repeated last
  have same : block.getLastD marker = candidate := Option.some.inj last
  by_cases empty : block = []
  · subst block
    simp at same
    subst candidate
    simp
  · have simple : word.toList.count (block.getLastD marker) = 1 :=
      blockSimple (block.getLastD marker)
        (getLastD_mem_of_nonempty block marker empty)
    rw [same] at simple
    exact False.elim (repeated simple)

/-- Appending a marker already present in repeated support preserves exact
membership and may be used to synchronize factor and raw streaming states. -/
theorem repeatedSupport_append_existing_congr
    (seen : List Nat) (marker : Nat)
    (present : marker ∈ seen) :
    ∀ candidate,
      candidate ∈ seen ↔ candidate ∈ seen ++ [marker] := by
  intro candidate
  constructor
  · intro member
    simp [member]
  · intro member
    have alternatives : candidate ∈ seen ∨ candidate = marker := by
      simpa using member
    rcases alternatives with already | same
    · exact already
    · simpa [same] using present

/-- The final-factor case is discharged separately, exactly as fable's cut
requires: a repeated final marker decorates once, while a simple final
letter never decorates. -/
theorem stablePredecessorStreamingFold_singleFinalFactor
    (word : Word Nat) (before seen : List Nat)
    (last : Option Nat) (marker : Nat) (block : List Nat)
    (split :
      word.toList =
        before ++ renderSuccessorFactors [(marker, block)])
    (markerRepeated : word.toList.count marker ≠ 1)
    (blockSimple :
      ∀ letter ∈ block, word.toList.count letter = 1)
    (lastSeen : LastRepeatedSeenInvariant word seen last) :
    stablePredecessorStreamingFold word before seen last
        (renderSuccessorFactors [(marker, block)]) =
      emittedMarkerSquare last marker ++ block := by
  have actualFinal : word.final = block.getLastD marker := by
    apply final_eq_getLastD_of_split word before block marker
    simpa [renderSuccessorFactors, renderSuccessorFactor,
      List.append_assoc] using split
  by_cases present : marker ∈ seen
  · cases block with
    | nil =>
        have final : word.final = marker := by
          simpa using actualFinal
        simp [renderSuccessorFactors, renderSuccessorFactor,
          stablePredecessorStreamingFold, markerRepeated, present,
          signatureFinalDecoration, emittedMarkerSquare, final]
    | cons first tail =>
        have finalSimple : word.toList.count word.final = 1 := by
          rw [actualFinal]
          exact blockSimple ((first :: tail).getLastD marker)
            (getLastD_mem_of_nonempty (first :: tail) marker (by simp))
        have processed :=
          stablePredecessorStreamingFold_simpleBlock_afterMarker
            word before seen last marker (first :: tail) []
            markerRepeated blockSimple
        have processedClean :
            stablePredecessorStreamingFold
                word (before ++ [marker]) seen last (first :: tail) =
              emittedMarkerSquare last marker ++ (first :: tail) := by
          simpa [stablePredecessorStreamingFold,
            signatureFinalDecoration, finalSimple,
            List.append_assoc] using processed
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          stablePredecessorStreamingFold, markerRepeated,
          present] using processedClean
  · have lastDifferent : last ≠ some marker := by
      intro same
      exact present (lastSeen marker markerRepeated same)
    cases block with
    | nil =>
        have final : word.final = marker := by
          simpa using actualFinal
        simp [renderSuccessorFactors, renderSuccessorFactor,
          stablePredecessorStreamingFold, markerRepeated, present,
          signatureFinalDecoration, emittedMarkerSquare,
          final, lastDifferent]
    | cons first tail =>
        have finalSimple : word.toList.count word.final = 1 := by
          rw [actualFinal]
          exact blockSimple ((first :: tail).getLastD marker)
            (getLastD_mem_of_nonempty (first :: tail) marker (by simp))
        have processed :=
          stablePredecessorStreamingFold_simpleBlock_afterMarker
            word before (seen ++ [marker]) (some marker)
            marker (first :: tail) [] markerRepeated blockSimple
        have processedClean :
            stablePredecessorStreamingFold
                word (before ++ [marker]) (seen ++ [marker])
                  (some marker) (first :: tail) =
              first :: tail := by
          simpa [stablePredecessorStreamingFold,
            signatureFinalDecoration, finalSimple,
            emittedMarkerSquare, List.append_assoc] using processed
        have appended :=
          congrArg (fun output : List Nat => [marker, marker] ++ output)
            processedClean
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          stablePredecessorStreamingFold, markerRepeated, present,
          emittedMarkerSquare, lastDifferent,
          List.append_assoc] using appended

/-- Fable's exact suffix induction.  Every nonfinal seen-empty marker is
dropped, every adjacent-equal boundary is merged, and the final factor is
handled by the separately proved terminal-decoration lemma. -/
theorem stablePredecessorStreamingFold_eq_finalFactorFold
    (word : Word Nat) :
    ∀ (factors : List SuccessorFactor)
      (before seen : List Nat) (last : Option Nat),
      factors ≠ [] →
      word.toList = before ++ renderSuccessorFactors factors →
      (∀ factor ∈ factors, word.toList.count factor.1 ≠ 1) →
      (∀ factor ∈ factors,
        ∀ letter ∈ factor.2, word.toList.count letter = 1) →
      LastRepeatedSeenInvariant word seen last →
      stablePredecessorStreamingFold word before seen last
          (renderSuccessorFactors factors) =
        finalFactorFold seen last factors
  | [], _, _, _, nonempty, _, _, _, _ => by
      exact False.elim (nonempty rfl)
  | [(marker, block)], before, seen, last,
      _, split, markersRepeated, blocksSimple, lastSeen => by
      have markerRepeated : word.toList.count marker ≠ 1 :=
        markersRepeated (marker, block) (by simp)
      have blockSimple :
          ∀ letter ∈ block, word.toList.count letter = 1 := by
        intro letter member
        exact blocksSimple (marker, block) (by simp) letter member
      simpa [finalFactorFold] using
        stablePredecessorStreamingFold_singleFinalFactor
          word before seen last marker block split
          markerRepeated blockSimple lastSeen
  | (marker, block) :: next :: rest,
      before, seen, last,
      _, split, markersRepeated, blocksSimple, lastSeen => by
      have markerRepeated : word.toList.count marker ≠ 1 :=
        markersRepeated (marker, block) (by simp)
      have blockSimple :
          ∀ letter ∈ block, word.toList.count letter = 1 := by
        intro letter member
        exact blocksSimple (marker, block) (by simp) letter member
      have tailRepeated :
          ∀ factor ∈ next :: rest,
            word.toList.count factor.1 ≠ 1 := by
        intro factor member
        exact markersRepeated factor (by simp [member])
      have tailSimple :
          ∀ factor ∈ next :: rest,
            ∀ letter ∈ factor.2, word.toList.count letter = 1 := by
        intro factor member letter letterMember
        exact blocksSimple factor (by simp [member]) letter letterMember
      have tailSplit :
          word.toList =
            ((before ++ [marker]) ++ block) ++
              renderSuccessorFactors (next :: rest) := by
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          List.append_assoc] using split
      by_cases drop : block = [] ∧ marker ∈ seen
      · rcases drop with ⟨empty, present⟩
        subst block
        have tail :=
          stablePredecessorStreamingFold_eq_finalFactorFold
            word (next :: rest) (before ++ [marker]) seen last
            (by simp) (by simpa using tailSplit)
            tailRepeated tailSimple lastSeen
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          stablePredecessorStreamingFold, finalFactorFold,
          markerRepeated, present, List.append_assoc] using tail
      · by_cases present : marker ∈ seen
        · have blockNonempty : block ≠ [] := by
            intro empty
            exact drop ⟨empty, present⟩
          have processed :=
            stablePredecessorStreamingFold_simpleBlock_afterMarker
              word before seen last marker block
              (renderSuccessorFactors (next :: rest))
              markerRepeated blockSimple
          have processedClean :
              stablePredecessorStreamingFold
                  word (before ++ [marker]) seen last
                    (block ++
                      renderSuccessorFactors (next :: rest)) =
                emittedMarkerSquare last marker ++ block ++
                  stablePredecessorStreamingFold
                    word ((before ++ [marker]) ++ block) seen
                      (some (block.getLastD marker))
                      (renderSuccessorFactors (next :: rest)) := by
            simpa [blockNonempty] using processed
          have seenChange :=
            stablePredecessorStreamingFold_seen_congr word
              (renderSuccessorFactors (next :: rest))
              ((before ++ [marker]) ++ block)
              seen (seen ++ [marker])
              (some (block.getLastD marker))
              (repeatedSupport_append_existing_congr
                seen marker present)
          have nextInvariant :=
            lastRepeatedSeen_after_factor word seen marker block blockSimple
          have tail :=
            stablePredecessorStreamingFold_eq_finalFactorFold
              word (next :: rest)
              ((before ++ [marker]) ++ block)
              (seen ++ [marker]) (some (block.getLastD marker))
              (by simp) tailSplit tailRepeated tailSimple nextInvariant
          have first :
              stablePredecessorStreamingFold word before seen last
                  (renderSuccessorFactors
                    ((marker, block) :: next :: rest)) =
                stablePredecessorStreamingFold
                  word (before ++ [marker]) seen last
                    (block ++ renderSuccessorFactors (next :: rest)) := by
            simp [renderSuccessorFactors, renderSuccessorFactor,
              stablePredecessorStreamingFold, markerRepeated, present]
          rw [finalFactorFold, if_neg drop]
          exact first.trans <|
            processedClean.trans <|
              (congrArg
                (fun output : List Nat =>
                  emittedMarkerSquare last marker ++ block ++ output)
                seenChange).trans <|
                congrArg
                  (fun output : List Nat =>
                    emittedMarkerSquare last marker ++ block ++ output)
                  tail
        · have lastDifferent : last ≠ some marker := by
            intro same
            exact present (lastSeen marker markerRepeated same)
          have processed :=
            stablePredecessorStreamingFold_simpleBlock_afterMarker
              word before (seen ++ [marker]) (some marker)
              marker block (renderSuccessorFactors (next :: rest))
              markerRepeated blockSimple
          have processedClean :
              stablePredecessorStreamingFold
                  word (before ++ [marker]) (seen ++ [marker])
                    (some marker)
                    (block ++ renderSuccessorFactors (next :: rest)) =
                block ++
                  stablePredecessorStreamingFold
                    word ((before ++ [marker]) ++ block)
                      (seen ++ [marker])
                      (some (block.getLastD marker))
                      (renderSuccessorFactors (next :: rest)) := by
            cases block with
            | nil =>
                simp
            | cons first tail =>
                simpa [emittedMarkerSquare] using processed
          have nextInvariant :=
            lastRepeatedSeen_after_factor word seen marker block blockSimple
          have tail :=
            stablePredecessorStreamingFold_eq_finalFactorFold
              word (next :: rest)
              ((before ++ [marker]) ++ block)
              (seen ++ [marker]) (some (block.getLastD marker))
              (by simp) tailSplit tailRepeated tailSimple nextInvariant
          have first :
              stablePredecessorStreamingFold word before seen last
                  (renderSuccessorFactors
                    ((marker, block) :: next :: rest)) =
                [marker, marker] ++
                  stablePredecessorStreamingFold
                    word (before ++ [marker]) (seen ++ [marker])
                      (some marker)
                      (block ++ renderSuccessorFactors (next :: rest)) := by
            simp [renderSuccessorFactors, renderSuccessorFactor,
              stablePredecessorStreamingFold, markerRepeated, present]
          rw [finalFactorFold, if_neg drop]
          simp only [emittedMarkerSquare, lastDifferent, ↓reduceIte]
          exact first.trans <|
            (congrArg
              (fun output : List Nat => [marker, marker] ++ output)
              processedClean).trans <|
              congrArg
                (fun output : List Nat =>
                  [marker, marker] ++ block ++ output)
                tail

/-- A globally simple already-emitted symbol can never merge with the first
globally repeated factor marker. -/
theorem renderSquaredFactorsAfter_simpleLast
    (whole : List Nat) (last : Nat)
    (factors : List SuccessorFactor)
    (lastSimple : whole.count last = 1)
    (markersRepeated :
      ∀ factor ∈ factors, whole.count factor.1 ≠ 1) :
    renderSquaredFactorsAfter (some last) factors =
      renderSquaredSuccessorFactors factors := by
  cases factors with
  | nil =>
      rfl
  | cons factor rest =>
      rcases factor with ⟨marker, block⟩
      have repeated : whole.count marker ≠ 1 :=
        markersRepeated (marker, block) (by simp)
      have different : last ≠ marker := by
        intro same
        rw [same] at lastSimple
        exact repeated lastSimple
      simp [renderSquaredFactorsAfter, emittedMarkerSquare,
        renderSquaredSuccessorFactors, different]

/-- A globally simple initial block leaves the factor continuation in exactly
the same output state as an empty emitted prefix. -/
theorem finalFactorFold_simpleLast_eq_none
    (whole : List Nat) (factors : List SuccessorFactor)
    (seen : List Nat) (last : Nat)
    (lastSimple : whole.count last = 1)
    (markersRepeated :
      ∀ factor ∈ factors, whole.count factor.1 ≠ 1)
    (blocksSimple :
      ∀ factor ∈ factors,
        ∀ letter ∈ factor.2, whole.count letter = 1) :
    finalFactorFold seen (some last) factors =
      finalFactorFold seen none factors := by
  have normalizedRepeated :
      ∀ factor ∈
          collapseAdjacentEmptySameFactors
            (retainFirstBlockOrFinalFactors seen factors),
        whole.count factor.1 ≠ 1 := by
    intro factor member
    exact markersRepeated factor <|
      mem_retainFirstBlockOrFinalFactors factor factors seen <|
        mem_collapseAdjacentEmptySameFactors factor
          (retainFirstBlockOrFinalFactors seen factors) member
  have withLast :=
    finalFactorFold_eq_relativeCanonical
      whole factors seen (some last) markersRepeated blocksSimple
  have withoutLast :=
    finalFactorFold_eq_relativeCanonical
      whole factors seen none markersRepeated blocksSimple
  calc
    finalFactorFold seen (some last) factors =
        renderSquaredFactorsAfter (some last)
          (collapseAdjacentEmptySameFactors
            (retainFirstBlockOrFinalFactors seen factors)) :=
      withLast.symm
    _ = renderSquaredSuccessorFactors
          (collapseAdjacentEmptySameFactors
            (retainFirstBlockOrFinalFactors seen factors)) :=
      renderSquaredFactorsAfter_simpleLast whole last
        (collapseAdjacentEmptySameFactors
          (retainFirstBlockOrFinalFactors seen factors))
        lastSimple normalizedRepeated
    _ = finalFactorFold seen none factors := by
      simpa using withoutLast

/-- All globally multiple historical successor markers satisfy the exact
state-assembly repeatedness premise. -/
theorem successorMarkers_repeated
    (letters : List Nat) :
    ∀ factor ∈ successorFactors letters,
      letters.count factor.1 ≠ 1 := by
  intro factor member
  have multiple :=
    successorFactor_marker_multiple letters factor.2 factor.1 member
  omega

/-- All historical successor blocks satisfy the exact state-assembly global
simplicity premise, independently of their local block positions. -/
theorem successorBlocks_simple
    (letters : List Nat) :
    ∀ factor ∈ successorFactors letters,
      ∀ letter ∈ factor.2, letters.count letter = 1 := by
  intro factor member letter letterMember
  exact successorFactor_block_letter_simple
    letters factor.2 factor.1 letter member letterMember

/-- Full final-separated assembly: the raw prefix-generalized scanner and
the exact reachable corrected historical factor canonical agree on every
alphabet and every nonempty word. -/
theorem stablePredecessorStreamingFold_eq_ownerCanonical
    (word : Word Nat) :
    stablePredecessorStreamingFold word [] [] none word.toList =
      firstOrderPredecessorCanonicalList word.toList := by
  let initial := initialSimpleBlock word.toList
  let factors := successorFactors word.toList
  have decomposition :
      word.toList = initial ++ renderSuccessorFactors factors :=
    (reconstruct word.toList).symm
  have markersRepeated :
      ∀ factor ∈ factors,
        word.toList.count factor.1 ≠ 1 :=
    successorMarkers_repeated word.toList
  have blocksSimple :
      ∀ factor ∈ factors,
        ∀ letter ∈ factor.2, word.toList.count letter = 1 :=
    successorBlocks_simple word.toList
  cases initialShape : initial with
  | nil =>
      have sourceShape :
          word.toList = renderSuccessorFactors factors := by
        simpa [initialShape] using decomposition
      have factorsNonempty : factors ≠ [] := by
        intro empty
        rw [empty] at sourceShape
        cases word with
        | mk head tail =>
            simp [renderSuccessorFactors, Word.toList] at sourceShape
      have emptyInvariant :
          LastRepeatedSeenInvariant word [] none := by
        intro marker _ impossible
        cases impossible
      have folded :=
        stablePredecessorStreamingFold_eq_finalFactorFold word factors
          [] [] none factorsNonempty (by simpa using sourceShape)
          markersRepeated blocksSimple emptyInvariant
      have canonical := finalFactorFold_eq_ownerCanonical word.toList
      calc
        stablePredecessorStreamingFold word [] [] none word.toList =
            finalFactorFold [] none factors := by
          simpa [sourceShape] using folded
        _ = firstOrderPredecessorCanonicalList word.toList := by
          simpa [firstOrderPredecessorCanonicalList,
            initial, initialShape, factors] using canonical
  | cons first tail =>
      have initialIdentity :
          initialSimpleBlock word.toList = first :: tail := by
        exact initialShape
      have firstSimple : word.toList.count first = 1 :=
        initialSimpleBlock_letter_simple word.toList first <| by
          rw [initialIdentity]
          simp
      have tailSimple :
          ∀ letter ∈ tail, word.toList.count letter = 1 := by
        intro letter member
        apply initialSimpleBlock_letter_simple word.toList letter
        rw [initialIdentity]
        simp [member]
      have lastSimple :
          word.toList.count (tail.getLastD first) = 1 := by
        apply initialSimpleBlock_letter_simple word.toList
          (tail.getLastD first)
        rw [initialIdentity]
        exact List.getLastD_mem_cons (l := tail) (a := first)
      have sourceShape :
          word.toList =
            (first :: tail) ++ renderSuccessorFactors factors := by
        simpa [initialShape] using decomposition
      have firstStep :
          stablePredecessorStreamingFold word [] [] none word.toList =
            first ::
              stablePredecessorStreamingFold
                word [first] [] (some first)
                  (tail ++ renderSuccessorFactors factors) := by
        rw [sourceShape]
        simp [stablePredecessorStreamingFold,
          prefixPredecessorDecoration, firstSimple]
      have tailStep :=
        stablePredecessorStreamingFold_simpleTail word tail [] [] first
          (renderSuccessorFactors factors) firstSimple tailSimple
      have processedInitial :
          stablePredecessorStreamingFold word [] [] none word.toList =
            (first :: tail) ++
              stablePredecessorStreamingFold
                word (first :: tail) [] (some (tail.getLastD first))
                  (renderSuccessorFactors factors) := by
        simpa [List.append_assoc] using
          firstStep.trans
            (congrArg (fun output : List Nat => first :: output) tailStep)
      cases factorsShape : factors with
      | nil =>
          have noFactors : successorFactors word.toList = [] := by
            simpa [factors] using factorsShape
          have sourceSimple :
              word.toList.count word.final = 1 := by
            have final :=
              final_eq_getLastD_of_split word [] tail first <| by
                simpa [factorsShape, renderSuccessorFactors] using sourceShape
            rw [final]
            exact lastSimple
          calc
            stablePredecessorStreamingFold word [] [] none word.toList =
                first :: tail := by
              simpa [factorsShape, renderSuccessorFactors,
                stablePredecessorStreamingFold,
                signatureFinalDecoration, sourceSimple] using
                  processedInitial
            _ = firstOrderPredecessorCanonicalList word.toList := by
              simp [firstOrderPredecessorCanonicalList,
                initialIdentity, noFactors,
                retainFirstBlockOrFinalFactors,
                collapseAdjacentEmptySameFactors,
                renderSquaredSuccessorFactors]
      | cons head rest =>
          have nonempty : factors ≠ [] := by
            simp [factorsShape]
          have initialInvariant :
              LastRepeatedSeenInvariant word []
                (some (tail.getLastD first)) := by
            intro marker repeated same
            have equal : tail.getLastD first = marker :=
              Option.some.inj same
            rw [equal] at lastSimple
            exact False.elim (repeated lastSimple)
          have folded :=
            stablePredecessorStreamingFold_eq_finalFactorFold word factors
              (first :: tail) [] (some (tail.getLastD first))
              nonempty sourceShape markersRepeated blocksSimple
              initialInvariant
          have removeSimpleLast :=
            finalFactorFold_simpleLast_eq_none word.toList factors []
              (tail.getLastD first) lastSimple
              markersRepeated blocksSimple
          have canonical := finalFactorFold_eq_ownerCanonical word.toList
          calc
            stablePredecessorStreamingFold word [] [] none word.toList =
                (first :: tail) ++
                  finalFactorFold [] (some (tail.getLastD first)) factors :=
              processedInitial.trans <|
                congrArg (fun output : List Nat =>
                  (first :: tail) ++ output) folded
            _ = (first :: tail) ++ finalFactorFold [] none factors := by
              rw [removeSimpleLast]
            _ = firstOrderPredecessorCanonicalList word.toList := by
              simp only [firstOrderPredecessorCanonicalList,
                initialIdentity]
              exact congrArg
                (fun output : List Nat => (first :: tail) ++ output)
                canonical

/-- Fable's exact single missing factor/streaming obligation is now proved
unconditionally; it is no longer an owner-supplied premise. -/
theorem correctedSuccessorFactorStreamingAgreement :
    CorrectedSuccessorFactorStreamingAgreement := by
  intro word
  exact (stablePredecessorStreamingFold_eq_ownerCanonical word).symm

/-- The already proved full semantic streaming state immediately yields the
exact previously conditional unrestricted corrected-scanner signature law. -/
theorem stablePredecessorScannerSignatureAgreement :
    StablePredecessorScannerSignatureAgreement :=
  correctedFactorStreamingAgreement_iff_scannerSignatureAgreement.mp
    correctedSuccessorFactorStreamingAgreement

/-- Full original first-occurrence order now genuinely lifts every complete
opposite-factor lower derivation in the authenticated FOUR-law basis. -/
theorem firstOccurrencePreservingSimplePredecessorLift :
    FirstOccurrencePreservingSimplePredecessorLift :=
  stablePredecessorScannerAgreement_implies_ownerLift
    stablePredecessorScannerSignatureAgreement

/-- Independently complete unrestricted intersection for the actual frozen
`S3_16 × S5_402ᵒᵖ` factor pair. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  intersectionBasis_of_simplePredecessorLift
    firstOccurrencePreservingSimplePredecessorLift

/-- Certified reusable rank-091 family normalizer with no owner premises. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The final authenticated noncollision `S3_16` class is unconditional. -/
theorem s6_8453_representative_basis :
    BasisFor S6_8453.table.semigroup basis :=
  S6_8453.representative_basis_of_normalizer normalizer

/-- The opposite orientation retains the exact reversed frozen four-law list. -/
theorem s6_8453_opposite_basis :
    BasisFor S6_8453.table.semigroup.opposite (reversedBasis basis) :=
  S6_8453.opposite_basis_of_normalizer normalizer

/-- Reviewed shared transport preserves literal displayed-law derivations
and the two independent unrestricted factor-theory implications. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091.Seed
