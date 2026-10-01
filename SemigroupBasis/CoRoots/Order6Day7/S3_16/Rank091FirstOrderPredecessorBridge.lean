import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_402
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_402Opposite
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner

/-!
# Exact rank-091 first-occurrence / simple-predecessor owner bridge

The immutable four-law `S3_16 × S5_402ᵒᵖ` presentation must preserve the
COMPLETE first-occurrence sequence as well as the independently complete
opposite-factor capped-multiplicity / globally-simple immediate-predecessor
signature.  The kernel-green rank-090 direct-factor seed, and the independently
complete historical `S2_4 × S5_402ᵒᵖ` seed, cannot simply be replayed because
their respective terminal and full-first-occurrence invariants differ.

This source proves exact factor semantics, genuine displayed-law derivations,
and stable order-preserving successor-factor reachability before asserting any
unrestricted owner intersection or class endpoint.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 14000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091.FirstOrderPredecessorBridge

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The actual frozen left factor determines COMPLETE first-occurrence order. -/
theorem firstOccurrences_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
    identity valid

/-- Complete LRB normalization makes full first order exactly sufficient. -/
theorem leftValid_of_firstOccurrences
    (identity : Identity Nat)
    (same : firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList) :
    identity.SatisfiedBy leftTable.semigroup :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.leftValid_of_firstOccurrences
    identity same

/-- The actual opposite right factor supplies the complete direct signature
on the TWO reversed words, not on the original words. -/
theorem reversedSuccessor_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs.reverse identity.rhs.reverse := by
  apply
    SemigroupBasis.CoRoots.Order6LeeZhang23_9Invariant.rightFactorValid_reversedS5_402
      identity
  exact valid

/-- Independent complete direct `S5_402` semantics also prove sufficiency of
the literal reversed-word opposite signature. -/
theorem rightValid_of_reversedSuccessor
    (identity : Identity Nat)
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs.reverse identity.rhs.reverse) :
    identity.SatisfiedBy rightTable.semigroup := by
  have lower :=
    SemigroupBasis.CoRoots.S5_402.derivesOfSameSimpleSuccessorSignature same
  have direct :
      identity.reversed.SatisfiedBy
        SemigroupBasis.CoRoots.S5_402.table.semigroup := by
    simpa [Identity.reversed] using
      lower.sound SemigroupBasis.CoRoots.S5_402.models
  change
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_402.table.semigroup.opposite
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.CoRoots.S5_402.table.semigroup).mpr direct

/-- The exact joint semantic descriptor; neither the first-order coordinate
nor the opposite-factor orientation is truncated. -/
structure SameFirstOrderSimplePredecessorSignature
    (left right : Word Nat) : Prop where
  firstOrder :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  reversedSuccessor :
    SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse

/-- Exact unrestricted equivalence of the real pair and its full signature. -/
theorem sameSignature_iff_factorValidity
    (identity : Identity Nat) :
    SameFirstOrderSimplePredecessorSignature identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧
        identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro same
    exact ⟨leftValid_of_firstOccurrences identity same.firstOrder,
      rightValid_of_reversedSuccessor identity same.reversedSuccessor⟩
  · rintro ⟨leftValid, rightValid⟩
    exact ⟨firstOccurrences_of_leftValid identity leftValid,
      reversedSuccessor_of_rightValid identity rightValid⟩

/-- Full first-order equality implies the literal initial variable. -/
theorem head_eq_of_firstOccurrences
    (left right : Word Nat)
    (same :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    left.head = right.head := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have heads := congrArg List.head? same
          simpa [Word.toList, firstOccurrenceSequence] using heads

/-- The complete historical opposite-factor signature is strictly weaker:
the new left owner contributes its entire first-occurrence sequence. -/
theorem historicalSignature_of_fullSignature
    {left right : Word Nat}
    (same : SameFirstOrderSimplePredecessorSignature left right) :
    SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax.SameLeeZhang23_9Signature
      left right :=
  ⟨head_eq_of_firstOccurrences left right same.firstOrder,
    same.reversedSuccessor⟩

/-! ## Genuine exact four-law derivations -/

/-- Frozen law 00 expands any genuine square. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    (Derives.fromBasis (e := law00) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 duplicates the left occurrence of a repeated whole word. -/
theorem derivesLeftDuplication (first middle : Word Nat) :
    Derives basis
      ((first ++ middle) ++ first)
      (((first ++ first) ++ middle) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) :=
    (Derives.fromBasis (e := law01) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 02 duplicates the right occurrence of a repeated whole word. -/
theorem derivesRightDuplication (first middle : Word Nat) :
    Derives basis
      ((first ++ middle) ++ first)
      (((first ++ middle) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) :=
    (Derives.fromBasis (e := law02) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 03 moves a repeated marker left before an ACTUAL final square. -/
theorem derivesTerminalSquareMove
    (first middle final : Word Nat) :
    Derives basis
      ((((first ++ middle) ++ first) ++ final) ++ final)
      ((((first ++ first) ++ middle) ++ final) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2, 2])
        (Word.mk 0 [0, 1, 2, 2]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The opposite lower square alternation is a genuine THREE-step
four-law derivation; the invalid direct-factor square crossing is not used. -/
theorem derivesSquareAlternation (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ second)
      (((first ++ second) ++ first) ++ second) := by
  have expand :
      Derives basis
        (((first ++ first) ++ second) ++ second)
        ((((first ++ first) ++ second) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first) (derivesPowerExpansion second)
  have move :
      Derives basis
        ((((first ++ first) ++ second) ++ second) ++ second)
        ((((first ++ second) ++ first) ++ second) ++ second) :=
    (derivesTerminalSquareMove first second second).symm
  have contract :
      Derives basis
        ((((first ++ second) ++ first) ++ second) ++ second)
        (((first ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first (derivesRightDuplication second first).symm
  exact expand.trans (move.trans contract)

/-- The reversed lower factor-middle move needs whole-word substitution in
the frozen terminal-square law; singleton-only replay cannot derive it. -/
theorem derivesReverseFactorMiddleLeft
    (first second third : Word Nat) :
    Derives basis
      ((((first ++ second) ++ first) ++ third) ++ third)
      ((((first ++ second) ++ third) ++ first) ++ third) := by
  have expand :
      Derives basis
        ((((first ++ second) ++ first) ++ third) ++ third)
        (((((first ++ second) ++ first) ++ third) ++ third) ++ third) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((first ++ second) ++ first)
        (derivesPowerExpansion third)
  have direct :=
    Derives.appendRight
      (derivesTerminalSquareMove first second third) third
  have direct' :
      Derives basis
        (((((first ++ second) ++ first) ++ third) ++ third) ++ third)
        (((((first ++ first) ++ second) ++ third) ++ third) ++ third) := by
    simpa [Word.append_assoc] using direct
  have whole :=
    (derivesTerminalSquareMove first (second ++ third) third).symm
  have whole' :
      Derives basis
        (((((first ++ first) ++ second) ++ third) ++ third) ++ third)
        (((((first ++ second) ++ third) ++ first) ++ third) ++ third) := by
    simpa [Word.append_assoc] using whole
  have contract :
      Derives basis
        (((((first ++ second) ++ third) ++ first) ++ third) ++ third)
        ((((first ++ second) ++ third) ++ first) ++ third) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ second)
        (derivesRightDuplication third first).symm
  exact expand.trans (direct'.trans (whole'.trans contract))

/-- The reversed simple-successor shift is a genuine THREE-step whole-word
derivation in the exact four-law package. -/
theorem derivesReverseSimpleSuccessorShift
    (first second third : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ third) ++ second)
      ((((first ++ second) ++ third) ++ first) ++ second) := by
  have expand :
      Derives basis
        ((((first ++ first) ++ second) ++ third) ++ second)
        (((((first ++ first) ++ second) ++ third) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesRightDuplication second third)
  have whole :=
    (derivesTerminalSquareMove first (second ++ third) second).symm
  have whole' :
      Derives basis
        (((((first ++ first) ++ second) ++ third) ++ second) ++ second)
        (((((first ++ second) ++ third) ++ first) ++ second) ++ second) := by
    simpa [Word.append_assoc] using whole
  have contract :
      Derives basis
        (((((first ++ second) ++ third) ++ first) ++ second) ++ second)
        ((((first ++ second) ++ third) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first
        (derivesRightDuplication second (third ++ first)).symm
  exact expand.trans (whole'.trans contract)

/-! ## Stable first-order-preserving successor-factor reachability -/

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- Duplicate the left occurrence of any scattered repeated marker. -/
theorem listDerivesExpandLeftOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter, letter] ++ middle ++ [letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            derivesLeftDuplication
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Duplicate the right occurrence of any scattered repeated marker. -/
theorem listDerivesExpandRightOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter] ++ middle ++ [letter, letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
            derivesRightDuplication
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Every globally repeated marker occurrence can be squared in place. -/
theorem listDerivesDuplicateSelectedOccurrence
    (letter : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [letter] ++ after).count letter) :
    ListDerives
      (before ++ [letter] ++ after)
      (before ++ [letter, letter] ++ after) := by
  by_cases afterMember : letter ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesExpandLeftOccurrence letter middle).context
        before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : letter ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count letter = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count letter = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [letter] ++ after).count letter = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesExpandRightOccurrence letter middle).context
        beforePrefix after
    simpa [split, List.append_assoc] using expanded

/-- Render every historical successor marker twice, followed by its honest
globally-simple successor block. -/
def renderSquaredSuccessorFactors :
    List SuccessorFactor → List Nat
  | [] => []
  | (marker, block) :: rest =>
      [marker, marker] ++ block ++
        renderSquaredSuccessorFactors rest

@[simp] theorem renderSquaredSuccessorFactors_append
    (left right : List SuccessorFactor) :
    renderSquaredSuccessorFactors (left ++ right) =
      renderSquaredSuccessorFactors left ++
        renderSquaredSuccessorFactors right := by
  induction left with
  | nil =>
      simp [renderSquaredSuccessorFactors]
  | cons factor rest inductionHypothesis =>
      rcases factor with ⟨marker, block⟩
      simp [renderSquaredSuccessorFactors,
        inductionHypothesis, List.append_assoc]

/-- Square each independently certified globally multiple successor marker. -/
theorem listDerivesSquareSuccessorFactorsAux :
    ∀ (factors : List SuccessorFactor) (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤
          (before ++ renderSuccessorFactors factors).count factor.1) →
      ListDerives
        (before ++ renderSuccessorFactors factors)
        (before ++ renderSquaredSuccessorFactors factors)
  | [], before, _ => by
      simpa [renderSuccessorFactors, renderSquaredSuccessorFactors] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) before)
  | (marker, block) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤
            (before ++ [marker] ++
              (block ++ renderSuccessorFactors rest)).count marker := by
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          List.append_assoc] using
            multiples (marker, block) (by simp)
      have firstRaw :=
        listDerivesDuplicateSelectedOccurrence
          marker before (block ++ renderSuccessorFactors rest)
          markerMultiple
      have firstStep :
          ListDerives
            (before ++ renderSuccessorFactors
              ((marker, block) :: rest))
            ((before ++ [marker, marker] ++ block) ++
              renderSuccessorFactors rest) := by
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          List.append_assoc] using firstRaw
      have restMultiples :
          ∀ factor ∈ rest,
            2 ≤
              ((before ++ [marker, marker] ++ block) ++
                renderSuccessorFactors rest).count factor.1 := by
        intro factor member
        have oldMultiple :
            2 ≤
              (before ++ [marker] ++
                (block ++ renderSuccessorFactors rest)).count factor.1 := by
          simpa [renderSuccessorFactors, renderSuccessorFactor,
            List.append_assoc] using
              multiples factor (by simp [member])
        have monotone :=
          SemigroupBasis.CoRoots.S5_402.count_le_count_duplicateSelected
            factor.1 marker before
              (block ++ renderSuccessorFactors rest)
        have newMultiple := Nat.le_trans oldMultiple monotone
        simpa [List.append_assoc] using newMultiple
      have restStep :=
        listDerivesSquareSuccessorFactorsAux rest
          (before ++ [marker, marker] ++ block) restMultiples
      simpa [renderSquaredSuccessorFactors,
        List.append_assoc] using firstStep.trans restStep

/-- Every input reaches its literal opposite-oriented squared-factor scan. -/
theorem listDerivesSquareAllSuccessorMarkers
    (letters : List Nat) :
    ListDerives letters
      (initialSimpleBlock letters ++
        renderSquaredSuccessorFactors (successorFactors letters)) := by
  have multiples :
      ∀ factor ∈ successorFactors letters,
        2 ≤
          (initialSimpleBlock letters ++
            renderSuccessorFactors (successorFactors letters)).count
              factor.1 := by
    intro factor member
    rw [reconstruct letters]
    exact successorFactor_marker_multiple
      letters factor.2 factor.1 member
  have squared :=
    listDerivesSquareSuccessorFactorsAux
      (successorFactors letters) (initialSimpleBlock letters) multiples
  simpa [reconstruct letters] using squared

/-- Four repeated copies contract to two using only frozen power law 00. -/
theorem derivesPowerFourToTwo (first : Word Nat) :
    Derives basis (((first ++ first) ++ first) ++ first)
      (first ++ first) := by
  have firstStep :=
    Derives.prepend first (derivesPowerExpansion first).symm
  have fourToThree :
      Derives basis (((first ++ first) ++ first) ++ first)
        ((first ++ first) ++ first) := by
    simpa [Word.append_assoc] using firstStep
  exact fourToThree.trans (derivesPowerExpansion first).symm

/-- Delete an already-seen squared marker immediately BEFORE any genuine
next squared marker; the frozen terminal guard is never cancelled. -/
theorem listDerivesDropSeenMarkerBeforeNextSquare
    (marker nextMarker : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([marker, marker] ++ middle ++
          [marker, marker, nextMarker, nextMarker])
        ([marker, marker] ++ middle ++ [nextMarker, nextMarker])
  | [] => by
      have contracted :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesPowerFourToTwo (Word.singleton marker)).context
            [] [nextMarker, nextMarker]
      simpa [Word.singleton, Word.append,
        List.append_assoc] using contracted
  | head :: tail => by
      let middleWord := listWordOfCons head tail
      have contractLeft :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (derivesLeftDuplication
            (Word.singleton marker) middleWord).symm).context
              [] [marker, nextMarker, nextMarker]
      have firstStep :
          ListDerives
            ([marker, marker] ++ (head :: tail) ++
              [marker, marker, nextMarker, nextMarker])
            ([marker] ++ (head :: tail) ++
              [marker, marker, nextMarker, nextMarker]) := by
        simpa [middleWord, listWordOfCons, Word.singleton,
          Word.append, List.append_assoc] using contractLeft
      have contractRight :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (derivesRightDuplication
            (Word.singleton marker) middleWord).symm).context
              [] [nextMarker, nextMarker]
      have secondStep :
          ListDerives
            ([marker] ++ (head :: tail) ++
              [marker, marker, nextMarker, nextMarker])
            ([marker] ++ (head :: tail) ++
              [marker, nextMarker, nextMarker]) := by
        simpa [middleWord, listWordOfCons, Word.singleton,
          Word.append, List.append_assoc] using contractRight
      have moved :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesTerminalSquareMove
            (Word.singleton marker) middleWord
            (Word.singleton nextMarker)
      have thirdStep :
          ListDerives
            ([marker] ++ (head :: tail) ++
              [marker, nextMarker, nextMarker])
            ([marker, marker] ++ (head :: tail) ++
              [nextMarker, nextMarker]) := by
        simpa [middleWord, listWordOfCons, Word.singleton,
          Word.append, List.append_assoc] using moved
      exact firstStep.trans (secondStep.trans thirdStep)

/-- Project processed successor markers in their actual source order. -/
def successorFactorMarkers (factors : List SuccessorFactor) : List Nat :=
  factors.map Prod.fst

/-- Delete exactly one already-seen EMPTY successor factor when a genuine
later successor factor provides its terminal square guard. -/
theorem listDerivesDropSeenMarkerOnlyNonfinalFactor
    (before after : List SuccessorFactor)
    (marker : Nat)
    (represented : marker ∈ successorFactorMarkers before)
    (nonfinal : after ≠ []) :
    ListDerives
      (renderSquaredSuccessorFactors
        (before ++ [(marker, [])] ++ after))
      (renderSquaredSuccessorFactors (before ++ after)) := by
  obtain ⟨factor, factorMember, factorMarker⟩ :=
    List.mem_map.mp represented
  rcases factor with ⟨witnessMarker, witnessBlock⟩
  simp only at factorMarker
  subst witnessMarker
  obtain ⟨front, middle, split⟩ :=
    List.mem_iff_append.mp factorMember
  subst before
  cases after with
  | nil =>
      exact False.elim (nonfinal rfl)
  | cons next rest =>
      rcases next with ⟨nextMarker, nextBlock⟩
      have contracted :=
        (listDerivesDropSeenMarkerBeforeNextSquare
          marker nextMarker
          (witnessBlock ++ renderSquaredSuccessorFactors middle)).context
            (renderSquaredSuccessorFactors front)
            (nextBlock ++ renderSquaredSuccessorFactors rest)
      simpa [renderSquaredSuccessorFactors,
        List.append_assoc] using contracted

/-- Preserve every first marker, every nonempty globally-simple successor
block, and the ACTUAL final successor factor. -/
def retainFirstBlockOrFinalFactors
    (seen : List Nat) : List SuccessorFactor → List SuccessorFactor
  | [] => []
  | [factor] => [factor]
  | (marker, block) :: next :: rest =>
      if block = [] ∧ marker ∈ seen then
        retainFirstBlockOrFinalFactors seen (next :: rest)
      else
        (marker, block) ::
          retainFirstBlockOrFinalFactors
            (seen ++ [marker]) (next :: rest)

/-- Stably remove precisely the already-seen EMPTY NONFINAL factors. -/
theorem listDerivesRetainFirstBlockOrFinalFactorsAux
    (initial : List Nat) :
    ∀ (factors before : List SuccessorFactor),
      ListDerives
        (initial ++
          renderSquaredSuccessorFactors (before ++ factors))
        (initial ++
          renderSquaredSuccessorFactors
            (before ++
              retainFirstBlockOrFinalFactors
                (successorFactorMarkers before) factors))
  | [], before => by
      simpa [retainFirstBlockOrFinalFactors] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (initial ++ renderSquaredSuccessorFactors before))
  | [factor], before => by
      simpa [retainFirstBlockOrFinalFactors] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (initial ++
            renderSquaredSuccessorFactors (before ++ [factor])))
  | (marker, block) :: next :: rest, before => by
      by_cases drop :
          block = [] ∧ marker ∈ successorFactorMarkers before
      · rcases drop with ⟨blockEmpty, represented⟩
        subst block
        have first :=
          (listDerivesDropSeenMarkerOnlyNonfinalFactor
            before (next :: rest) marker represented (by simp)).context
              initial []
        have firstStep :
            ListDerives
              (initial ++
                renderSquaredSuccessorFactors
                  (before ++ (marker, []) :: next :: rest))
              (initial ++
                renderSquaredSuccessorFactors
                  (before ++ next :: rest)) := by
          simpa [List.append_assoc] using first
        have tail :=
          listDerivesRetainFirstBlockOrFinalFactorsAux
            initial (next :: rest) before
        simpa [retainFirstBlockOrFinalFactors,
          represented, List.append_assoc] using firstStep.trans tail
      · have tail :=
          listDerivesRetainFirstBlockOrFinalFactorsAux
            initial (next :: rest)
            (before ++ [(marker, block)])
        rw [retainFirstBlockOrFinalFactors, if_neg drop]
        simpa [successorFactorMarkers,
          List.append_assoc] using tail

/-- Collapse adjacent retained factors when the first contributes no simple
letters and both factors carry the same globally multiple marker. -/
def collapseAdjacentEmptySameFactors :
    List SuccessorFactor → List SuccessorFactor
  | [] => []
  | (marker, block) :: rest =>
      match collapseAdjacentEmptySameFactors rest with
      | [] => [(marker, block)]
      | (nextMarker, nextBlock) :: tail =>
          if block = [] ∧ marker = nextMarker then
            (nextMarker, nextBlock) :: tail
          else
            (marker, block) :: (nextMarker, nextBlock) :: tail

/-- Every adjacent equal-marker collapse is a genuine four-to-two contraction
in the frozen presentation; no semantic cancellation is assumed. -/
theorem listDerivesCollapseAdjacentEmptySameFactors :
    ∀ factors : List SuccessorFactor,
      ListDerives
        (renderSquaredSuccessorFactors factors)
        (renderSquaredSuccessorFactors
          (collapseAdjacentEmptySameFactors factors))
  | [] => by
      simpa [renderSquaredSuccessorFactors,
        collapseAdjacentEmptySameFactors] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis) [])
  | (marker, block) :: rest => by
      have tailStep :=
        (listDerivesCollapseAdjacentEmptySameFactors rest).context
          ([marker, marker] ++ block) []
      have normalizedTail :
          ListDerives
            (renderSquaredSuccessorFactors ((marker, block) :: rest))
            ([marker, marker] ++ block ++
              renderSquaredSuccessorFactors
                (collapseAdjacentEmptySameFactors rest)) := by
        simpa [renderSquaredSuccessorFactors,
          List.append_assoc] using tailStep
      cases normalized : collapseAdjacentEmptySameFactors rest with
      | nil =>
          simpa [collapseAdjacentEmptySameFactors, normalized,
            renderSquaredSuccessorFactors, List.append_assoc] using
              normalizedTail
      | cons next tail =>
          rcases next with ⟨nextMarker, nextBlock⟩
          by_cases collapsible : block = [] ∧ marker = nextMarker
          · rcases collapsible with ⟨emptyBlock, sameMarker⟩
            subst block
            subst nextMarker
            have contracted :=
              (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
                derivesPowerFourToTwo (Word.singleton marker)).context
                  [] (nextBlock ++ renderSquaredSuccessorFactors tail)
            have contraction :
                ListDerives
                  ([marker, marker] ++
                    renderSquaredSuccessorFactors
                      ((marker, nextBlock) :: tail))
                  (renderSquaredSuccessorFactors
                    ((marker, nextBlock) :: tail)) := by
              simpa [Word.singleton, Word.append,
                renderSquaredSuccessorFactors,
                List.append_assoc] using contracted
            have normalizedCollapsed :
                ListDerives
                  (renderSquaredSuccessorFactors
                    ((marker, []) :: rest))
                  ([marker, marker] ++
                    renderSquaredSuccessorFactors
                      ((marker, nextBlock) :: tail)) := by
              simpa [normalized] using normalizedTail
            simpa [collapseAdjacentEmptySameFactors, normalized,
              renderSquaredSuccessorFactors, List.append_assoc] using
                normalizedCollapsed.trans contraction
          · simpa [collapseAdjacentEmptySameFactors, normalized,
              collapsible, renderSquaredSuccessorFactors,
              List.append_assoc] using normalizedTail

/-- Exact proposed opposite-oriented stable first-order normal form. -/
def firstOrderPredecessorCanonicalList (letters : List Nat) : List Nat :=
  initialSimpleBlock letters ++
    renderSquaredSuccessorFactors
      (collapseAdjacentEmptySameFactors
        (retainFirstBlockOrFinalFactors [] (successorFactors letters)))

/-- Every word genuinely reaches its stable, first-order-preserving,
final-preserving successor-factor form in the ACTUAL four-law presentation. -/
theorem listDerivesFirstOrderPredecessorCanonical
    (letters : List Nat) :
    ListDerives letters (firstOrderPredecessorCanonicalList letters) := by
  have squared := listDerivesSquareAllSuccessorMarkers letters
  have retained :=
    listDerivesRetainFirstBlockOrFinalFactorsAux
      (initialSimpleBlock letters) (successorFactors letters) []
  have collapsed :=
    (listDerivesCollapseAdjacentEmptySameFactors
      (retainFirstBlockOrFinalFactors [] (successorFactors letters))).context
        (initialSimpleBlock letters) []
  have retainedStep :
      ListDerives
        (initialSimpleBlock letters ++
          renderSquaredSuccessorFactors (successorFactors letters))
        (initialSimpleBlock letters ++
          renderSquaredSuccessorFactors
            (retainFirstBlockOrFinalFactors []
              (successorFactors letters))) := by
    simpa [successorFactorMarkers] using retained
  have collapsedStep :
      ListDerives
        (initialSimpleBlock letters ++
          renderSquaredSuccessorFactors
            (retainFirstBlockOrFinalFactors []
              (successorFactors letters)))
        (firstOrderPredecessorCanonicalList letters) := by
    simpa [firstOrderPredecessorCanonicalList] using collapsed
  exact squared.trans (retainedStep.trans collapsedStep)

/-! ## Independent exact signature renderer and honest owner boundary -/

/-- Select a simple letter's genuine predecessor by using the complete direct
successor selector on its literally reversed source word. -/
def signaturePredecessor?
    (word : Word Nat) (support : List Nat) (letter : Nat) : Option Nat :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.signatureSuccessor?
    word.reverse support letter

/-- The full reversed-factor signature determines the predecessor selector
for any fixed, shared support ordering. -/
theorem signaturePredecessor?_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse)
    (support : List Nat) (letter : Nat) :
    signaturePredecessor? left support letter =
      signaturePredecessor? right support letter := by
  exact
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.signatureSuccessor?_eq_of_sameSignature
      same support letter

/-- Reversal preserves the precise globally-simple count coordinate. -/
theorem simple_iff_of_reversedSuccessor
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse)
    (letter : Nat) :
    left.toList.count letter = 1 ↔ right.toList.count letter = 1 := by
  simpa [SemigroupBasis.CoRoots.S5_402.GloballySimple,
    SemigroupBasis.CoRoots.S5_107.SimpleIn,
    Word.toList_reverse, List.count_reverse] using
      same.globallySimple letter

/-- The head of each reversed word is the genuine original final letter. -/
theorem final_eq_of_reversedSuccessor
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse) :
    left.final = right.final := by
  simpa only
    [SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax.reverse_head_eq_final]
      using same.head

/-- Emit a repeated predecessor only when it is not already the most recent
symbol in the already-rendered first-order prefix. -/
def signaturePredecessorDecoration
    (word : Word Nat) (support : List Nat)
    (last : Option Nat) (letter : Nat) : List Nat :=
  match signaturePredecessor? word support letter with
  | none => []
  | some marker =>
      if word.toList.count marker = 1 then
        []
      else if last = some marker then
        []
      else
        [marker, marker]

/-- Both predecessor choice and its multiplicity test are determined by the
complete, independently kernel-green opposite-factor signature. -/
theorem signaturePredecessorDecoration_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse)
    (support : List Nat) (last : Option Nat) (letter : Nat) :
    signaturePredecessorDecoration left support last letter =
      signaturePredecessorDecoration right support last letter := by
  unfold signaturePredecessorDecoration
  rw [signaturePredecessor?_eq_of_sameSignature same support letter]
  cases selected : signaturePredecessor? right support letter with
  | none => rfl
  | some marker =>
      have simple := simple_iff_of_reversedSuccessor same marker
      by_cases leftSimple : left.toList.count marker = 1
      · have rightSimple : right.toList.count marker = 1 :=
          simple.mp leftSimple
        simp [leftSimple, rightSimple]
      · have rightNotSimple : ¬ right.toList.count marker = 1 :=
          fun impossible => leftSimple (simple.mpr impossible)
        simp [leftSimple, rightNotSimple]

/-- Preserve the independently required actual final repeated letter. -/
def signatureFinalDecoration
    (word : Word Nat) (last : Option Nat) : List Nat :=
  if word.toList.count word.final = 1 then
    []
  else if last = some word.final then
    []
  else
    [word.final, word.final]

/-- Final decoration is also a function solely of the reversed signature. -/
theorem signatureFinalDecoration_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse)
    (last : Option Nat) :
    signatureFinalDecoration left last =
      signatureFinalDecoration right last := by
  have finals := final_eq_of_reversedSuccessor same
  have simple := simple_iff_of_reversedSuccessor same left.final
  unfold signatureFinalDecoration
  rw [← finals]
  by_cases leftSimple : left.toList.count left.final = 1
  · simp [leftSimple, simple.mp leftSimple]
  · have rightNotSimple : ¬ right.toList.count left.final = 1 :=
      fun impossible => leftSimple (simple.mpr impossible)
    simp [leftSimple, rightNotSimple]

/-- The fully signature-native renderer emits first occurrences in their
exact original order, the certified simple predecessors, and the final guard. -/
def renderFirstOrderPredecessorSignature
    (word : Word Nat) (support : List Nat) (last : Option Nat) :
    List Nat → List Nat
  | [] => signatureFinalDecoration word last
  | letter :: rest =>
      if word.toList.count letter = 1 then
        signaturePredecessorDecoration word support last letter ++
          [letter] ++
            renderFirstOrderPredecessorSignature
              word support (some letter) rest
      else
        [letter, letter] ++
          renderFirstOrderPredecessorSignature
            word support (some letter) rest

/-- Fixing support and order makes the independent renderer provably equal
under the complete unrestricted opposite-factor signature. -/
theorem renderFirstOrderPredecessorSignature_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      left.reverse right.reverse)
    (support : List Nat) :
    ∀ (order : List Nat) (last : Option Nat),
      renderFirstOrderPredecessorSignature left support last order =
        renderFirstOrderPredecessorSignature right support last order
  | [], last =>
      signatureFinalDecoration_eq_of_sameSignature same last
  | letter :: rest, last => by
      have simple := simple_iff_of_reversedSuccessor same letter
      by_cases leftSimple : left.toList.count letter = 1
      · have rightSimple : right.toList.count letter = 1 :=
          simple.mp leftSimple
        simp only [renderFirstOrderPredecessorSignature,
          leftSimple, rightSimple, ↓reduceIte]
        rw [signaturePredecessorDecoration_eq_of_sameSignature
          same support last letter]
        exact congrArg
          (fun tail =>
            signaturePredecessorDecoration right support last letter ++
              [letter] ++ tail)
          (renderFirstOrderPredecessorSignature_eq_of_sameSignature
            same support rest (some letter))
      · have rightNotSimple : ¬ right.toList.count letter = 1 :=
          fun impossible => leftSimple (simple.mpr impossible)
        simp only [renderFirstOrderPredecessorSignature,
          leftSimple, rightNotSimple, ↓reduceIte]
        exact congrArg (fun tail => [letter, letter] ++ tail)
          (renderFirstOrderPredecessorSignature_eq_of_sameSignature
            same support rest (some letter))

/-- This target depends only on exact first order, global simplicity,
simple predecessors and the genuine final letter. -/
def exactFirstOrderPredecessorSignatureCanonicalList
    (word : Word Nat) : List Nat :=
  let order := firstOccurrenceSequence word.toList
  renderFirstOrderPredecessorSignature word order none order

/-- The signature-only target is already unconditionally invariant for every
alphabet and every word length. -/
theorem exactPredecessorCanonicalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameFirstOrderSimplePredecessorSignature left right) :
    exactFirstOrderPredecessorSignatureCanonicalList left =
      exactFirstOrderPredecessorSignatureCanonicalList right := by
  unfold exactFirstOrderPredecessorSignatureCanonicalList
  rw [← same.firstOrder]
  exact renderFirstOrderPredecessorSignature_eq_of_sameSignature
    same.reversedSuccessor (firstOccurrenceSequence left.toList)
    (firstOccurrenceSequence left.toList) none

/-- A globally simple source's literal immediately preceding source letter
is exactly the reversed-signature-selected predecessor. -/
theorem signaturePredecessor?_eq_actual
    (word : Word Nat) (before after : List Nat)
    (marker letter : Nat)
    (split : word.toList = before ++ marker :: letter :: after)
    (simple : word.toList.count letter = 1) :
    signaturePredecessor? word
      (firstOccurrenceSequence word.toList) letter = some marker := by
  have different : letter ≠ marker := by
    intro same
    subst marker
    rw [split, List.count_append,
      List.count_cons_self, List.count_cons_self] at simple
    omega
  have simpleReverse : word.reverse.toList.count letter = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using simple
  have originalEdge : (marker, letter) ∈ word.adjacentPairs :=
    (SemigroupBasis.CoRoots.S5_107.mem_adjacentPairs_iff_exists_split
      marker letter word).mpr ⟨before, after, split⟩
  have reversedEdge : (letter, marker) ∈ word.reverse.adjacentPairs :=
    (SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax.adjacentPairs_reverse_iff
      word letter marker).mpr originalEdge
  have supported : marker ∈ firstOccurrenceSequence word.toList := by
    apply
      (SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.mem_firstOccurrenceSequence_iff
        marker word.toList).mpr
    rw [split]
    simp
  unfold signaturePredecessor?
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.signatureSuccessor?
  apply
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.find?_eq_some_of_unique
      (fun candidate =>
        decide
          (letter ≠ candidate ∧
            word.reverse.toList.count letter = 1 ∧
            (letter, candidate) ∈ word.reverse.adjacentPairs)) marker
  · simp [different, simple, reversedEdge]
  · intro candidate candidatePasses
    have selected :
        letter ≠ candidate ∧
          word.reverse.toList.count letter = 1 ∧
            (letter, candidate) ∈ word.reverse.adjacentPairs := by
      simpa only [decide_eq_true_eq] using candidatePasses
    apply
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.adjacent_target_unique_of_count_one
        letter word.reverse.toList candidate marker simpleReverse
    · rw [SemigroupBasis.CoRoots.S5_107.listAdjacentPairs_toList]
      exact selected.2.2
    · rw [SemigroupBasis.CoRoots.S5_107.listAdjacentPairs_toList]
      exact reversedEdge
  · exact supported

/-- A globally simple initial source letter has no genuine predecessor. -/
theorem signaturePredecessor?_eq_none_at_head
    (word : Word Nat) (after : List Nat) (letter : Nat)
    (split : word.toList = letter :: after)
    (simple : word.toList.count letter = 1) :
    signaturePredecessor? word
      (firstOccurrenceSequence word.toList) letter = none := by
  have initial : word.head = letter := by
    cases word with
    | mk actualHead actualTail =>
        have heads := congrArg List.head? split
        simpa [Word.toList] using heads
  have finalReverse : word.reverse.final = letter := by
    simpa only
      [SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax.reverse_final_eq_head]
        using initial
  have simpleReverse : word.reverse.toList.count letter = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using simple
  have simpleFinal :
      SemigroupBasis.CoRoots.S5_107.SimpleFinal word.reverse letter :=
    ⟨simpleReverse, finalReverse⟩
  have noSuccessor :=
    (SemigroupBasis.CoRoots.S5_402.simpleFinal_iff_noImmediateSuccessor
      word.reverse letter).mp simpleFinal
  unfold signaturePredecessor?
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge.signatureSuccessor?
  apply
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.find?_eq_none_of_no_matches
  intro candidate passes
  have selected :
      letter ≠ candidate ∧
        word.reverse.toList.count letter = 1 ∧
          (letter, candidate) ∈ word.reverse.adjacentPairs := by
    simpa only [decide_eq_true_eq] using passes
  exact noSuccessor.2 candidate selected

/-- Streaming decoration computed from the literal already-scanned prefix. -/
def prefixPredecessorDecoration
    (word : Word Nat) (before : List Nat) (last : Option Nat) : List Nat :=
  match before.reverse with
  | [] => []
  | marker :: _ =>
      if word.toList.count marker = 1 then
        []
      else if last = some marker then
        []
      else
        [marker, marker]

/-- For a genuinely globally simple next letter, the raw streaming decoration
is exactly the already proved signature-native predecessor decoration. -/
theorem prefixPredecessorDecoration_eq_signature
    (word : Word Nat) (before after : List Nat)
    (last : Option Nat) (letter : Nat)
    (split : word.toList = before ++ letter :: after)
    (simple : word.toList.count letter = 1) :
    prefixPredecessorDecoration word before last =
      signaturePredecessorDecoration word
        (firstOccurrenceSequence word.toList) last letter := by
  cases reversed : before.reverse with
  | nil =>
      have beforeEmpty : before = [] := by
        have restored := congrArg List.reverse reversed
        simpa using restored
      subst before
      have none :=
        signaturePredecessor?_eq_none_at_head word after letter
          (by simpa using split) simple
      simp [prefixPredecessorDecoration,
        signaturePredecessorDecoration, none]
  | cons marker reversedFront =>
      have beforeShape : before = reversedFront.reverse ++ [marker] := by
        have restored := congrArg List.reverse reversed
        simpa [List.reverse_cons] using restored
      have actualSplit :
          word.toList = reversedFront.reverse ++ marker :: letter :: after := by
        rw [split, beforeShape]
        simp [List.append_assoc]
      have actual :=
        signaturePredecessor?_eq_actual word reversedFront.reverse after
          marker letter actualSplit simple
      simp [prefixPredecessorDecoration, reversed,
        signaturePredecessorDecoration, actual]

/-- Independent prefix-generalized streaming scanner. The prior emitted symbol
is preserved even when already-seen repeated source symbols are skipped. -/
def stablePredecessorStreamingFold
    (word : Word Nat) (before seen : List Nat) (last : Option Nat) :
    List Nat → List Nat
  | [] => signatureFinalDecoration word last
  | letter :: rest =>
      if word.toList.count letter = 1 then
        prefixPredecessorDecoration word before last ++ [letter] ++
          stablePredecessorStreamingFold
            word (before ++ [letter]) seen (some letter) rest
      else if letter ∈ seen then
        stablePredecessorStreamingFold
          word (before ++ [letter]) seen last rest
      else
        [letter, letter] ++
          stablePredecessorStreamingFold
            word (before ++ [letter]) (seen ++ [letter])
              (some letter) rest

/-- Exact unrestricted prefix-state theorem: scanner repeated support,
first-occurrence support, literal scanned prefix, and last emitted marker are
all synchronized without dropping the final guard. -/
theorem stablePredecessorStreamingFold_eq_signature_state
    (word : Word Nat) :
    ∀ (remaining before scannerSeen signatureSeen : List Nat)
      (last : Option Nat),
      word.toList = before ++ remaining →
      (∀ letter,
        letter ∈ scannerSeen ↔
          letter ∈ before ∧ word.toList.count letter ≠ 1) →
      (∀ letter, letter ∈ signatureSeen ↔ letter ∈ before) →
      stablePredecessorStreamingFold
        word before scannerSeen last remaining =
        renderFirstOrderPredecessorSignature word
          (firstOccurrenceSequence word.toList) last
          (SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix
            signatureSeen remaining) := by
  intro remaining
  induction remaining with
  | nil =>
      intro before scannerSeen signatureSeen last _ _ _
      simp [stablePredecessorStreamingFold,
        SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix,
        renderFirstOrderPredecessorSignature]
  | cons letter rest inductionHypothesis =>
      intro before scannerSeen signatureSeen last split
        scannerInvariant signatureInvariant
      have advanced :
          word.toList = (before ++ [letter]) ++ rest := by
        simpa [List.append_assoc] using split
      by_cases simple : word.toList.count letter = 1
      · have beforeAbsent : letter ∉ before := by
          intro present
          have positive : 0 < before.count letter :=
            List.count_pos_iff.mpr present
          rw [split, List.count_append,
            List.count_cons_self] at simple
          omega
        have signatureAbsent : letter ∉ signatureSeen := by
          intro present
          exact beforeAbsent ((signatureInvariant letter).mp present)
        have scannerNext :
            ∀ candidate,
              candidate ∈ scannerSeen ↔
                candidate ∈ before ++ [letter] ∧
                  word.toList.count candidate ≠ 1 := by
          intro candidate
          rw [scannerInvariant candidate]
          by_cases same : candidate = letter
          · subst candidate
            simp [simple]
          · simp [same]
        have signatureNext :
            ∀ candidate,
              candidate ∈ letter :: signatureSeen ↔
                candidate ∈ before ++ [letter] := by
          intro candidate
          simp [signatureInvariant candidate, or_comm]
        have tail :=
          inductionHypothesis (before ++ [letter]) scannerSeen
            (letter :: signatureSeen) (some letter) advanced
            scannerNext signatureNext
        have decoration :=
          prefixPredecessorDecoration_eq_signature word before rest
            last letter split simple
        simp only [stablePredecessorStreamingFold, simple, ↓reduceIte,
          SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix,
          signatureAbsent, renderFirstOrderPredecessorSignature]
        rw [decoration]
        exact congrArg
          (fun output =>
            signaturePredecessorDecoration word
              (firstOccurrenceSequence word.toList) last letter ++
                [letter] ++ output) tail
      · have knownEquivalent :
            letter ∈ scannerSeen ↔ letter ∈ signatureSeen := by
          rw [scannerInvariant letter, signatureInvariant letter]
          simp [simple]
        have scannerAppended :
            ∀ candidate,
              candidate ∈ scannerSeen ++ [letter] ↔
                candidate ∈ before ++ [letter] ∧
                  word.toList.count candidate ≠ 1 := by
          intro candidate
          simp only [List.mem_append, List.mem_singleton]
          rw [scannerInvariant candidate]
          by_cases same : candidate = letter
          · subst candidate
            simp [simple]
          · simp [same]
        by_cases signatureKnown : letter ∈ signatureSeen
        · have scannerKnown : letter ∈ scannerSeen :=
            knownEquivalent.mpr signatureKnown
          have beforeKnown : letter ∈ before :=
            (signatureInvariant letter).mp signatureKnown
          have scannerUnchanged :
              ∀ candidate,
                candidate ∈ scannerSeen ↔
                  candidate ∈ before ++ [letter] ∧
                    word.toList.count candidate ≠ 1 := by
            intro candidate
            rw [scannerInvariant candidate]
            by_cases same : candidate = letter
            · subst candidate
              simp [beforeKnown, simple]
            · simp [same]
          have signatureUnchanged :
              ∀ candidate,
                candidate ∈ signatureSeen ↔
                  candidate ∈ before ++ [letter] := by
            intro candidate
            rw [signatureInvariant candidate]
            by_cases same : candidate = letter
            · subst candidate
              simp [beforeKnown]
            · simp [same]
          have tail :=
            inductionHypothesis (before ++ [letter]) scannerSeen
              signatureSeen last advanced
              scannerUnchanged signatureUnchanged
          simpa [stablePredecessorStreamingFold, simple, scannerKnown,
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix,
            signatureKnown] using tail
        · have scannerAbsent : letter ∉ scannerSeen := by
            intro present
            exact signatureKnown (knownEquivalent.mp present)
          have signatureNext :
              ∀ candidate,
                candidate ∈ letter :: signatureSeen ↔
                  candidate ∈ before ++ [letter] := by
            intro candidate
            simp [signatureInvariant candidate, or_comm]
          have tail :=
            inductionHypothesis (before ++ [letter])
              (scannerSeen ++ [letter]) (letter :: signatureSeen)
              (some letter) advanced scannerAppended signatureNext
          have appended :=
            congrArg (fun output : List Nat => [letter, letter] ++ output)
              tail
          simpa [stablePredecessorStreamingFold, simple, scannerAbsent,
            SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix,
            signatureKnown, renderFirstOrderPredecessorSignature] using
              appended

/-- Starting from genuinely empty scanned/emitted state, the independent
streaming scanner is exactly the complete signature-native renderer. -/
theorem stablePredecessorStreamingFold_eq_exactSignature
    (word : Word Nat) :
    stablePredecessorStreamingFold word [] [] none word.toList =
      exactFirstOrderPredecessorSignatureCanonicalList word := by
  have state :=
    stablePredecessorStreamingFold_eq_signature_state
      word word.toList [] [] [] none
      (by simp)
      (by intro letter; simp)
      (by intro letter; simp)
  rw [SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed.firstOccurrenceAfterPrefix_nil]
    at state
  simpa [exactFirstOrderPredecessorSignatureCanonicalList] using state

/-- One precisely exposed combinatorial scanner agreement is sufficient; it
is not postulated, stamped, or silently used as an unconditional proof. -/
def StablePredecessorScannerSignatureAgreement : Prop :=
  ∀ word : Word Nat,
    firstOrderPredecessorCanonicalList word.toList =
      exactFirstOrderPredecessorSignatureCanonicalList word

/-- Sharper owner cut: identify the already-reachable, adjacent-collapsed
historical successor scan with the already-proved prefix streaming scanner. -/
def CorrectedSuccessorFactorStreamingAgreement : Prop :=
  ∀ word : Word Nat,
    firstOrderPredecessorCanonicalList word.toList =
      stablePredecessorStreamingFold word [] [] none word.toList

/-- The factor/streaming identification and the signature agreement are
literally equivalent because the complete streaming/signature state theorem
has already been proved without additional assumptions. -/
theorem correctedFactorStreamingAgreement_iff_scannerSignatureAgreement :
    CorrectedSuccessorFactorStreamingAgreement ↔
      StablePredecessorScannerSignatureAgreement := by
  constructor
  · intro agreement word
    exact (agreement word).trans
      (stablePredecessorStreamingFold_eq_exactSignature word)
  · intro agreement word
    exact (agreement word).trans
      (stablePredecessorStreamingFold_eq_exactSignature word).symm

/-- Genuine frozen-law reachability and independent signature invariance turn
the single explicit scanner agreement into unrestricted derivability. -/
theorem derives_of_stablePredecessorScannerAgreement
    (agreement : StablePredecessorScannerSignatureAgreement)
    (left right : Word Nat)
    (same : SameFirstOrderSimplePredecessorSignature left right) :
    Derives basis left right := by
  have leftDerivation :=
    listDerivesFirstOrderPredecessorCanonical left.toList
  have rightDerivation :=
    listDerivesFirstOrderPredecessorCanonical right.toList
  have canonicalEqual :
      firstOrderPredecessorCanonicalList left.toList =
        firstOrderPredecessorCanonicalList right.toList :=
    (agreement left).trans <|
      (exactPredecessorCanonicalList_eq_of_sameSignature same).trans
        (agreement right).symm
  have joined : ListDerives left.toList right.toList := by
    exact leftDerivation.trans <| by
      rw [canonicalEqual]
      exact rightDerivation.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord joined

/-- The exact absent owner premise lifts independently complete `S5_402`
derivations of reversed words while preserving full original first order. -/
def FirstOccurrencePreservingSimplePredecessorLift : Prop :=
  ∀ identity : Identity Nat,
    firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList →
      Derives SemigroupBasis.CoRoots.S5_402.basis
        identity.lhs.reverse identity.rhs.reverse →
        Derives basis identity.lhs identity.rhs

/-- The explicitly isolated scanner agreement suffices for the exact owner
lift; no converse is assumed. -/
theorem stablePredecessorScannerAgreement_implies_ownerLift
    (agreement : StablePredecessorScannerSignatureAgreement) :
    FirstOccurrencePreservingSimplePredecessorLift := by
  intro identity order lower
  exact derives_of_stablePredecessorScannerAgreement agreement
    identity.lhs identity.rhs
    ⟨order, SemigroupBasis.CoRoots.S5_402.derives_sameSignature lower⟩

/-- A separately supplied exact owner lift proves the actual intersection. -/
def intersectionBasis_of_simplePredecessorLift
    (lift : FirstOccurrencePreservingSimplePredecessorLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact lift identity
      (firstOccurrences_of_leftValid identity leftValid)
      (SemigroupBasis.CoRoots.S5_402.derivesOfSameSimpleSuccessorSignature
        (reversedSuccessor_of_rightValid identity rightValid))

/-- Every genuine intersection conversely supplies the exact missing lift. -/
theorem simplePredecessorLift_of_intersectionBasis
    (intersection :
      IntersectionBasis leftTable.semigroup rightTable.semigroup basis) :
    FirstOccurrencePreservingSimplePredecessorLift := by
  intro identity same lowerDerivation
  exact intersection.complete identity
    (leftValid_of_firstOccurrences identity same)
    (rightValid_of_reversedSuccessor identity
      (SemigroupBasis.CoRoots.S5_402.derives_sameSignature lowerDerivation))

/-- Sharp owner boundary: an intersection exists if and only if its exact
unrestricted first-order-preserving predecessor lift is independently proved. -/
theorem intersection_exists_iff_simplePredecessorLift :
    Nonempty
      (IntersectionBasis leftTable.semigroup rightTable.semigroup basis) ↔
      FirstOccurrencePreservingSimplePredecessorLift := by
  constructor
  · rintro ⟨intersection⟩
    exact simplePredecessorLift_of_intersectionBasis intersection
  · intro lift
    exact ⟨intersectionBasis_of_simplePredecessorLift lift⟩

/-- The one staged class and both orientations remain rigorously conditional
until the exact owner lift is supplied. -/
theorem both_orientations_of_simplePredecessorLift
    (lift : FirstOccurrencePreservingSimplePredecessorLift) :
    BasisFor S6_8453.table.semigroup basis ∧
      BasisFor S6_8453.table.semigroup.opposite (reversedBasis basis) := by
  let owner := intersectionBasis_of_simplePredecessorLift lift
  let normalizer :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      owner
  exact
    ⟨S6_8453.representative_basis_of_normalizer normalizer,
      S6_8453.opposite_basis_of_normalizer normalizer⟩

/-- The pure predecessor scanner lemma would close both exact endpoints. -/
theorem both_orientations_of_stablePredecessorScannerAgreement
    (agreement : StablePredecessorScannerSignatureAgreement) :
    BasisFor S6_8453.table.semigroup basis ∧
      BasisFor S6_8453.table.semigroup.opposite (reversedBasis basis) :=
  both_orientations_of_simplePredecessorLift
    (stablePredecessorScannerAgreement_implies_ownerLift agreement)

/-! ## Formal refutations of genuinely distinct normalization shortcuts -/

private def shortcutWitnessToFin : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The first-order-changing lower shortcut is genuinely valid on the actual
opposite right factor, not merely a bounded rewrite-search suggestion. -/
theorem lowerOppositeFirstOrderReordering_rightValid :
    (⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩ : Identity Nat).SatisfiedBy
      rightTable.semigroup := by
  let identity : Identity Nat :=
    ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩
  have roundTrip :
      (identity.map shortcutWitnessToFin).map Fin.val = identity := by
    decide
  have finiteValid :
      (identity.map shortcutWitnessToFin).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (identity.map shortcutWitnessToFin) (by decide)
  have lifted :=
    (identity.map shortcutWitnessToFin).satisfiedBy_map
      Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

/-- The complete lower opposite-factor theory alone allows reorderings that
destroy the true `S3_16` first-occurrence coordinate. -/
theorem lowerOppositeFirstOrderReordering_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1, 1])
      (Word.mk 1 [0, 0, 1]) := by
  intro derivation
  have order :=
    firstOccurrences_of_leftValid
      ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩
      (derivation.sound leftModels)
  change [0, 1] = [1, 0] at order
  exact (by decide : ([0, 1] : List Nat) ≠ [1, 0]) order

/-- Even the historical opposite-factor engine's genuine preserved-head
condition is too weak: it still permits a later first-order inversion. -/
theorem historicalHeadPreservingReordering_rightValid :
    (⟨Word.mk 0 [0, 2, 1, 1], Word.mk 0 [1, 0, 2, 1]⟩ : Identity Nat).SatisfiedBy
      rightTable.semigroup := by
  let identity : Identity Nat :=
    ⟨Word.mk 0 [0, 2, 1, 1], Word.mk 0 [1, 0, 2, 1]⟩
  have roundTrip :
      (identity.map shortcutWitnessToFin).map Fin.val = identity := by
    decide
  have finiteValid :
      (identity.map shortcutWitnessToFin).SatisfiedBy rightTable.semigroup :=
    rightTable.checkIdentityFused_sound
      (identity.map shortcutWitnessToFin) (by decide)
  have lifted :=
    (identity.map shortcutWitnessToFin).satisfiedBy_map
      Fin.val rightTable.semigroup finiteValid
  rw [roundTrip] at lifted
  exact lifted

/-- This second shortcut satisfies the complete historical head-plus-opposite
signature even though it violates the new full first-occurrence coordinate. -/
theorem historicalHeadPreservingReordering_has_historicalSignature :
    SemigroupBasis.CoRoots.Order6LeeZhang23_9Syntax.SameLeeZhang23_9Signature
      (Word.mk 0 [0, 2, 1, 1])
      (Word.mk 0 [1, 0, 2, 1]) :=
  ⟨rfl,
    reversedSuccessor_of_rightValid
      ⟨Word.mk 0 [0, 2, 1, 1], Word.mk 0 [1, 0, 2, 1]⟩
      historicalHeadPreservingReordering_rightValid⟩

theorem historicalHeadPreservingReordering_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 2, 1, 1])
      (Word.mk 0 [1, 0, 2, 1]) := by
  intro derivation
  have order :=
    firstOccurrences_of_leftValid
      ⟨Word.mk 0 [0, 2, 1, 1], Word.mk 0 [1, 0, 2, 1]⟩
      (derivation.sound leftModels)
  change [0, 2, 1] = [0, 1, 2] at order
  exact
    (by decide : ([0, 2, 1] : List Nat) ≠ [0, 1, 2]) order

/-- The kernel-green rank-090 direct-factor crossing is unavailable after
oppositing: it changes the actual final letter. -/
theorem priorRank090SquareCrossing_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1, 1])
      (Word.mk 0 [1, 1, 0]) := by
  intro derivation
  have signature :=
    reversedSuccessor_of_rightValid
      ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩
      (derivation.sound rightModels)
  have finals := final_eq_of_reversedSuccessor signature
  change (1 : Nat) = 0 at finals
  exact (by decide : (1 : Nat) ≠ 0) finals

/-- Preserving the final successor factor without collapsing newly adjacent
equal markers is not signature-invariant even on frozen displayed law 03. -/
theorem uncollapsedRetainedScanner_not_lawInvariant :
    (initialSimpleBlock [0, 1, 0, 2, 2] ++
      renderSquaredSuccessorFactors
        (retainFirstBlockOrFinalFactors []
          (successorFactors [0, 1, 0, 2, 2]))) ≠
      (initialSimpleBlock [0, 0, 1, 2, 2] ++
        renderSquaredSuccessorFactors
          (retainFirstBlockOrFinalFactors []
            (successorFactors [0, 0, 1, 2, 2]))) := by
  decide

/-- The mathematically necessary equal-marker collapse repairs that exact
displayed-law counterexample using only the proved power contraction. -/
theorem collapsedRetainedScanner_preserves_displayedLaw03 :
    firstOrderPredecessorCanonicalList [0, 1, 0, 2, 2] =
      firstOrderPredecessorCanonicalList [0, 0, 1, 2, 2] := by
  decide

/-- A genuinely repeated final letter remains explicit in both independent
renderers; the final guard cannot be cancelled globally. -/
theorem finalRepeatedMarker_preserved_by_both_renderers :
    firstOrderPredecessorCanonicalList [0, 1, 0, 2, 0] =
      [0, 0, 1, 0, 0, 2, 0, 0] ∧
      exactFirstOrderPredecessorSignatureCanonicalList
        (Word.mk 0 [1, 0, 2, 0]) =
        [0, 0, 1, 0, 0, 2, 0, 0] := by
  decide

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank091.FirstOrderPredecessorBridge
