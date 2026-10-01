import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_240
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_402SignatureBridge

/-!
# Exact rank-090 first-occurrence / simple-successor owner boundary

The immutable five-law `S3_16 × S5_402` presentation has an exact
unrestricted semantic descriptor: the entire first-occurrence sequence and
the independently complete `S5_402` capped-multiplicity / globally-simple
immediate-successor signature.

The complete thirteen-law lower-factor calculus cannot be replayed wholesale:
its factor swaps genuinely change first-occurrence order. Conversely, the
complete left-regular-band calculus cannot be replayed wholesale because its
primitive laws genuinely change the right-factor capped multiplicities.

This bridge proves the exact semantic equivalence, seven genuinely safe
lower-factor axioms, whole-word factor-middle derivations, an order-preserving
candidate renderer, and the precise unrestricted owner obligation. It never
asserts that the remaining renderer uniqueness obligation has been discharged.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge

open SemigroupBasis
open SemigroupBasis.Examples

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The actual frozen left table is exactly the complete three-state LRB. -/
def actualLeftIntoCanonical :
    Embedding leftTable.semigroup leftRegularBandThree.semigroup where
  toFun := fun value => value
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equal
    exact equal

/-- The kernel-green rank-018 detector fixes the COMPLETE first order. -/
theorem firstOccurrences_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
    identity valid

/-- Complete LRB normalization makes the exact first-order test sufficient. -/
theorem leftValid_of_firstOccurrences
    (identity : Identity Nat)
    (same : firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList) :
    identity.SatisfiedBy leftTable.semigroup :=
  actualLeftIntoCanonical.pullback_identity identity
    ((SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbDerives_of_sameFirstOccurrences
      identity.lhs identity.rhs same).sound leftRegularBandThreeBasis_models)

/-- Independent direct `S5_402` semantics recover its exact owner signature. -/
theorem simpleSuccessor_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs identity.rhs := by
  apply SemigroupBasis.CoRoots.S5_402.sameSignature_of_valid identity
  exact valid

/-- The independent thirteen-law owner closes signature sufficiency. -/
theorem rightValid_of_simpleSuccessor
    (identity : Identity Nat)
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature
      identity.lhs identity.rhs) :
    identity.SatisfiedBy rightTable.semigroup := by
  exact
    (SemigroupBasis.CoRoots.S5_402.derivesOfSameSimpleSuccessorSignature same).sound
      SemigroupBasis.CoRoots.S5_402.models

/-- The exact joint semantic descriptor; the initials are never truncated. -/
structure SameFirstOrderSimpleSuccessorSignature
    (left right : Word Nat) : Prop where
  firstOrder :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  simpleSuccessor :
    SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature left right

/-- Exact equivalence on every alphabet, not a bounded-model claim. -/
theorem sameSignature_iff_factorValidity
    (identity : Identity Nat) :
    SameFirstOrderSimpleSuccessorSignature identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧
        identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro same
    exact ⟨leftValid_of_firstOccurrences identity same.firstOrder,
      rightValid_of_simpleSuccessor identity same.simpleSuccessor⟩
  · rintro ⟨leftValid, rightValid⟩
    exact ⟨firstOccurrences_of_leftValid identity leftValid,
      simpleSuccessor_of_rightValid identity rightValid⟩

/-! ## Genuine unrestricted displayed-law derivations -/

/-- The immutable power law, oriented as the lower owner's expansion. -/
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

/-- Frozen law 01 duplicates the left occurrence of any repeated word. -/
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

/-- Frozen law 02 duplicates the right occurrence of any repeated word. -/
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

/-- Frozen law 03 crosses a repeated block without changing first order. -/
theorem derivesSquareCrossing (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ second)
      (((first ++ second) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    (Derives.fromBasis (e := law03) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 04 crosses a repeated final block through a genuine middle. -/
theorem derivesSquareTailMove
    (first middle final : Word Nat) :
    Derives basis
      ((((first ++ first) ++ middle) ++ final) ++ final)
      ((((first ++ middle) ++ final) ++ final) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2, 2])
        (Word.mk 0 [1, 2, 2, 0]) :=
    (Derives.fromBasis (e := law04) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The lower square alternation is a genuine three-step frozen derivation. -/
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
  have cross :
      Derives basis
        ((((first ++ first) ++ second) ++ second) ++ second)
        ((((first ++ second) ++ second) ++ first) ++ second) :=
    Derives.appendRight (derivesSquareCrossing first second) second
  have contract :
      Derives basis
        ((((first ++ second) ++ second) ++ first) ++ second)
        (((first ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first (derivesLeftDuplication second first).symm
  exact expand.trans (cross.trans contract)

/-- Whole-word substitutions expose the order-preserving left-middle move. -/
theorem derivesFactorMiddleLeft
    (first second third : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ third) ++ second)
      ((((first ++ second) ++ first) ++ third) ++ second) := by
  have expand :
      Derives basis
        ((((first ++ first) ++ second) ++ third) ++ second)
        (((((first ++ first) ++ second) ++ second) ++ third) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesLeftDuplication second third)
  have cross :
      Derives basis
        (((((first ++ first) ++ second) ++ second) ++ third) ++ second)
        (((((first ++ second) ++ second) ++ first) ++ third) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesSquareCrossing first second)
        (third ++ second)
  have contract :
      Derives basis
        (((((first ++ second) ++ second) ++ first) ++ third) ++ second)
        ((((first ++ second) ++ first) ++ third) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first
        (derivesLeftDuplication second (first ++ third)).symm
  exact expand.trans (cross.trans contract)

/-- Whole-word substitutions also expose the order-preserving right move. -/
theorem derivesFactorMiddleRight
    (first second third : Word Nat) :
    Derives basis
      ((((first ++ first) ++ second) ++ third) ++ second)
      ((((first ++ second) ++ third) ++ second) ++ first) := by
  have expand :
      Derives basis
        ((((first ++ first) ++ second) ++ third) ++ second)
        (((((first ++ first) ++ second) ++ third) ++ second) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesRightDuplication second third)
  have move :
      Derives basis
        (((((first ++ first) ++ second) ++ third) ++ second) ++ second)
        (((((first ++ second) ++ third) ++ second) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      derivesSquareTailMove first (second ++ third) second
  have contract :
      Derives basis
        (((((first ++ second) ++ third) ++ second) ++ second) ++ first)
        ((((first ++ second) ++ third) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend first
          (derivesRightDuplication second third).symm) first
  exact expand.trans (move.trans contract)

/-! ## Order-preserving, target-valid terminated-marker squaring -/

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- Duplicate the left occurrence of an arbitrary scattered repeated letter. -/
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

/-- Duplicate the right occurrence of an arbitrary scattered repeated letter. -/
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

/-- Every selected globally repeated position can be doubled in place. -/
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

/-- Square all frozen-owner factors without importing its invalid swaps. -/
theorem listDerivesSquareTerminatedMarkersAux
    (final : List Nat) :
    ∀ (factors : List (List Nat × Nat))
      (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤
          (before ++
            SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks factors ++
            final).count factor.2) →
      ListDerives
        (before ++
          SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks factors ++ final)
        (before ++
          SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks factors ++
          final)
  | [], before, _ => by
      simpa [SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks,
        SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis) (before ++ final))
  | (block, marker) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤
            ((before ++ block) ++ [marker] ++
              (SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++
                final)).count marker := by
        simpa [SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks,
          List.append_assoc] using
            multiples (block, marker) (by simp)
      have firstRaw :=
        listDerivesDuplicateSelectedOccurrence
          marker (before ++ block)
          (SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++ final)
          markerMultiple
      have firstStep :
          ListDerives
            (before ++
              SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks
                ((block, marker) :: rest) ++ final)
            ((before ++ block ++ [marker, marker]) ++
              SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++
              final) := by
        simpa [SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks,
          List.append_assoc] using firstRaw
      have restMultiples :
          ∀ factor ∈ rest,
            2 ≤
              ((before ++ block ++ [marker, marker]) ++
                SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++
                final).count factor.2 := by
        intro factor member
        have oldMultiple :
            2 ≤
              ((before ++ block) ++ [marker] ++
                (SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++
                  final)).count factor.2 := by
          simpa [SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks,
            List.append_assoc] using
              multiples factor (by simp [member])
        have monotone :=
          SemigroupBasis.CoRoots.S5_402.count_le_count_duplicateSelected
            factor.2 marker (before ++ block)
              (SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks rest ++
                final)
        have newMultiple := Nat.le_trans oldMultiple monotone
        simpa [List.append_assoc] using newMultiple
      have restStep :=
        listDerivesSquareTerminatedMarkersAux
          final rest (before ++ block ++ [marker, marker]) restMultiples
      have combined := firstStep.trans restStep
      simpa [SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks,
        List.append_assoc] using combined

/-- Every word reaches its scanner's squared factors in the ACTUAL basis. -/
theorem listDerivesSquareAllTerminatedMarkers
    (letters : List Nat) :
    ListDerives letters
      (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
          (SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters) ++
        SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock letters) := by
  have multiples :
      ∀ factor ∈ SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters,
        2 ≤
          (SemigroupBasis.CoRoots.S5_402.renderTerminatedBlocks
              (SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters) ++
            SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock letters).count
              factor.2 := by
    intro factor member
    rw [SemigroupBasis.CoRoots.S5_402.terminatedBlocks_render letters]
    exact SemigroupBasis.CoRoots.S5_402.terminatedBlocks_marker_multiple
      letters factor member
  have squared :=
    listDerivesSquareTerminatedMarkersAux
      (SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock letters)
      (SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters) [] <| by
        simpa using multiples
  simpa [SemigroupBasis.CoRoots.S5_402.terminatedBlocks_render letters] using
    squared

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

/-- Delete one already-seen marker beyond ANY intervening final square. -/
theorem listDerivesDropSeenMarkerAcrossFinalSquare
    (marker finalMarker : Nat) (middle : List Nat) :
    ListDerives
      ([marker, marker] ++ middle ++ [finalMarker, finalMarker, marker])
      ([marker, marker] ++ middle ++ [finalMarker, finalMarker]) := by
  let genuineMiddle := listWordOfCons marker middle
  have moved :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      (derivesSquareTailMove (Word.singleton marker)
        genuineMiddle (Word.singleton finalMarker)).symm
  have movedStep :
      ListDerives
        ([marker, marker] ++ middle ++ [finalMarker, finalMarker, marker])
        ([marker, marker, marker] ++ middle ++
          [finalMarker, finalMarker]) := by
    simpa [genuineMiddle, listWordOfCons, Word.singleton,
      Word.append, List.append_assoc] using moved
  have contracted :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      (derivesPowerExpansion (Word.singleton marker)).symm).context
        [] (middle ++ [finalMarker, finalMarker])
  have contractedStep :
      ListDerives
        ([marker, marker, marker] ++ middle ++
          [finalMarker, finalMarker])
        ([marker, marker] ++ middle ++ [finalMarker, finalMarker]) := by
    simpa [Word.singleton, Word.append, List.append_assoc] using
      contracted
  exact movedStep.trans contractedStep

/-- Delete an entire already-seen squared marker after an arbitrary square. -/
theorem listDerivesDropSeenMarkerSquareAcrossFinalSquare
    (marker finalMarker : Nat) (middle : List Nat) :
    ListDerives
      ([marker, marker] ++ middle ++
        [finalMarker, finalMarker, marker, marker])
      ([marker, marker] ++ middle ++ [finalMarker, finalMarker]) := by
  have first :=
    (listDerivesDropSeenMarkerAcrossFinalSquare marker finalMarker middle).append
      [marker]
  have firstStep :
      ListDerives
        ([marker, marker] ++ middle ++
          [finalMarker, finalMarker, marker, marker])
        ([marker, marker] ++ middle ++
          [finalMarker, finalMarker, marker]) := by
    simpa [List.append_assoc] using first
  exact firstStep.trans
    (listDerivesDropSeenMarkerAcrossFinalSquare marker finalMarker middle)

private theorem exists_append_singleton_of_ne_nil
    {α : Type} :
    ∀ (items : List α), items ≠ [] →
      ∃ front last, items = front ++ [last]
  | [], nonempty => False.elim (nonempty rfl)
  | item :: rest, _ => by
      cases rest with
      | nil =>
          exact ⟨[], item, by simp⟩
      | cons next tail =>
          obtain ⟨front, last, shape⟩ :=
            exists_append_singleton_of_ne_nil
              (next :: tail) (by simp)
          exact ⟨item :: front, last, by simp [shape]⟩

/-- Remove a redundant empty-block factor WITHOUT sorting any factors. -/
theorem listDerivesDropSeenMarkerOnlyFactor
    (before after : List (List Nat × Nat))
    (marker : Nat) (final : List Nat)
    (represented :
      marker ∈ SemigroupBasis.CoRoots.S5_402.terminatedFactorMarkers before) :
    ListDerives
      (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
        (before ++ [([], marker)] ++ after) ++ final)
      (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
        (before ++ after) ++ final) := by
  rcases List.mem_map.mp represented with
    ⟨factor, factorMember, factorMarker⟩
  rcases factor with ⟨block, witnessMarker⟩
  simp only at factorMarker
  subst witnessMarker
  obtain ⟨front, middle, split⟩ :=
    List.mem_iff_append.mp factorMember
  subst before
  by_cases middleEmpty : middle = []
  · subst middle
    have contraction :=
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
        derivesPowerFourToTwo (Word.singleton marker)).context
          (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks front ++
            block)
          (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks after ++
            final)
    simpa [SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks,
      Word.singleton, Word.append, List.append_assoc] using contraction
  · obtain ⟨middleFront, last, lastShape⟩ :=
      exists_append_singleton_of_ne_nil middle middleEmpty
    rcases last with ⟨lastBlock, lastMarker⟩
    rw [lastShape]
    have contraction :=
      (listDerivesDropSeenMarkerSquareAcrossFinalSquare
        marker lastMarker
        (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
          middleFront ++ lastBlock)).context
          (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks front ++
            block)
          (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks after ++
            final)
    simpa [SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks,
      List.append_assoc] using contraction

/-- Keep every simple-bearing factor and each marker's first factor, in place. -/
def retainFirstOrBlockFactors
    (seen : List Nat) :
    List (List Nat × Nat) → List (List Nat × Nat)
  | [] => []
  | (block, marker) :: rest =>
      if block = [] ∧ marker ∈ seen then
        retainFirstOrBlockFactors seen rest
      else
        (block, marker) ::
          retainFirstOrBlockFactors (seen ++ [marker]) rest

/-- Stably delete exactly the already-seen empty-block factors. -/
theorem listDerivesRetainFirstOrBlockFactorsAux
    (final : List Nat) :
    ∀ (factors before : List (List Nat × Nat)),
      ListDerives
        (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
          (before ++ factors) ++ final)
        (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
          (before ++
            retainFirstOrBlockFactors
              (SemigroupBasis.CoRoots.S5_402.terminatedFactorMarkers before)
              factors) ++ final)
  | [], before => by
      simpa [retainFirstOrBlockFactors] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
            before ++ final))
  | (block, marker) :: rest, before => by
      by_cases drop :
          block = [] ∧
            marker ∈
              SemigroupBasis.CoRoots.S5_402.terminatedFactorMarkers before
      · rcases drop with ⟨blockEmpty, represented⟩
        subst block
        have first :=
          listDerivesDropSeenMarkerOnlyFactor before rest marker final
            represented
        have restStep :=
          listDerivesRetainFirstOrBlockFactorsAux final rest before
        have combined := first.trans restStep
        simpa [retainFirstOrBlockFactors, represented,
          List.append_assoc] using combined
      · have next :=
          listDerivesRetainFirstOrBlockFactorsAux final rest
            (before ++ [(block, marker)])
        rw [retainFirstOrBlockFactors, if_neg drop]
        simpa [SemigroupBasis.CoRoots.S5_402.terminatedFactorMarkers,
          List.append_assoc] using next

/-- Proposed order-preserving normal form; equality is NOT assumed. -/
def firstOrderSuccessorCanonicalList (letters : List Nat) : List Nat :=
  SemigroupBasis.CoRoots.S5_402.renderSquaredTerminatedBlocks
      (retainFirstOrBlockFactors []
        (SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters)) ++
    SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock letters

/-- The ACTUAL frozen presentation reaches the stable first-order scanner. -/
theorem listDerivesFirstOrderSuccessorCanonical
    (letters : List Nat) :
    ListDerives letters (firstOrderSuccessorCanonicalList letters) := by
  have squared := listDerivesSquareAllTerminatedMarkers letters
  have retained :=
    listDerivesRetainFirstOrBlockFactorsAux
      (SemigroupBasis.CoRoots.S5_402.terminatedFinalBlock letters)
      (SemigroupBasis.CoRoots.S5_402.terminatedBlocks letters) []
  exact squared.trans <| by
    simpa [firstOrderSuccessorCanonicalList,
      SemigroupBasis.CoRoots.S5_402.terminatedFactorMarkers] using retained

/-- Select a simple letter's genuine immediate successor from known support. -/
def signatureSuccessor?
    (word : Word Nat) (support : List Nat) (source : Nat) : Option Nat :=
  support.find? fun target =>
    decide
      (source ≠ target ∧ word.toList.count source = 1 ∧
        (source, target) ∈ word.adjacentPairs)

/-- The complete lower signature determines every selected successor. -/
theorem signatureSuccessor?_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature left right)
    (support : List Nat) (source : Nat) :
    signatureSuccessor? left support source =
      signatureSuccessor? right support source := by
  apply congrArg (fun predicate : Nat → Bool => support.find? predicate)
  funext target
  have equivalent :
      (source ≠ target ∧ left.toList.count source = 1 ∧
        (source, target) ∈ left.adjacentPairs) ↔
      (source ≠ target ∧ right.toList.count source = 1 ∧
        (source, target) ∈ right.adjacentPairs) := by
    simpa [SemigroupBasis.CoRoots.S5_402.ImmediateSuccessor,
      SemigroupBasis.CoRoots.S5_107.SimpleIn] using
      same.successor source target
  simp [equivalent]

/-- Render first occurrences, injecting only already-seen simple successors. -/
def renderFirstOrderSignature
    (word : Word Nat) (support : List Nat) (seen : List Nat) :
    List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if word.toList.count letter = 1 then
        let required :=
          match signatureSuccessor? word support letter with
          | none => []
          | some marker =>
              if marker ∈ seen then [marker, marker] else []
        [letter] ++ required ++
          renderFirstOrderSignature word support (letter :: seen) rest
      else
        [letter, letter] ++
          renderFirstOrderSignature word support (letter :: seen) rest

/-- A fixed first order and exact lower signature make this renderer equal. -/
theorem renderFirstOrderSignature_eq_of_sameSignature
    {left right : Word Nat}
    (same : SemigroupBasis.CoRoots.S5_402.SameSimpleSuccessorSignature left right)
    (support : List Nat) :
    ∀ (order seen : List Nat),
      renderFirstOrderSignature left support seen order =
        renderFirstOrderSignature right support seen order
  | [], _ => rfl
  | letter :: rest, seen => by
      have simple := same.globallySimple letter
      have successors :=
        signatureSuccessor?_eq_of_sameSignature same support letter
      by_cases leftSimple : left.toList.count letter = 1
      · have rightSimple : right.toList.count letter = 1 :=
          simple.mp leftSimple
        simp only [renderFirstOrderSignature, leftSimple, rightSimple,
          ↓reduceIte]
        rw [successors]
        exact congrArg
          (fun tail =>
            [letter] ++
              (match signatureSuccessor? right support letter with
               | none => []
               | some marker =>
                   if marker ∈ seen then [marker, marker] else []) ++ tail)
          (renderFirstOrderSignature_eq_of_sameSignature
            same support rest (letter :: seen))
      · have rightNotSimple :
            ¬ right.toList.count letter = 1 :=
          fun present => leftSimple (simple.mpr present)
        simp only [renderFirstOrderSignature, leftSimple, rightNotSimple,
          ↓reduceIte]
        exact congrArg (fun tail => [letter, letter] ++ tail)
          (renderFirstOrderSignature_eq_of_sameSignature
            same support rest (letter :: seen))

/-- This second renderer depends only on the independently proved signature. -/
def exactFirstOrderSignatureCanonicalList (word : Word Nat) : List Nat :=
  let order := firstOccurrenceSequence word.toList
  renderFirstOrderSignature word order [] order

/-- Unrestricted equality of the deterministic signature-only renderer. -/
theorem exactCanonicalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameFirstOrderSimpleSuccessorSignature left right) :
    exactFirstOrderSignatureCanonicalList left =
      exactFirstOrderSignatureCanonicalList right := by
  unfold exactFirstOrderSignatureCanonicalList
  rw [← same.firstOrder]
  exact renderFirstOrderSignature_eq_of_sameSignature
    same.simpleSuccessor (firstOccurrenceSequence left.toList)
    (firstOccurrenceSequence left.toList) []

/-- The remaining issue is PURE scanner/signature agreement, not soundness. -/
def StableScannerSignatureAgreement : Prop :=
  ∀ word : Word Nat,
    firstOrderSuccessorCanonicalList word.toList =
      exactFirstOrderSignatureCanonicalList word

/-- Stable scanner agreement would close genuine unrestricted completeness. -/
theorem derives_of_stableScannerAgreement
    (agreement : StableScannerSignatureAgreement)
    (left right : Word Nat)
    (same : SameFirstOrderSimpleSuccessorSignature left right) :
    Derives basis left right := by
  have leftDerivation :=
    listDerivesFirstOrderSuccessorCanonical left.toList
  have rightDerivation :=
    listDerivesFirstOrderSuccessorCanonical right.toList
  have canonicalEqual :
      firstOrderSuccessorCanonicalList left.toList =
        firstOrderSuccessorCanonicalList right.toList :=
    (agreement left).trans <|
      (exactCanonicalList_eq_of_sameSignature same).trans
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

theorem stableScannerAgreement_implies_ownerLift
    (agreement : StableScannerSignatureAgreement) :
    ∀ identity : Identity Nat,
      firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList →
        Derives SemigroupBasis.CoRoots.S5_402.basis
          identity.lhs identity.rhs →
          Derives basis identity.lhs identity.rhs := by
  intro identity order lower
  exact derives_of_stableScannerAgreement agreement
    identity.lhs identity.rhs
    ⟨order, SemigroupBasis.CoRoots.S5_402.derives_sameSignature lower⟩

/-- A repeated successor after a globally simple letter must be retained. -/
theorem stableScanner_preserves_repeated_simpleSuccessor_example :
    firstOrderSuccessorCanonicalList [0, 1, 0, 2] =
      [0, 0, 1, 0, 0, 2] := by
  decide

/-- The independent signature renderer predicts the exact same boundary. -/
theorem exactSignature_preserves_repeated_simpleSuccessor_example :
    exactFirstOrderSignatureCanonicalList (Word.mk 0 [1, 0, 2]) =
      [0, 0, 1, 0, 0, 2] := by
  decide

/-! ## Exact unrestricted owner obligation -/

/-- Lift the complete lower proof exactly when all first occurrences agree. -/
def FirstOccurrencePreservingSimpleSuccessorLift : Prop :=
  ∀ identity : Identity Nat,
    firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList →
      Derives SemigroupBasis.CoRoots.S5_402.basis
        identity.lhs identity.rhs →
        Derives basis identity.lhs identity.rhs

/-- The missing lift is equivalent to complete exact-signature reachability. -/
theorem lift_iff_jointSignatureReach :
    FirstOccurrencePreservingSimpleSuccessorLift ↔
      (∀ {left right : Word Nat},
        SameFirstOrderSimpleSuccessorSignature left right →
          Derives basis left right) := by
  constructor
  · intro lift left right same
    exact lift ⟨left, right⟩ same.firstOrder
      (SemigroupBasis.CoRoots.S5_402.derivesOfSameSimpleSuccessorSignature
        same.simpleSuccessor)
  · intro reach identity same lowerDerivation
    exact reach
      ⟨same, SemigroupBasis.CoRoots.S5_402.derives_sameSignature
        lowerDerivation⟩

/-- A separately proved lift, and only then, gives the exact intersection. -/
def intersectionBasis_of_simpleSuccessorLift
    (lift : FirstOccurrencePreservingSimpleSuccessorLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact lift identity
      (firstOccurrences_of_leftValid identity leftValid)
      (SemigroupBasis.CoRoots.S5_402.basisFor.2 identity rightValid)

/-- Every actual owner intersection conversely proves the exact lift. -/
theorem simpleSuccessorLift_of_intersectionBasis
    (intersection :
      IntersectionBasis leftTable.semigroup rightTable.semigroup basis) :
    FirstOccurrencePreservingSimpleSuccessorLift := by
  intro identity same lowerDerivation
  exact intersection.complete identity
    (leftValid_of_firstOccurrences identity same)
    (lowerDerivation.sound SemigroupBasis.CoRoots.S5_402.models)

/-- Honest owner boundary: no unconditional normalizer is manufactured. -/
theorem intersection_exists_iff_simpleSuccessorLift :
    Nonempty
      (IntersectionBasis leftTable.semigroup rightTable.semigroup basis) ↔
      FirstOccurrencePreservingSimpleSuccessorLift := by
  constructor
  · rintro ⟨intersection⟩
    exact simpleSuccessorLift_of_intersectionBasis intersection
  · intro lift
    exact ⟨intersectionBasis_of_simpleSuccessorLift lift⟩

/-! ## Formal refutations of three genuinely distinct shortcut strategies -/

/-- Whole lower-owner replay fails: factor-left changes first-occurrence order. -/
theorem lowerFactorLeft_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1, 2, 1])
      (Word.mk 0 [0, 2, 1, 1]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 1 else if letter = 1 then 0 else 2
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- The lower sorting engine's factor swap has the same genuine obstruction. -/
theorem lowerFactorSwap_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1, 2, 1])
      (Word.mk 0 [2, 0, 1, 1]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 1 else if letter = 1 then 0 else 2
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- Lower simple-block sorting also changes the true left-factor first order. -/
theorem lowerSimpleBlockSwap_not_derivable :
    ¬ Derives basis (Word.mk 0 [1, 0, 2, 0])
      (Word.mk 0 [2, 0, 1, 0]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 1 else if letter = 1 then 0 else 2
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- Generic LRB idempotence destroys the genuine capped multiplicity. -/
theorem lrbIdempotence_not_derivable :
    ¬ Derives basis (Word.singleton 0) (Word.mk 0 [0]) := by
  intro derivation
  have evaluated := derivation.sound rightModels (fun _ => (1 : Fin 5))
  change (1 : Fin 5) = 0 at evaluated
  exact (by decide : (1 : Fin 5) ≠ 0) evaluated

/-- Generic LRB regularity is likewise false on actual direct `S5_402`. -/
theorem lrbRegularity_not_derivable :
    ¬ Derives basis (Word.mk 0 [1]) (Word.mk 0 [1, 0]) := by
  intro derivation
  let valuation : Nat → Fin 5 :=
    fun letter => if letter = 0 then 1 else 4
  have evaluated := derivation.sound rightModels valuation
  change (2 : Fin 5) = 0 at evaluated
  exact (by decide : (2 : Fin 5) ≠ 0) evaluated

/-- Rank 089's one-final-guard contraction is false on the new right factor. -/
theorem priorRank089PrefixContraction_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1]) := by
  intro derivation
  let valuation : Nat → Fin 5 :=
    fun letter => if letter = 0 then 1 else 4
  have evaluated := derivation.sound rightModels valuation
  change (0 : Fin 5) = 2 at evaluated
  exact (by decide : (0 : Fin 5) ≠ 2) evaluated

/-- The exact one class and both orientations follow only from the owner lift. -/
theorem both_orientations_of_simpleSuccessorLift
    (lift : FirstOccurrencePreservingSimpleSuccessorLift) :
    BasisFor S6_8281.table.semigroup basis ∧
      BasisFor S6_8281.table.semigroup.opposite (reversedBasis basis) := by
  let owner := intersectionBasis_of_simpleSuccessorLift lift
  let normalizer :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      owner
  exact
    ⟨S6_8281.representative_basis_of_normalizer normalizer,
      S6_8281.opposite_basis_of_normalizer normalizer⟩

/-- The one remaining pure scanner lemma would discharge both endpoints. -/
theorem both_orientations_of_stableScannerAgreement
    (agreement : StableScannerSignatureAgreement) :
    BasisFor S6_8281.table.semigroup basis ∧
      BasisFor S6_8281.table.semigroup.opposite (reversedBasis basis) :=
  both_orientations_of_simpleSuccessorLift
    (stableScannerAgreement_implies_ownerLift agreement)

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge
