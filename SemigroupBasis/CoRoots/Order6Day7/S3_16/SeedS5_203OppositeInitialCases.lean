import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_203OppositeInitialMoves

/-!
# Unrestricted first-order / initial-state completeness for rank 082

The direct left factor fixes full first-occurrence order.  The opposite
right factor fixes the exact S5_203 terminal signature of reversed words.
The new safe padding moves close the five initial strata without changing
either factor orientation, weakening the owner obligation, or assuming
global guard cancellation.  The original twenty-two laws are unchanged.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialSeed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83
open InitialGuard

abbrev InitialSignature (left right : Word Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature
    left.reverse right.reverse

abbrev InitialDoubleton (word : Word Nat) (selected : Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton
    word.reverse selected

/-- Reversal converts the literal initial pair into the exact terminal
renderer; it does not reverse the left factor's identity theory. -/
theorem reverse_initialWord (initial second : Nat) (tail : List Nat) :
    (initialWord initial second tail).reverse =
      (TerminalSplit.pair tail.reverse second initial).renderWord := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_initialWord, TerminalSplit.toList_renderWord]
  simp [TerminalSplit.renderList, List.reverse_cons, List.append_assoc]

/-- The reversed terminal split retains precisely the actual initial pair. -/
theorem terminalSplit_reverse_initialWord
    (initial second : Nat) (tail : List Nat) :
    terminalSplit (initialWord initial second tail).reverse =
      .pair tail.reverse second initial := by
  rw [reverse_initialWord, terminalSplit_renderWord_inverse]

private theorem uniqueInitial_pair_iff (initial second : Nat)
    (tail : List Nat) (selected : Nat) :
    UniqueFinal (initialWord initial second tail).reverse selected ↔
      initial = selected ∧ initial ≠ second ∧ initial ∉ tail := by
  simp [UniqueFinal, terminalSplit_reverse_initialWord]

private theorem uniqueInitialPair_pair_iff (initial second : Nat)
    (tail : List Nat) (selectedSecond selectedInitial : Nat) :
    UniqueTerminalPair (initialWord initial second tail).reverse
        selectedSecond selectedInitial ↔
      second = selectedSecond ∧ initial = selectedInitial ∧
        selectedSecond ∉ tail ∧ selectedInitial ≠ selectedSecond ∧
          selectedInitial ∉ tail := by
  simp [UniqueTerminalPair, terminalSplit_reverse_initialWord]

private theorem doubleton_pair_iff (initial second : Nat)
    (tail : List Nat) (selected : Nat) :
    InitialDoubleton (initialWord initial second tail) selected ↔
      second = selected ∧ initial = selected ∧ selected ∉ tail := by
  simp [InitialDoubleton,
    SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
    terminalSplit_reverse_initialWord]

private theorem mem_firstOrder_iff (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | first :: rest => by
      by_cases equal : selected = first
      · subst selected
        simp [firstOccurrenceSequence]
      · have induction := mem_firstOrder_iff selected rest
        simp [firstOccurrenceSequence, induction, equal]

/-- A fresh variable does not remove anything from the tail's first order. -/
theorem filter_firstOrder_of_fresh (selected : Nat) (letters : List Nat)
    (fresh : selected ∉ letters) :
    (firstOccurrenceSequence letters).filter (fun letter => decide (letter ≠ selected)) =
      firstOccurrenceSequence letters := by
  apply List.filter_eq_self.mpr
  intro letter present
  simp only [decide_eq_true_eq]
  intro equal
  subst letter
  exact fresh ((mem_firstOrder_iff selected letters).mp present)

/-- A unique initial variable prepends literally to the tail's first order. -/
theorem firstOrder_cons_of_fresh (initial : Nat) (tail : List Nat)
    (fresh : initial ∉ tail) :
    firstOccurrenceSequence (initial :: tail) =
      initial :: firstOccurrenceSequence tail := by
  simp only [firstOccurrenceSequence, filter_firstOrder_of_fresh initial tail fresh]

/-- A fresh initial doubleton contributes one first occurrence, but remains
a distinct initial-state stratum from an initial cube. -/
theorem firstOrder_initialDoubleton (initial : Nat) (tail : List Nat)
    (fresh : initial ∉ tail) :
    firstOccurrenceSequence (initial :: initial :: tail) =
      initial :: firstOccurrenceSequence tail := by
  simp [firstOccurrenceSequence]
  intro letter present equal
  subst letter
  exact fresh ((mem_firstOrder_iff initial tail).mp present)

/-- Equal full first-occurrence orders fix the actual head variable. -/
theorem head_eq_of_firstOrder {left right : Word Nat}
    (order : firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList) : left.head = right.head := by
  have heads := congrArg List.head? order
  simpa [Word.toList, firstOccurrenceSequence] using heads

/-- Complete initial-pair analysis with no bound on the tail or alphabet. -/
theorem derivesInitialPairs_of_signature (initial leftSecond rightSecond : Nat)
    (leftTail rightTail : List Nat)
    (order : firstOccurrenceSequence (initial :: leftSecond :: leftTail) =
      firstOccurrenceSequence (initial :: rightSecond :: rightTail))
    (signature : InitialSignature (initialWord initial leftSecond leftTail)
      (initialWord initial rightSecond rightTail)) :
    Derives basis (initialWord initial leftSecond leftTail)
      (initialWord initial rightSecond rightTail) := by
  classical
  by_cases leftUnique :
      UniqueFinal (initialWord initial leftSecond leftTail).reverse initial
  · have leftParts := (uniqueInitial_pair_iff _ _ _ _).mp leftUnique
    have rightUnique := (signature.uniqueFinal initial).mp leftUnique
    have rightParts := (uniqueInitial_pair_iff _ _ _ _).mp rightUnique
    have tailOrder : firstOccurrenceSequence (leftSecond :: leftTail) =
        firstOccurrenceSequence (rightSecond :: rightTail) := by
      have full := order
      rw [firstOrder_cons_of_fresh initial (leftSecond :: leftTail)
          (by simp [leftParts.2.1, leftParts.2.2]),
        firstOrder_cons_of_fresh initial (rightSecond :: rightTail)
          (by simp [rightParts.2.1, rightParts.2.2])] at full
      exact (List.cons.inj full).2
    have secondEqual : leftSecond = rightSecond :=
      head_eq_of_firstOrder (left := Word.mk leftSecond leftTail)
        (right := Word.mk rightSecond rightTail) tailOrder
    subst rightSecond
    by_cases leftSecondFresh : leftSecond ∉ leftTail
    · have leftPair :
          UniqueTerminalPair (initialWord initial leftSecond leftTail).reverse
            leftSecond initial :=
        (uniqueInitialPair_pair_iff _ _ _ _ _).mpr
          ⟨rfl, rfl, leftSecondFresh, leftParts.2.1, leftParts.2.2⟩
      have rightPair :=
        (signature.uniqueTerminalPairOfUniqueFinal
          leftSecond initial leftUnique).mp leftPair
      have rightPairParts := (uniqueInitialPair_pair_iff _ _ _ _ _).mp rightPair
      have tailOnlyOrder : firstOccurrenceSequence leftTail =
          firstOccurrenceSequence rightTail := by
        rw [firstOrder_cons_of_fresh leftSecond leftTail leftSecondFresh,
          firstOrder_cons_of_fresh leftSecond rightTail rightPairParts.2.2.1] at tailOrder
        exact (List.cons.inj tailOrder).2
      exact derivesSameTailFirstOrder initial leftSecond leftTail rightTail tailOnlyOrder
    · have leftSeen : leftSecond ∈ leftTail := Classical.byContradiction leftSecondFresh
      have rightSeen : leftSecond ∈ rightTail := by
        apply Classical.byContradiction
        intro fresh
        have rightPair :
            UniqueTerminalPair (initialWord initial leftSecond rightTail).reverse
              leftSecond initial :=
          (uniqueInitialPair_pair_iff _ _ _ _ _).mpr
            ⟨rfl, rfl, fresh, rightParts.2.1, rightParts.2.2⟩
        have leftPair :=
          (signature.uniqueTerminalPairOfUniqueFinal
            leftSecond initial leftUnique).mpr rightPair
        have leftPairParts := (uniqueInitialPair_pair_iff _ _ _ _ _).mp leftPair
        exact leftPairParts.2.2.1 leftSeen
      have middle :
          Derives basis (initialWord initial leftSecond (leftSecond :: leftTail))
            (initialWord initial leftSecond (leftSecond :: rightTail)) :=
        derivesSameFirstOrderUnderInitialPair
          (Word.mk leftSecond leftTail) (Word.mk leftSecond rightTail)
          (Word.singleton initial) (Word.singleton leftSecond) tailOrder
      exact (derivesSeenSecondPadding initial leftSecond leftTail leftSeen).trans <|
        middle.trans (derivesSeenSecondPadding initial leftSecond rightTail rightSeen).symm
  · by_cases leftDoubleton :
        InitialDoubleton (initialWord initial leftSecond leftTail) initial
    · have leftParts := (doubleton_pair_iff _ _ _ _).mp leftDoubleton
      have rightDoubleton := (signature.terminalDoubleton initial).mp leftDoubleton
      have rightParts := (doubleton_pair_iff _ _ _ _).mp rightDoubleton
      have leftSecondEqual : leftSecond = initial := leftParts.1
      have rightSecondEqual : rightSecond = initial := rightParts.1
      subst leftSecond
      subst rightSecond
      have tailOrder : firstOccurrenceSequence leftTail =
          firstOccurrenceSequence rightTail := by
        rw [firstOrder_initialDoubleton initial leftTail leftParts.2.2,
          firstOrder_initialDoubleton initial rightTail rightParts.2.2] at order
        exact (List.cons.inj order).2
      exact derivesSameTailFirstOrder initial initial leftTail rightTail tailOrder
    · have leftSeen : initial ∈ leftTail := by
        apply Classical.byContradiction
        intro fresh
        by_cases equal : initial = leftSecond
        · exact leftDoubleton
            ((doubleton_pair_iff _ _ _ _).mpr ⟨equal.symm, rfl, fresh⟩)
        · exact leftUnique
            ((uniqueInitial_pair_iff _ _ _ _).mpr ⟨rfl, equal, fresh⟩)
      have rightSeen : initial ∈ rightTail := by
        apply Classical.byContradiction
        intro fresh
        by_cases equal : initial = rightSecond
        · have rightDoubleton :
              InitialDoubleton (initialWord initial rightSecond rightTail) initial :=
            (doubleton_pair_iff _ _ _ _).mpr ⟨equal.symm, rfl, fresh⟩
          exact leftDoubleton ((signature.terminalDoubleton initial).mpr rightDoubleton)
        · have rightUnique :
              UniqueFinal (initialWord initial rightSecond rightTail).reverse initial :=
            (uniqueInitial_pair_iff _ _ _ _).mpr ⟨rfl, equal, fresh⟩
          exact leftUnique ((signature.uniqueFinal initial).mpr rightUnique)
      have middle := derivesSameFirstOrderUnderInitialPair
        (initialWord initial leftSecond leftTail) (initialWord initial rightSecond rightTail)
        (Word.singleton initial) (Word.singleton initial) order
      exact (derivesGenericInitialGuards initial leftSecond leftTail leftSeen).trans <|
        middle.trans (derivesGenericInitialGuards initial rightSecond rightTail rightSeen).symm

/-- Full first order and the exact reversed terminal signature imply an
unrestricted derivation, including singleton and empty-tail cases. -/
theorem derives_of_firstOrder_initialSignature (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList)
    (signature : InitialSignature left right) : Derives basis left right := by
  cases left with
  | mk leftInitial leftTail =>
      cases right with
      | mk rightInitial rightTail =>
          have initialEqual : leftInitial = rightInitial := head_eq_of_firstOrder order
          subst rightInitial
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil => exact Derives.refl _
              | cons second tail =>
                  have impossible : IsSingletonWord (initialWord leftInitial second tail).reverse :=
                    signature.singleton.mp (by trivial)
                  simp [IsSingletonWord, terminalSplit_reverse_initialWord] at impossible
          | cons leftSecond leftRest =>
              cases rightTail with
              | nil =>
                  have impossible : IsSingletonWord (initialWord leftInitial leftSecond leftRest).reverse :=
                    signature.singleton.mpr (by trivial)
                  simp [IsSingletonWord, terminalSplit_reverse_initialWord] at impossible
              | cons rightSecond rightRest =>
                  exact derivesInitialPairs_of_signature leftInitial leftSecond rightSecond
                    leftRest rightRest order signature

/-- Unconditional completeness for the exact actual-factor intersection. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact derives_of_firstOrder_initialSignature identity.lhs identity.rhs
      (firstOccurrences_of_targetLeftValid identity leftValid)
      (initialSignature_of_targetRightValid identity rightValid)

/-- Discharge precisely the old owner lift, retaining both validity premises. -/
theorem firstOccurrenceInitialTerminalSignatureLift : FirstOccurrenceInitialTerminalSignatureLift :=
  targetIntersection_iff_ownerLift.mp intersectionBasis

/-- The pair-valid cancellation obligation is proved; global cancellation
is neither assumed nor implied. -/
theorem pairValidInitialDoubleGuardCancellation : PairValidInitialDoubleGuardCancellation :=
  ownerLift_iff_pairValidInitialDoubleGuardCancellation.mp
    firstOccurrenceInitialTerminalSignatureLift

/-- Reuse the existing C1 quotient-normalizer transport shape. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  normalizer_of_ownerLift firstOccurrenceInitialTerminalSignatureLift

/-- Unconditional representative basis through the original frozen maps. -/
theorem s6_5636_representative_basis : BasisFor S6_5636.table.semigroup basis :=
  S6_5636.representative_basis_of_normalizer normalizer

/-- Unconditional opposite basis for the literally reversed raw22 list. -/
theorem s6_5636_opposite_basis :
    BasisFor S6_5636.table.semigroup.opposite (reversedBasis basis) :=
  S6_5636.opposite_basis_of_normalizer normalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank082.InitialSeed
