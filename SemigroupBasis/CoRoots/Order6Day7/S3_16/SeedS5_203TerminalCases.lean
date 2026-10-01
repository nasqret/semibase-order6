import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_203TerminalMoves

/-!
# Unrestricted terminal completeness for S3_16 x S5_203

Full first-occurrence order and the exact S5_203 terminal signature suffice
for the unchanged twelve-law rank-081 presentation.  The proof separates
singleton words, globally unique terminal pairs, repeated penultimates
with unique finals, fresh terminal doubletons, and the generic repeated
final stratum.  Only the last stratum uses the safe absorption theorem.

This discharges the old owner-lift obligation and gives unconditional
representative and opposite basis theorems for S6_5581.  The finite screen
is not imported or used as an unrestricted premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.TerminalSeed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83
open DoubleGuard
open SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed
  (firstOccurrenceSequence_append_final terminalSplit_wordOfTerminalPair)

abbrev TerminalSignature :=
  SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.SameSupportTerminalStateSignature

abbrev TerminalDoubleton :=
  SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton

private theorem uniqueFinal_pair_iff (stem : List Nat)
    (penultimate final selected : Nat) :
    UniqueFinal (pairWord stem penultimate final) selected ↔
      final = selected ∧ final ≠ penultimate ∧ final ∉ stem := by
  simp [UniqueFinal, pairWord, terminalSplit_wordOfTerminalPair]

private theorem uniquePair_pair_iff (stem : List Nat)
    (penultimate final selectedPenultimate selectedFinal : Nat) :
    UniqueTerminalPair (pairWord stem penultimate final)
        selectedPenultimate selectedFinal ↔
      penultimate = selectedPenultimate ∧ final = selectedFinal ∧
        selectedPenultimate ∉ stem ∧ selectedFinal ≠ selectedPenultimate ∧
          selectedFinal ∉ stem := by
  simp [UniqueTerminalPair, pairWord, terminalSplit_wordOfTerminalPair]

private theorem doubleton_pair_iff (stem : List Nat)
    (penultimate final selected : Nat) :
    TerminalDoubleton (pairWord stem penultimate final) selected ↔
      penultimate = selected ∧ final = selected ∧ selected ∉ stem := by
  simp [TerminalDoubleton,
    SemigroupBasis.CoRoots.S5_203.DirectCompletenessArchitecture.TerminalDoubleton,
    pairWord, terminalSplit_wordOfTerminalPair]

/-- Two fresh distinct terminal letters are appended to the stem order. -/
theorem firstOrder_freshPair (stem : List Nat) (penultimate final : Nat)
    (penultimateFresh : penultimate ∉ stem) (finalFresh : final ∉ stem)
    (distinct : final ≠ penultimate) :
    firstOccurrenceSequence (stem ++ [penultimate, final]) =
      firstOccurrenceSequence stem ++ [penultimate, final] := by
  rw [show stem ++ [penultimate, final] =
    (stem ++ [penultimate]) ++ [final] by simp]
  simp only [firstOccurrenceSequence_append_final, List.mem_append,
    List.mem_singleton, penultimateFresh, finalFresh, distinct,
    false_or, if_false]
  simp

/-- A repeated penultimate and fresh final add just the final to stem order. -/
theorem firstOrder_repeatedPenultimate (stem : List Nat)
    (penultimate final : Nat) (penultimateSeen : penultimate ∈ stem)
    (finalFresh : final ∉ stem) (distinct : final ≠ penultimate) :
    firstOccurrenceSequence (stem ++ [penultimate, final]) =
      firstOccurrenceSequence stem ++ [final] := by
  rw [show stem ++ [penultimate, final] =
    (stem ++ [penultimate]) ++ [final] by simp]
  simp only [firstOccurrenceSequence_append_final, List.mem_append,
    List.mem_singleton, penultimateSeen, finalFresh, distinct,
    false_or, if_false, if_true]

/-- A fresh terminal doubleton adds its variable exactly once to first order. -/
theorem firstOrder_doubleton (stem : List Nat) (final : Nat)
    (fresh : final ∉ stem) :
    firstOccurrenceSequence (stem ++ [final, final]) =
      firstOccurrenceSequence stem ++ [final] := by
  rw [show stem ++ [final, final] = (stem ++ [final]) ++ [final] by simp]
  simp only [firstOccurrenceSequence_append_final, List.mem_append,
    List.mem_singleton, fresh, false_or, eq_self, if_true, if_false]

/-- Repeated penultimates can be retargeted to the common initial letter
while preserving the identical final guard. -/
theorem derivesUniqueFinalRepeated (leftStem rightStem : List Nat)
    (leftPenultimate rightPenultimate final : Nat)
    (leftSeen : leftPenultimate ∈ leftStem)
    (rightSeen : rightPenultimate ∈ rightStem)
    (order : firstOccurrenceSequence leftStem =
      firstOccurrenceSequence rightStem) :
    Derives basis (pairWord leftStem leftPenultimate final)
      (pairWord rightStem rightPenultimate final) := by
  cases leftStem with
  | nil => simp at leftSeen
  | cons leftFirst leftRest =>
      cases rightStem with
      | nil => simp at rightSeen
      | cons rightFirst rightRest =>
          have equalHeads : leftFirst = rightFirst :=
            head_eq_of_firstOrder
              (left := Word.mk leftFirst leftRest)
              (right := Word.mk rightFirst rightRest) order
          subst rightFirst
          change Derives basis
            (pairWord (Word.mk leftFirst leftRest).toList leftPenultimate final)
            (pairWord (Word.mk leftFirst rightRest).toList rightPenultimate final)
          rw [pairWord_of_word, pairWord_of_word]
          have leftHeadSeen : leftFirst ∈ (Word.mk leftFirst leftRest).toList := by
            simp [Word.toList]
          have rightHeadSeen : leftFirst ∈ (Word.mk leftFirst rightRest).toList := by
            simp [Word.toList]
          exact (derivesChangeSeenPenultimate
            (Word.mk leftFirst leftRest) leftPenultimate leftFirst final
            leftSeen leftHeadSeen).trans <|
              (derivesSameFirstOrderUnderDoubleGuard
                (Word.mk leftFirst leftRest) (Word.mk leftFirst rightRest)
                (Word.singleton leftFirst) (Word.singleton final) order).trans
                  (derivesChangeSeenPenultimate
                    (Word.mk leftFirst rightRest) rightPenultimate leftFirst final
                    rightSeen rightHeadSeen).symm

/-- In the generic stratum, both words absorb the same two head guards;
the old first-order bridge then applies literally to the whole words. -/
theorem derivesGenericPairs (leftStem rightStem : List Nat)
    (leftPenultimate leftFinal rightPenultimate rightFinal : Nat)
    (leftSeen : leftFinal ∈ leftStem) (rightSeen : rightFinal ∈ rightStem)
    (order : firstOccurrenceSequence (leftStem ++ [leftPenultimate, leftFinal]) =
      firstOccurrenceSequence (rightStem ++ [rightPenultimate, rightFinal])) :
    Derives basis (pairWord leftStem leftPenultimate leftFinal)
      (pairWord rightStem rightPenultimate rightFinal) := by
  cases leftStem with
  | nil => simp at leftSeen
  | cons leftFirst leftRest =>
      cases rightStem with
      | nil => simp at rightSeen
      | cons rightFirst rightRest =>
          have equalHeads : leftFirst = rightFirst := by
            have heads := congrArg List.head? order
            simpa [firstOccurrenceSequence] using heads
          subst rightFirst
          change Derives basis
            (pairWord (Word.mk leftFirst leftRest).toList leftPenultimate leftFinal)
            (pairWord (Word.mk leftFirst rightRest).toList rightPenultimate rightFinal)
          rw [pairWord_of_word, pairWord_of_word]
          have leftHeadSeen : leftFirst ∈ (Word.mk leftFirst leftRest).toList := by
            simp [Word.toList]
          have rightHeadSeen : leftFirst ∈ (Word.mk leftFirst rightRest).toList := by
            simp [Word.toList]
          have wholeOrder :
              firstOccurrenceSequence
                  (((Word.mk leftFirst leftRest ++ Word.singleton leftPenultimate) ++
                    Word.singleton leftFinal).toList) =
                firstOccurrenceSequence
                  (((Word.mk leftFirst rightRest ++ Word.singleton rightPenultimate) ++
                    Word.singleton rightFinal).toList) := by
            simp only [Word.toList_append, Word.toList_singleton]
            simpa only [Word.toList, List.cons_append, List.append_assoc,
              List.nil_append] using order
          exact (derivesGenericDoubleGuard
            (Word.mk leftFirst leftRest) leftPenultimate leftFinal leftFirst
            leftSeen leftHeadSeen).trans <|
              (derivesSameFirstOrderUnderDoubleGuard
                ((Word.mk leftFirst leftRest ++ Word.singleton leftPenultimate) ++
                  Word.singleton leftFinal)
                ((Word.mk leftFirst rightRest ++ Word.singleton rightPenultimate) ++
                  Word.singleton rightFinal)
                (Word.singleton leftFirst) (Word.singleton leftFirst) wholeOrder).trans
                  (derivesGenericDoubleGuard
                    (Word.mk leftFirst rightRest) rightPenultimate rightFinal leftFirst
                    rightSeen rightHeadSeen).symm

/-- Complete terminal-pair analysis; doubletons remain a separate stratum. -/
theorem derivesPairs_of_signature (leftStem rightStem : List Nat)
    (leftPenultimate leftFinal rightPenultimate rightFinal : Nat)
    (order : firstOccurrenceSequence (leftStem ++ [leftPenultimate, leftFinal]) =
      firstOccurrenceSequence (rightStem ++ [rightPenultimate, rightFinal]))
    (signature : TerminalSignature
      (pairWord leftStem leftPenultimate leftFinal)
      (pairWord rightStem rightPenultimate rightFinal)) :
    Derives basis (pairWord leftStem leftPenultimate leftFinal)
      (pairWord rightStem rightPenultimate rightFinal) := by
  classical
  by_cases leftUnique :
      UniqueFinal (pairWord leftStem leftPenultimate leftFinal) leftFinal
  · have leftParts := (uniqueFinal_pair_iff _ _ _ _).mp leftUnique
    have rightUnique := (signature.uniqueFinal leftFinal).mp leftUnique
    have rightParts := (uniqueFinal_pair_iff _ _ _ _).mp rightUnique
    have finalEqual : rightFinal = leftFinal := rightParts.1
    subst rightFinal
    by_cases leftPenultimateFresh : leftPenultimate ∉ leftStem
    · have leftPair :
          UniqueTerminalPair (pairWord leftStem leftPenultimate leftFinal)
            leftPenultimate leftFinal :=
        (uniquePair_pair_iff _ _ _ _ _).mpr
          ⟨rfl, rfl, leftPenultimateFresh, leftParts.2.1, leftParts.2.2⟩
      have rightPair :=
        (signature.uniqueTerminalPairOfUniqueFinal
          leftPenultimate leftFinal leftUnique).mp leftPair
      have rightPairParts := (uniquePair_pair_iff _ _ _ _ _).mp rightPair
      have penultimateEqual : rightPenultimate = leftPenultimate := rightPairParts.1
      subst rightPenultimate
      have stemOrder : firstOccurrenceSequence leftStem =
          firstOccurrenceSequence rightStem := by
        have withPair :
            firstOccurrenceSequence leftStem ++ [leftPenultimate, leftFinal] =
              firstOccurrenceSequence rightStem ++ [leftPenultimate, leftFinal] := by
          simpa only [firstOrder_freshPair leftStem leftPenultimate leftFinal
              leftPenultimateFresh leftParts.2.2 leftParts.2.1,
            firstOrder_freshPair rightStem leftPenultimate leftFinal
              rightPairParts.2.2.1 rightParts.2.2 rightParts.2.1] using order
        exact List.append_cancel_right withPair
      exact derivesSameStemFirstOrder leftStem rightStem leftPenultimate leftFinal
        stemOrder
    · have leftSeen : leftPenultimate ∈ leftStem :=
        Classical.byContradiction leftPenultimateFresh
      have rightSeen : rightPenultimate ∈ rightStem := by
        apply Classical.byContradiction
        intro fresh
        have rightPair :
            UniqueTerminalPair (pairWord rightStem rightPenultimate leftFinal)
              rightPenultimate leftFinal :=
          (uniquePair_pair_iff _ _ _ _ _).mpr
            ⟨rfl, rfl, fresh, rightParts.2.1, rightParts.2.2⟩
        have leftPair :=
          (signature.uniqueTerminalPairOfUniqueFinal
            rightPenultimate leftFinal leftUnique).mpr rightPair
        have leftPairParts := (uniquePair_pair_iff _ _ _ _ _).mp leftPair
        apply leftPairParts.2.2.1
        rw [← leftPairParts.1]
        exact leftSeen
      have stemOrder : firstOccurrenceSequence leftStem =
          firstOccurrenceSequence rightStem := by
        have withFinal : firstOccurrenceSequence leftStem ++ [leftFinal] =
            firstOccurrenceSequence rightStem ++ [leftFinal] := by
          simpa only [firstOrder_repeatedPenultimate leftStem leftPenultimate leftFinal
              leftSeen leftParts.2.2 leftParts.2.1,
            firstOrder_repeatedPenultimate rightStem rightPenultimate leftFinal
              rightSeen rightParts.2.2 rightParts.2.1] using order
        exact List.append_cancel_right withFinal
      exact derivesUniqueFinalRepeated leftStem rightStem leftPenultimate
        rightPenultimate leftFinal leftSeen rightSeen stemOrder
  · by_cases leftDoubleton :
        TerminalDoubleton (pairWord leftStem leftPenultimate leftFinal) leftFinal
    · have leftParts := (doubleton_pair_iff _ _ _ _).mp leftDoubleton
      have rightDoubleton := (signature.terminalDoubleton leftFinal).mp leftDoubleton
      have rightParts := (doubleton_pair_iff _ _ _ _).mp rightDoubleton
      have leftPenultimateEqual : leftPenultimate = leftFinal := leftParts.1
      have rightPenultimateEqual : rightPenultimate = leftFinal := rightParts.1
      have rightFinalEqual : rightFinal = leftFinal := rightParts.2.1
      subst leftPenultimate
      subst rightPenultimate
      subst rightFinal
      have stemOrder : firstOccurrenceSequence leftStem =
          firstOccurrenceSequence rightStem := by
        have withFinal : firstOccurrenceSequence leftStem ++ [leftFinal] =
            firstOccurrenceSequence rightStem ++ [leftFinal] := by
          simpa only [firstOrder_doubleton leftStem leftFinal leftParts.2.2,
            firstOrder_doubleton rightStem leftFinal rightParts.2.2] using order
        exact List.append_cancel_right withFinal
      exact derivesSameStemFirstOrder leftStem rightStem leftFinal leftFinal stemOrder
    · have leftSeen : leftFinal ∈ leftStem := by
        apply Classical.byContradiction
        intro fresh
        by_cases equal : leftFinal = leftPenultimate
        · exact leftDoubleton
            ((doubleton_pair_iff _ _ _ _).mpr ⟨equal.symm, rfl, fresh⟩)
        · exact leftUnique
            ((uniqueFinal_pair_iff _ _ _ _).mpr ⟨rfl, equal, fresh⟩)
      have rightSeen : rightFinal ∈ rightStem := by
        apply Classical.byContradiction
        intro fresh
        by_cases equal : rightFinal = rightPenultimate
        · have rightDoubleton :
              TerminalDoubleton (pairWord rightStem rightPenultimate rightFinal)
                rightFinal :=
            (doubleton_pair_iff _ _ _ _).mpr ⟨equal.symm, rfl, fresh⟩
          have leftOther := (signature.terminalDoubleton rightFinal).mpr rightDoubleton
          have leftParts := (doubleton_pair_iff _ _ _ _).mp leftOther
          have finalEqual : leftFinal = rightFinal := leftParts.2.1
          exact leftDoubleton (by simpa only [← finalEqual] using leftOther)
        · have rightUnique :
              UniqueFinal (pairWord rightStem rightPenultimate rightFinal) rightFinal :=
            (uniqueFinal_pair_iff _ _ _ _).mpr ⟨rfl, equal, fresh⟩
          have leftOther := (signature.uniqueFinal rightFinal).mpr rightUnique
          have leftParts := (uniqueFinal_pair_iff _ _ _ _).mp leftOther
          have finalEqual : leftFinal = rightFinal := leftParts.1
          exact leftUnique (by simpa only [← finalEqual] using leftOther)
      exact derivesGenericPairs leftStem rightStem leftPenultimate leftFinal
        rightPenultimate rightFinal leftSeen rightSeen order

/-- Full first order and the exact terminal signature imply an unrestricted
derivation, including singleton and empty-stem boundary cases. -/
theorem derives_of_firstOrder_terminalSignature (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList)
    (signature : TerminalSignature left right) : Derives basis left right := by
  cases leftSplit : terminalSplit left with
  | singleton leftFinal =>
      have rendered := terminalSplit_renderWord left
      rw [leftSplit] at rendered
      have leftShape : left = Word.singleton leftFinal := by
        simpa [TerminalSplit.renderWord] using rendered.symm
      have rightSingleton : IsSingletonWord right :=
        signature.singleton.mp (by simp [IsSingletonWord, leftSplit])
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have renderedRight := terminalSplit_renderWord right
          rw [rightSplit] at renderedRight
          have rightShape : right = Word.singleton rightFinal := by
            simpa [TerminalSplit.renderWord] using renderedRight.symm
          rw [leftShape, rightShape] at order ⊢
          have finalEqual : leftFinal = rightFinal := head_eq_of_firstOrder order
          rw [finalEqual]
          exact Derives.refl _
      | pair stem penultimate final =>
          simp [IsSingletonWord, rightSplit] at rightSingleton
  | pair leftStem leftPenultimate leftFinal =>
      have rendered := terminalSplit_renderWord left
      rw [leftSplit] at rendered
      have leftShape : left = pairWord leftStem leftPenultimate leftFinal := by
        simpa [TerminalSplit.renderWord, pairWord,
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair] using rendered.symm
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have leftSingleton : IsSingletonWord left :=
            signature.singleton.mpr (by simp [IsSingletonWord, rightSplit])
          simp [IsSingletonWord, leftSplit] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          have renderedRight := terminalSplit_renderWord right
          rw [rightSplit] at renderedRight
          have rightShape : right = pairWord rightStem rightPenultimate rightFinal := by
            simpa [TerminalSplit.renderWord, pairWord,
              SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair] using renderedRight.symm
          rw [leftShape, rightShape] at order signature ⊢
          apply derivesPairs_of_signature leftStem rightStem leftPenultimate leftFinal
            rightPenultimate rightFinal ?_ signature
          simpa only [pairWord,
            SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair] using order

/-- The exact unchanged twelve-law intersection is now unconditional. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact derives_of_firstOrder_terminalSignature identity.lhs identity.rhs
      (firstOccurrences_of_targetLeftValid identity leftValid)
      (terminalSignature_of_targetRightValid identity rightValid)

/-- Discharge precisely the formerly open owner lift, without weakening it. -/
theorem firstOccurrenceTerminalSignatureLift : FirstOccurrenceTerminalSignatureLift :=
  targetIntersection_iff_ownerLift.mp intersectionBasis

/-- Only the actual pair-valid cancellation obligation follows; the old
unrestricted global cancellation remains false. -/
theorem pairValidDoubleGuardCancellation : PairValidDoubleGuardCancellation :=
  ownerLift_iff_pairValidDoubleGuardCancellation.mp firstOccurrenceTerminalSignatureLift

/-- Reuse the existing C1 quotient-normalizer transport shape. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  normalizer_of_ownerLift firstOccurrenceTerminalSignatureLift

/-- Unconditional representative basis for the exact frozen class map. -/
theorem s6_5581_representative_basis : BasisFor S6_5581.table.semigroup basis :=
  S6_5581.representative_basis_of_normalizer normalizer

/-- Unconditional opposite basis, with the literally reversed presentation. -/
theorem s6_5581_opposite_basis :
    BasisFor S6_5581.table.semigroup.opposite (reversedBasis basis) :=
  S6_5581.opposite_basis_of_normalizer normalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank081.TerminalSeed
