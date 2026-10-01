import SemigroupBasis.CoRoots.S5_203Normalization

namespace SemigroupBasis.CoRoots.S5_203

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83
open DirectCompletenessArchitecture

local instance tableOrderNeZero : NeZero table.order :=
  ⟨by decide⟩

namespace DirectCompletenessArchitecture

/-- Assign the tested variable to catalogue element four and every other
variable to element five, in one-based catalogue terminology. -/
def terminalValuation (tested value : Nat) : Fin 5 :=
  if value = tested then 3 else 4

/-- The constant element-four valuation separates singleton words. -/
def singletonValuation : Nat → Fin 5 :=
  fun _ => 3

/-- Assign the candidate penultimate to element three, the candidate final to
element four, and every other variable to element five. -/
def pairValuation
    (candidatePenultimate candidateFinal value : Nat) : Fin 5 :=
  if value = candidatePenultimate then 2
  else if value = candidateFinal then 3
  else 4

@[simp]
private theorem terminalPairWord_cons
    (x : Nat) (stem : List Nat) (penultimate final : Nat) :
    terminalPairWord (x :: stem) penultimate final =
      Word.singleton x ++ terminalPairWord stem penultimate final := rfl

private theorem mul_ne_singleton
    (left right : Fin 5) :
    table.mul left right ≠ 3 := by
  decide +revert

private theorem terminalHit_ne_absent (value : Fin 5) :
    table.mul 3 value ≠ 4 := by
  decide +revert

private theorem terminalHit_ne_simple (value : Fin 5) :
    table.mul 3 value ≠ 2 := by
  decide +revert

private theorem terminalHit_eq_doubleton_iff (value : Fin 5) :
    table.mul 3 value = 1 ↔ value = 3 := by
  decide +revert

private theorem terminalPass_eq_absent_iff (value : Fin 5) :
    table.mul 4 value = 4 ↔ value = 4 := by
  decide +revert

private theorem terminalPass_eq_simple_iff (value : Fin 5) :
    table.mul 4 value = 2 ↔ value = 2 ∨ value = 3 := by
  decide +revert

private theorem terminalPass_eq_doubleton_iff (value : Fin 5) :
    table.mul 4 value = 1 ↔ value = 1 := by
  decide +revert

private theorem evalTerminalPair_ne_singleton
    (tested : Nat) :
    ∀ stem penultimate final,
      table.semigroup.eval (terminalValuation tested)
          (terminalPairWord stem penultimate final) ≠ 3
  | [], penultimate, final => by
      change
        table.mul
            (terminalValuation tested penultimate)
            (terminalValuation tested final) ≠ 3
      exact mul_ne_singleton _ _
  | x :: stem, penultimate, final => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_singleton _ _

private theorem evalTerminalPair_eq_absent_iff
    (tested : Nat) :
    ∀ stem penultimate final,
      table.semigroup.eval (terminalValuation tested)
          (terminalPairWord stem penultimate final) = 4 ↔
        tested ∉ stem ∧
          penultimate ≠ tested ∧ final ≠ tested
  | [], penultimate, final => by
      change
        table.mul
            (terminalValuation tested penultimate)
            (terminalValuation tested final) = 4 ↔
          tested ∉ [] ∧
            penultimate ≠ tested ∧ final ≠ tested
      by_cases penultimateEq : penultimate = tested <;>
        by_cases finalEq : final = tested <;>
        simp [terminalValuation, table,
          Generated.Catalogue.S5_203.table,
          Generated.Catalogue.S5_203.mul,
          penultimateEq, finalEq] <;>
        decide
  | x :: stem, penultimate, final => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      change
        table.mul (terminalValuation tested x)
            (table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final)) = 4 ↔
          tested ∉ x :: stem ∧
            penultimate ≠ tested ∧ final ≠ tested
      by_cases xEq : x = tested
      · subst x
        simp [terminalValuation, terminalHit_ne_absent]
      · simp [terminalValuation, xEq, Ne.symm xEq,
          terminalPass_eq_absent_iff,
          evalTerminalPair_eq_absent_iff tested stem
            penultimate final]

private theorem evalTerminalPair_eq_simple_iff
    (tested : Nat) :
    ∀ stem penultimate final,
      table.semigroup.eval (terminalValuation tested)
          (terminalPairWord stem penultimate final) = 2 ↔
        final = tested ∧
          penultimate ≠ tested ∧ tested ∉ stem
  | [], penultimate, final => by
      change
        table.mul
            (terminalValuation tested penultimate)
            (terminalValuation tested final) = 2 ↔
          final = tested ∧
            penultimate ≠ tested ∧ tested ∉ []
      by_cases penultimateEq : penultimate = tested <;>
        by_cases finalEq : final = tested <;>
        simp [terminalValuation, table,
          Generated.Catalogue.S5_203.table,
          Generated.Catalogue.S5_203.mul,
          penultimateEq, finalEq] <;>
        decide
  | x :: stem, penultimate, final => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      change
        table.mul (terminalValuation tested x)
            (table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final)) = 2 ↔
          final = tested ∧
            penultimate ≠ tested ∧ tested ∉ x :: stem
      by_cases xEq : x = tested
      · subst x
        simp [terminalValuation, terminalHit_ne_simple]
      · have restNe :=
          evalTerminalPair_ne_singleton tested stem
            penultimate final
        simp [terminalValuation, xEq, Ne.symm xEq,
          terminalPass_eq_simple_iff, restNe,
          evalTerminalPair_eq_simple_iff tested stem
            penultimate final]

private theorem evalTerminalPair_eq_doubleton_iff
    (tested : Nat) :
    ∀ stem penultimate final,
      table.semigroup.eval (terminalValuation tested)
          (terminalPairWord stem penultimate final) = 1 ↔
        final = tested ∧
          penultimate = tested ∧ tested ∉ stem
  | [], penultimate, final => by
      change
        table.mul
            (terminalValuation tested penultimate)
            (terminalValuation tested final) = 1 ↔
          final = tested ∧
            penultimate = tested ∧ tested ∉ []
      by_cases penultimateEq : penultimate = tested <;>
        by_cases finalEq : final = tested <;>
        simp [terminalValuation, table,
          Generated.Catalogue.S5_203.table,
          Generated.Catalogue.S5_203.mul,
          penultimateEq, finalEq] <;>
        decide
  | x :: stem, penultimate, final => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      change
        table.mul (terminalValuation tested x)
            (table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final)) = 1 ↔
          final = tested ∧
            penultimate = tested ∧ tested ∉ x :: stem
      by_cases xEq : x = tested
      · subst x
        have restNe :=
          evalTerminalPair_ne_singleton tested stem
            penultimate final
        simp [terminalValuation, terminalHit_eq_doubleton_iff,
          restNe]
      · simp [terminalValuation, xEq, Ne.symm xEq,
          terminalPass_eq_doubleton_iff,
          evalTerminalPair_eq_doubleton_iff tested stem
            penultimate final]

private theorem singletonMarker_mul_ne_marker (value : Fin 5) :
    table.mul 3 value ≠ 3 := by
  decide +revert

private theorem evalSingletonPrefix_eq_marker_iff :
    ∀ stem final,
      table.semigroup.eval singletonValuation
          (wordOfPrefixFinal stem final) = 3 ↔
        stem = []
  | [], final => by
      simp [wordOfPrefixFinal, singletonValuation]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      change
        table.mul (singletonValuation x)
            (table.semigroup.eval singletonValuation
              (wordOfPrefixFinal xs final)) = 3 ↔
          x :: xs = []
      simp [singletonValuation, singletonMarker_mul_ne_marker]

/-- Exact absence certificate under the terminal-state valuation. -/
theorem evalTerminal_eq_absent_iff
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (terminalValuation tested) word = 4 ↔
      tested ∉ word.toList := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      by_cases finalEq : final = tested
      · subst final
        simp [TerminalSplit.renderWord, terminalValuation]
      · have testedNe : tested ≠ final := Ne.symm finalEq
        simp [TerminalSplit.renderWord, terminalValuation,
          finalEq, testedNe]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      change
        table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final) = 4 ↔
          tested ∉ (terminalPairWord stem penultimate final).toList
      simpa [toList_terminalPairWord, eq_comm] using
        evalTerminalPair_eq_absent_iff tested stem
          penultimate final

/-- Exact singleton certificate under the constant element-four valuation. -/
theorem evalSingleton_eq_marker_iff (word : Word Nat) :
    table.semigroup.eval singletonValuation word = 3 ↔
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord word := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SemigroupBasis.CoRoots.S5_83.IsSingletonWord
      rw [splitEq, ← reconstruct]
      simp [TerminalSplit.renderWord, singletonValuation]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SemigroupBasis.CoRoots.S5_83.IsSingletonWord
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, terminalPairWord] using
        evalSingletonPrefix_eq_marker_iff
          (stem ++ [penultimate]) final

/-- Outputs three and two are exactly the singleton and nonsingleton forms of
a globally unique final variable. -/
theorem evalTerminal_uniqueFinal_iff
    (tested : Nat) (word : Word Nat) :
      (table.semigroup.eval (terminalValuation tested) word = 3 ∨
        table.semigroup.eval (terminalValuation tested) word = 2) ↔
      SemigroupBasis.CoRoots.S5_83.UniqueFinal word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SemigroupBasis.CoRoots.S5_83.UniqueFinal
      rw [splitEq, ← reconstruct]
      by_cases finalEq : final = tested <;>
        simp [TerminalSplit.renderWord, terminalValuation, finalEq]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SemigroupBasis.CoRoots.S5_83.UniqueFinal
      rw [splitEq, ← reconstruct]
      change
        (table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final) = 3 ∨
            table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final) = 2) ↔
          final = tested ∧
            final ≠ penultimate ∧ final ∉ stem
      have notSingleton :
          table.semigroup.eval (terminalValuation tested)
              (terminalPairWord stem penultimate final) ≠ 3 :=
        evalTerminalPair_ne_singleton tested stem
          penultimate final
      have simple :
          table.semigroup.eval (terminalValuation tested)
                (terminalPairWord stem penultimate final) = 2 ↔
            final = tested ∧
              final ≠ penultimate ∧ final ∉ stem := by
        constructor
        · intro evaluated
          rcases
              (evalTerminalPair_eq_simple_iff tested stem
                penultimate final).mp evaluated with
            ⟨finalEq, penultimateNe, absent⟩
          subst tested
          exact ⟨rfl, Ne.symm penultimateNe, absent⟩
        · rintro ⟨finalEq, finalNe, absent⟩
          subst tested
          exact
            (evalTerminalPair_eq_simple_iff final stem
              penultimate final).mpr
              ⟨rfl, Ne.symm finalNe, absent⟩
      constructor
      · intro evaluated
        rcases evaluated with singleton | simpleValue
        · exact False.elim (notSingleton singleton)
        · exact simple.mp simpleValue
      · intro signature
        exact Or.inr (simple.mpr signature)

/-- Output two in one-based terminology is exactly the terminal-doubleton
state. -/
theorem evalTerminal_eq_doubleton_iff
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (terminalValuation tested) word = 1 ↔
      TerminalDoubleton word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold TerminalDoubleton
      rw [splitEq, ← reconstruct]
      by_cases finalEq : final = tested <;>
        simp [TerminalSplit.renderWord, terminalValuation, finalEq]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold TerminalDoubleton
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, terminalPairWord,
        and_left_comm, and_comm, and_assoc] using
        evalTerminalPair_eq_doubleton_iff tested stem
          penultimate final

private def pairSignal
    (stem : List Nat) (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat) : Prop :=
  candidateFinal ≠ candidatePenultimate ∧
    actualFinal = candidateFinal ∧
    (actualPenultimate = candidatePenultimate ∨
      actualPenultimate = candidateFinal) ∧
    candidatePenultimate ∉ stem ∧
    candidateFinal ∉ stem

private theorem pairCandidate_eq_signal_iff (value : Fin 5) :
    table.mul 2 value = 1 ↔ value = 3 := by
  decide +revert

private theorem pairFinal_eq_signal_iff (value : Fin 5) :
    table.mul 3 value = 1 ↔ value = 3 := by
  decide +revert

private theorem pairDefault_eq_signal_iff (value : Fin 5) :
    table.mul 4 value = 1 ↔ value = 1 := by
  decide +revert

private theorem evalPair_ne_singleton
    (candidatePenultimate candidateFinal
      actualPenultimate actualFinal : Nat) :
    ∀ stem,
      table.semigroup.eval
          (pairValuation candidatePenultimate candidateFinal)
          (terminalPairWord stem actualPenultimate actualFinal) ≠ 3
  | [] => by
      change
        table.mul
            (pairValuation candidatePenultimate candidateFinal
              actualPenultimate)
            (pairValuation candidatePenultimate candidateFinal
              actualFinal) ≠ 3
      exact mul_ne_singleton _ _
  | x :: stem => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_singleton _ _

private theorem evalPairPrefix_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) :
    ∀ stem actualPenultimate actualFinal,
      table.semigroup.eval
          (pairValuation candidatePenultimate candidateFinal)
          (terminalPairWord stem actualPenultimate actualFinal) = 1 ↔
        pairSignal stem actualPenultimate actualFinal
          candidatePenultimate candidateFinal
  | [], actualPenultimate, actualFinal => by
      change
        table.mul
            (pairValuation candidatePenultimate candidateFinal
              actualPenultimate)
            (pairValuation candidatePenultimate candidateFinal
              actualFinal) = 1 ↔
          pairSignal [] actualPenultimate actualFinal
            candidatePenultimate candidateFinal
      by_cases penEqCandidate :
          actualPenultimate = candidatePenultimate <;>
        by_cases penEqFinal :
          actualPenultimate = candidateFinal <;>
        by_cases finalEqCandidate :
          actualFinal = candidatePenultimate <;>
        by_cases finalEqFinal :
          actualFinal = candidateFinal <;>
        by_cases candidatesEqual :
          candidatePenultimate = candidateFinal <;>
        simp [pairValuation, pairSignal, table,
          Generated.Catalogue.S5_203.table,
          Generated.Catalogue.S5_203.mul, penEqCandidate,
          penEqFinal, finalEqCandidate, finalEqFinal,
          candidatesEqual, eq_comm] at * <;>
        omega
  | x :: stem, actualPenultimate, actualFinal => by
      rw [terminalPairWord_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      change
        table.mul
            (pairValuation candidatePenultimate candidateFinal x)
            (table.semigroup.eval
              (pairValuation candidatePenultimate candidateFinal)
              (terminalPairWord stem actualPenultimate actualFinal)) = 1 ↔
          pairSignal (x :: stem) actualPenultimate actualFinal
            candidatePenultimate candidateFinal
      by_cases xEqCandidate : x = candidatePenultimate
      · have restNe :=
          evalPair_ne_singleton candidatePenultimate candidateFinal
            actualPenultimate actualFinal stem
        simp [pairValuation, pairSignal, xEqCandidate,
          pairCandidate_eq_signal_iff, restNe]
      · by_cases xEqFinal : x = candidateFinal
        · have restNe :=
            evalPair_ne_singleton candidatePenultimate candidateFinal
              actualPenultimate actualFinal stem
          have candidatesNe :
              candidateFinal ≠ candidatePenultimate := by
            intro equal
            exact xEqCandidate (xEqFinal.trans equal)
          simp [pairValuation, pairSignal, xEqCandidate, xEqFinal,
            Ne.symm xEqCandidate, candidatesNe,
            pairFinal_eq_signal_iff, restNe]
        · simp [pairValuation, pairSignal, xEqCandidate, xEqFinal,
            Ne.symm xEqCandidate, Ne.symm xEqFinal,
            pairDefault_eq_signal_iff,
            evalPairPrefix_eq_signal_iff candidatePenultimate
              candidateFinal stem actualPenultimate actualFinal]

/-- Under the globally unique-final hypothesis, output two in one-based
terminology is exactly the globally unique terminal pair. The hypothesis
excludes the terminal-doubleton false positive of the same valuation. -/
theorem evalPair_eq_signal_iff_of_uniqueFinal
    (candidatePenultimate candidateFinal : Nat)
    (word : Word Nat)
    (unique :
      SemigroupBasis.CoRoots.S5_83.UniqueFinal word candidateFinal) :
    table.semigroup.eval
        (pairValuation candidatePenultimate candidateFinal) word = 1 ↔
      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair word
        candidatePenultimate candidateFinal := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
      rw [splitEq, ← reconstruct]
      by_cases finalEqCandidate :
          final = candidatePenultimate <;>
        by_cases finalEqFinal : final = candidateFinal <;>
        by_cases candidatesEqual :
          candidatePenultimate = candidateFinal <;>
        simp [TerminalSplit.renderWord, pairValuation,
          finalEqCandidate, finalEqFinal, candidatesEqual,
          eq_comm] <;>
        decide
  | pair stem actualPenultimate actualFinal =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      have uniqueParts :
          actualFinal = candidateFinal ∧
            actualFinal ≠ actualPenultimate ∧
            actualFinal ∉ stem := by
        simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
          splitEq] using unique
      have actualFinalEq : actualFinal = candidateFinal :=
        uniqueParts.1
      subst actualFinal
      have actualPenultimateNe :
          actualPenultimate ≠ candidateFinal :=
        Ne.symm uniqueParts.2.1
      unfold SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, pairSignal,
        uniqueParts.2.1, uniqueParts.2.2, actualPenultimateNe,
        and_left_comm, and_comm, and_assoc] using
        evalPairPrefix_eq_signal_iff
          candidatePenultimate candidateFinal
          stem actualPenultimate candidateFinal

end DirectCompletenessArchitecture

/-- Every identity valid in the exact catalogue table preserves support, the
singleton stratum, globally unique finals, terminal doubletons, and the
conditioned globally unique terminal pair. -/
theorem valid_sameSupportTerminalStateSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSupportTerminalStateSignature
      identity.lhs identity.rhs := by
  have support :
      SemigroupBasis.CoRoots.S5_83.SameSupport
        identity.lhs identity.rhs := by
    intro tested
    have evaluated := valid (terminalValuation tested)
    have absent :
        tested ∉ identity.lhs.toList ↔
          tested ∉ identity.rhs.toList := by
      calc
        tested ∉ identity.lhs.toList ↔
            table.semigroup.eval
                (terminalValuation tested) identity.lhs = 4 :=
          (evalTerminal_eq_absent_iff tested identity.lhs).symm
        _ ↔
            table.semigroup.eval
                (terminalValuation tested) identity.rhs = 4 := by
          rw [evaluated]
        _ ↔ tested ∉ identity.rhs.toList :=
          evalTerminal_eq_absent_iff tested identity.rhs
    constructor
    · intro leftMember
      apply Decidable.byContradiction
      intro rightAbsent
      exact (absent.mpr rightAbsent) leftMember
    · intro rightMember
      apply Decidable.byContradiction
      intro leftAbsent
      exact (absent.mp leftAbsent) rightMember
  have singleton :
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.lhs ↔
        SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.rhs := by
    have evaluated := valid singletonValuation
    calc
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.lhs ↔
          table.semigroup.eval singletonValuation identity.lhs = 3 :=
        (evalSingleton_eq_marker_iff identity.lhs).symm
      _ ↔
          table.semigroup.eval singletonValuation identity.rhs = 3 := by
        rw [evaluated]
      _ ↔ SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.rhs :=
        evalSingleton_eq_marker_iff identity.rhs
  have uniqueFinal :
      ∀ tested,
        SemigroupBasis.CoRoots.S5_83.UniqueFinal identity.lhs tested ↔
          SemigroupBasis.CoRoots.S5_83.UniqueFinal identity.rhs tested := by
    intro tested
    have evaluated := valid (terminalValuation tested)
    calc
      SemigroupBasis.CoRoots.S5_83.UniqueFinal identity.lhs tested ↔
          (table.semigroup.eval
                (terminalValuation tested) identity.lhs = 3 ∨
            table.semigroup.eval
                (terminalValuation tested) identity.lhs = 2) :=
        (evalTerminal_uniqueFinal_iff tested identity.lhs).symm
      _ ↔
          (table.semigroup.eval
                (terminalValuation tested) identity.rhs = 3 ∨
            table.semigroup.eval
                (terminalValuation tested) identity.rhs = 2) := by
        rw [evaluated]
      _ ↔ SemigroupBasis.CoRoots.S5_83.UniqueFinal identity.rhs tested :=
        evalTerminal_uniqueFinal_iff tested identity.rhs
  have terminalDoubleton :
      ∀ tested,
        TerminalDoubleton identity.lhs tested ↔
          TerminalDoubleton identity.rhs tested := by
    intro tested
    have evaluated := valid (terminalValuation tested)
    calc
      TerminalDoubleton identity.lhs tested ↔
          table.semigroup.eval
              (terminalValuation tested) identity.lhs = 1 :=
        (evalTerminal_eq_doubleton_iff tested identity.lhs).symm
      _ ↔
          table.semigroup.eval
              (terminalValuation tested) identity.rhs = 1 := by
        rw [evaluated]
      _ ↔ TerminalDoubleton identity.rhs tested :=
        evalTerminal_eq_doubleton_iff tested identity.rhs
  refine ⟨support, singleton, uniqueFinal, terminalDoubleton, ?_⟩
  intro penultimate final leftUnique
  have rightUnique :
      SemigroupBasis.CoRoots.S5_83.UniqueFinal identity.rhs final :=
    (uniqueFinal final).mp leftUnique
  have evaluated := valid (pairValuation penultimate final)
  calc
    SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
        identity.lhs penultimate final ↔
        table.semigroup.eval
            (pairValuation penultimate final) identity.lhs = 1 :=
      (evalPair_eq_signal_iff_of_uniqueFinal
        penultimate final identity.lhs leftUnique).symm
    _ ↔
        table.semigroup.eval
            (pairValuation penultimate final) identity.rhs = 1 := by
      rw [evaluated]
    _ ↔ SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
      identity.rhs penultimate final :=
      evalPair_eq_signal_iff_of_uniqueFinal
        penultimate final identity.rhs rightUnique

set_option maxRecDepth 100000 in
/-- Every formal consequence of the displayed basis preserves the concrete
terminal-state signature. -/
theorem derives_sameSupportTerminalStateSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameSupportTerminalStateSignature left right :=
  valid_sameSupportTerminalStateSignature ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

/-- Every displayed law preserves the exact signature after arbitrary
simultaneous nonempty-word substitution. -/
theorem basisLaw_bind_sameSupportTerminalStateSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    SameSupportTerminalStateSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameSupportTerminalStateSignature <|
    Derives.subst
      (Derives.fromBasis (basis := basis) member) substitution

end SemigroupBasis.CoRoots.S5_203
