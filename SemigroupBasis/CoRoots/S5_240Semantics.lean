import SemigroupBasis.CoRoots.S5_240Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part02

namespace SemigroupBasis.CoRoots.S5_240

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

def supportFinalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun x => if x = tested then 2 else 3

def singletonSeparator : Nat → Fin 5 :=
  fun _ => 1

def pairSeparator (penultimate final : Nat) : Nat → Fin 5 :=
  fun x => if x = penultimate then 2 else if x = final then 4 else 3

private theorem pairSeparator_ne_signal
    (penultimate final value : Nat) :
    pairSeparator penultimate final value ≠ (1 : Fin 5) := by
  unfold pairSeparator
  split
  · decide
  · split <;> decide

@[simp]
private theorem wordOfTerminalPair_cons
    (x : Nat) (stem : List Nat) (penultimate final : Nat) :
    wordOfTerminalPair (x :: stem) penultimate final =
      Word.singleton x ++
        wordOfTerminalPair stem penultimate final := rfl

@[simp]
private theorem table_semigroup_mul (left right : Fin 5) :
    Generated.Catalogue.S5_240.table.semigroup.mul left right =
      Generated.Catalogue.S5_240.mul left right := rfl

private theorem supportHit_ne_pass (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 2 value ≠ 3 := by
  decide +revert

private theorem supportPass_eq_pass_iff (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 3 value = 3 ↔
      value = 3 ∨ value = 4 := by
  decide +revert

private theorem finalMarker_ne_marker (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 2 value ≠ 2 := by
  decide +revert

private theorem finalPass_eq_marker_iff (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 3 value = 2 ↔ value = 2 := by
  decide +revert

private theorem projection_mul_eq_sink (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 1 value = 0 := by
  decide +revert

private theorem pairMarker_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 2 value = 1 ↔ value = 4 := by
  decide +revert

private theorem pairDefault_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 3 value = 1 ↔ value = 1 := by
  decide +revert

private theorem pairFinal_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_240.mul 4 value = 1 ↔ value = 1 := by
  decide +revert

private theorem mul_ne_four (left right : Fin 5) :
    Generated.Catalogue.S5_240.mul left right ≠ 4 := by
  decide +revert

private theorem evalSupportPrefix_ne_four (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_240.table.semigroup.eval
          (supportFinalSeparator tested)
          (wordOfPrefixFinal stem final) ≠ (4 : Fin 5)
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, supportFinalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_four _ _

private theorem evalSupportPrefix_eq_pass_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_240.table.semigroup.eval
          (supportFinalSeparator tested)
          (wordOfPrefixFinal stem final) = (3 : Fin 5) ↔
        tested ∉ stem ∧ final ≠ tested
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, supportFinalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue :
            supportFinalSeparator tested x = (2 : Fin 5) := by
          simp [supportFinalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (supportHit_ne_pass _ equality).elim
        · intro absent
          exfalso
          exact absent.1 (by simp [xTested])
      · have restNe := evalSupportPrefix_ne_four tested xs final
        have headValue :
            supportFinalSeparator tested x = (3 : Fin 5) := by
          simp [supportFinalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_240.mul 3
                (Generated.Catalogue.S5_240.table.semigroup.eval
                  (supportFinalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (3 : Fin 5) ↔
              Generated.Catalogue.S5_240.table.semigroup.eval
                    (supportFinalSeparator tested)
                    (wordOfPrefixFinal xs final) = (3 : Fin 5) ∨
                Generated.Catalogue.S5_240.table.semigroup.eval
                    (supportFinalSeparator tested)
                    (wordOfPrefixFinal xs final) = (4 : Fin 5) :=
            supportPass_eq_pass_iff _
          _ ↔ Generated.Catalogue.S5_240.table.semigroup.eval
                  (supportFinalSeparator tested)
                  (wordOfPrefixFinal xs final) = (3 : Fin 5) := by
            simp [restNe]
          _ ↔ tested ∉ xs ∧ final ≠ tested :=
            evalSupportPrefix_eq_pass_iff tested xs final
          _ ↔ tested ∉ x :: xs ∧ final ≠ tested := by
            simp [Ne.symm xTested]

private theorem evalFinalPrefix_eq_marker_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_240.table.semigroup.eval
          (supportFinalSeparator tested)
          (wordOfPrefixFinal stem final) = (2 : Fin 5) ↔
        final = tested ∧ tested ∉ stem
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, supportFinalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue :
            supportFinalSeparator tested x = (2 : Fin 5) := by
          simp [supportFinalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (finalMarker_ne_marker _ equality).elim
        · intro condition
          exfalso
          exact condition.2 (by simp [xTested])
      · have headValue :
            supportFinalSeparator tested x = (3 : Fin 5) := by
          simp [supportFinalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_240.mul 3
                (Generated.Catalogue.S5_240.table.semigroup.eval
                  (supportFinalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (2 : Fin 5) ↔
              Generated.Catalogue.S5_240.table.semigroup.eval
                  (supportFinalSeparator tested)
                  (wordOfPrefixFinal xs final) = (2 : Fin 5) :=
            finalPass_eq_marker_iff _
          _ ↔ final = tested ∧ tested ∉ xs :=
            evalFinalPrefix_eq_marker_iff tested xs final
          _ ↔ final = tested ∧ tested ∉ x :: xs := by
            simp [Ne.symm xTested]

private theorem evalSingletonPrefix_eq_projection_iff :
    ∀ stem final,
      Generated.Catalogue.S5_240.table.semigroup.eval
          singletonSeparator
          (wordOfPrefixFinal stem final) = (1 : Fin 5) ↔
        stem = []
  | [], final => by
      simp [wordOfPrefixFinal, singletonSeparator]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      simp_all [singletonSeparator, projection_mul_eq_sink]

private theorem evalPair_ne_final
    (candidatePenultimate candidateFinal actualPenultimate actualFinal : Nat) :
    ∀ stem,
      Generated.Catalogue.S5_240.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem actualPenultimate actualFinal) ≠
        (4 : Fin 5)
  | [] => by
      change
        Generated.Catalogue.S5_240.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal
              actualFinal) ≠ 4
      exact mul_ne_four _ _
  | x :: xs => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_four _ _

private def pairSignature
    (stem : List Nat) (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat) : Prop :=
  actualPenultimate = candidatePenultimate ∧
    actualFinal = candidateFinal ∧
    candidatePenultimate ∉ stem ∧
    candidateFinal ≠ candidatePenultimate

private theorem pairSignature_cons_iff
    (x : Nat) (stem : List Nat)
    (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat)
    (xNeCandidate : x ≠ candidatePenultimate) :
    pairSignature (x :: stem) actualPenultimate actualFinal
        candidatePenultimate candidateFinal ↔
      pairSignature stem actualPenultimate actualFinal
        candidatePenultimate candidateFinal := by
  constructor
  · rintro ⟨penultimateEq, finalEq, candidateAbsent,
      candidatesDifferent⟩
    exact ⟨penultimateEq, finalEq,
      fun member => candidateAbsent (List.mem_cons_of_mem x member),
      candidatesDifferent⟩
  · rintro ⟨penultimateEq, finalEq, candidateAbsent,
      candidatesDifferent⟩
    exact ⟨penultimateEq, finalEq,
      by simpa [List.mem_cons, Ne.symm xNeCandidate] using candidateAbsent,
      candidatesDifferent⟩

private theorem finalCondition_iff
    (tested : Nat) (stem : List Nat) (penultimate final : Nat) :
    (tested = final ∧ tested ∉ stem ∧ tested ≠ penultimate) ↔
      (tested = final ∧ penultimate ≠ final ∧ final ∉ stem) := by
  constructor
  · rintro ⟨equal, absent, different⟩
    subst final
    exact ⟨rfl, Ne.symm different, absent⟩
  · rintro ⟨equal, different, absent⟩
    subst final
    exact ⟨rfl, absent, Ne.symm different⟩

private theorem evalPairPrefix_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) :
    ∀ stem actualPenultimate actualFinal,
      Generated.Catalogue.S5_240.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem
            actualPenultimate actualFinal) = (1 : Fin 5) ↔
        pairSignature stem actualPenultimate actualFinal
          candidatePenultimate candidateFinal
  | [], actualPenultimate, actualFinal => by
      change
        Generated.Catalogue.S5_240.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal
              actualFinal) = 1 ↔
          pairSignature [] actualPenultimate actualFinal
            candidatePenultimate candidateFinal
      by_cases penEqCandidate :
          actualPenultimate = candidatePenultimate <;>
        by_cases penEqFinal :
          actualPenultimate = candidateFinal <;>
        by_cases finalEqCandidate :
          actualFinal = candidatePenultimate <;>
        by_cases finalEqFinal :
          actualFinal = candidateFinal <;>
        simp_all [pairSeparator, pairSignature,
          Generated.Catalogue.S5_240.mul, penEqCandidate, penEqFinal,
          finalEqCandidate, finalEqFinal, eq_comm]
  | x :: xs, actualPenultimate, actualFinal => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xEqCandidate : x = candidatePenultimate
      · have restNe :=
          evalPair_ne_final candidatePenultimate candidateFinal
            actualPenultimate actualFinal xs
        have headValue :
            pairSeparator candidatePenultimate candidateFinal x =
              (2 : Fin 5) := by
          simp [pairSeparator, xEqCandidate]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (restNe ((pairMarker_eq_signal_iff _).mp equality)).elim
        · rintro ⟨_, _, candidateAbsent, _⟩
          exfalso
          apply candidateAbsent
          simp [xEqCandidate]
      · by_cases xEqFinal : x = candidateFinal
        · have finalNeCandidate :
              candidateFinal ≠ candidatePenultimate := by
            intro equality
            exact xEqCandidate (xEqFinal.trans equality)
          have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (4 : Fin 5) := by
            rw [xEqFinal]
            simp [pairSeparator, finalNeCandidate]
          rw [headValue, table_semigroup_mul]
          calc
            Generated.Catalogue.S5_240.mul 4
                  (Generated.Catalogue.S5_240.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal)) =
                (1 : Fin 5) ↔
              Generated.Catalogue.S5_240.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal) =
                (1 : Fin 5) := pairFinal_eq_signal_iff _
            _ ↔ pairSignature xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal
            _ ↔ pairSignature (x :: xs) actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              (pairSignature_cons_iff x xs actualPenultimate actualFinal
                candidatePenultimate candidateFinal xEqCandidate).symm
        · have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (3 : Fin 5) := by
            simp [pairSeparator, xEqCandidate, xEqFinal]
          rw [headValue, table_semigroup_mul]
          calc
            Generated.Catalogue.S5_240.mul 3
                  (Generated.Catalogue.S5_240.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal)) =
                (1 : Fin 5) ↔
              Generated.Catalogue.S5_240.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal) =
                (1 : Fin 5) := pairDefault_eq_signal_iff _
            _ ↔ pairSignature xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal
            _ ↔ pairSignature (x :: xs) actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              (pairSignature_cons_iff x xs actualPenultimate actualFinal
                candidatePenultimate candidateFinal xEqCandidate).symm

/-- Exact absence certificate under the `3/4` one-based assignment. -/
theorem evalSupport_eq_pass_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_240.table.semigroup.eval
        (supportFinalSeparator tested) word = (3 : Fin 5) ↔
      tested ∉ word.toList := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      by_cases finalTested : final = tested
      · simp [TerminalSplit.renderWord, supportFinalSeparator, finalTested]
      · simp [TerminalSplit.renderWord, supportFinalSeparator, finalTested,
          Ne.symm finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        toList_wordOfPrefixFinal, List.mem_append, eq_comm,
        and_assoc] using
        evalSupportPrefix_eq_pass_iff tested
          (stem ++ [penultimate]) final

/-- Exact simple-final certificate under the `3/4` one-based assignment. -/
theorem evalFinal_eq_marker_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_240.table.semigroup.eval
        (supportFinalSeparator tested) word = (2 : Fin 5) ↔
      UniqueFinal word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      by_cases finalTested : final = tested <;>
        simp [TerminalSplit.renderWord, supportFinalSeparator,
          finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        List.mem_append, finalCondition_iff, eq_comm] using
        evalFinalPrefix_eq_marker_iff tested
          (stem ++ [penultimate]) final

/-- Exact singleton certificate under the constant one-based value `2`. -/
theorem evalSingleton_eq_projection_iff (word : Word Nat) :
    Generated.Catalogue.S5_240.table.semigroup.eval
        singletonSeparator word = (1 : Fin 5) ↔
      IsSingletonWord word := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold IsSingletonWord
      rw [splitEq, ← reconstruct]
      simp [TerminalSplit.renderWord, singletonSeparator]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold IsSingletonWord
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair] using
        evalSingletonPrefix_eq_projection_iff
          (stem ++ [penultimate]) final

/-- Exact simple-penultimate pair certificate under the one-based assignment
`p=3`, `t=5`, and every other variable `4`. -/
theorem evalPair_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat)
    (word : Word Nat) :
    Generated.Catalogue.S5_240.table.semigroup.eval
        (pairSeparator candidatePenultimate candidateFinal) word =
          (1 : Fin 5) ↔
      SimplePenultimatePair word
        candidatePenultimate candidateFinal := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SimplePenultimatePair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord] using
        pairSeparator_ne_signal candidatePenultimate candidateFinal final
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold SimplePenultimatePair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, pairSignature] using
        evalPairPrefix_eq_signal_iff
          candidatePenultimate candidateFinal
          stem penultimate final

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_240.table.semigroup) :
    SameSupport identity.lhs identity.rhs := by
  intro tested
  have evaluated := valid (supportFinalSeparator tested)
  have absent :
      tested ∉ identity.lhs.toList ↔
        tested ∉ identity.rhs.toList := by
    calc
      tested ∉ identity.lhs.toList ↔
          Generated.Catalogue.S5_240.table.semigroup.eval
              (supportFinalSeparator tested) identity.lhs = (3 : Fin 5) :=
        (evalSupport_eq_pass_iff tested identity.lhs).symm
      _ ↔
          Generated.Catalogue.S5_240.table.semigroup.eval
              (supportFinalSeparator tested) identity.rhs = (3 : Fin 5) := by
        rw [evaluated]
      _ ↔ tested ∉ identity.rhs.toList :=
        evalSupport_eq_pass_iff tested identity.rhs
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    exact (absent.mpr rightAbsent) leftMember
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    exact (absent.mp leftAbsent) rightMember

theorem valid_singleton
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_240.table.semigroup) :
    IsSingletonWord identity.lhs ↔
      IsSingletonWord identity.rhs := by
  have evaluated := valid singletonSeparator
  calc
    IsSingletonWord identity.lhs ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            singletonSeparator identity.lhs = (1 : Fin 5) :=
      (evalSingleton_eq_projection_iff identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            singletonSeparator identity.rhs = (1 : Fin 5) := by
      rw [evaluated]
    _ ↔ IsSingletonWord identity.rhs :=
      evalSingleton_eq_projection_iff identity.rhs

theorem valid_uniqueFinal
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_240.table.semigroup) :
    ∀ tested,
      UniqueFinal identity.lhs tested ↔
        UniqueFinal identity.rhs tested := by
  intro tested
  have evaluated := valid (supportFinalSeparator tested)
  calc
    UniqueFinal identity.lhs tested ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            (supportFinalSeparator tested) identity.lhs = (2 : Fin 5) :=
      (evalFinal_eq_marker_iff tested identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            (supportFinalSeparator tested) identity.rhs = (2 : Fin 5) := by
      rw [evaluated]
    _ ↔ UniqueFinal identity.rhs tested :=
      evalFinal_eq_marker_iff tested identity.rhs

theorem valid_simplePenultimatePair
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_240.table.semigroup) :
    ∀ penultimate final,
      SimplePenultimatePair identity.lhs penultimate final ↔
        SimplePenultimatePair identity.rhs penultimate final := by
  intro penultimate final
  have evaluated := valid (pairSeparator penultimate final)
  calc
    SimplePenultimatePair identity.lhs penultimate final ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            (pairSeparator penultimate final) identity.lhs = (1 : Fin 5) :=
      (evalPair_eq_signal_iff
        penultimate final identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_240.table.semigroup.eval
            (pairSeparator penultimate final) identity.rhs = (1 : Fin 5) := by
      rw [evaluated]
    _ ↔
        SimplePenultimatePair identity.rhs penultimate final :=
      evalPair_eq_signal_iff penultimate final identity.rhs

theorem valid_signature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_240.table.semigroup) :
    SameEndpointSuffixSignature identity.lhs identity.rhs :=
  ⟨valid_support identity valid,
    valid_singleton identity valid,
    valid_uniqueFinal identity valid,
    valid_simplePenultimatePair identity valid⟩

end SemigroupBasis.CoRoots.S5_240
