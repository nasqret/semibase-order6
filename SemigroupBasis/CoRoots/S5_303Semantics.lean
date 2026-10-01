import SemigroupBasis.CoRoots.S5_303Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part03

namespace SemigroupBasis.CoRoots.S5_303

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

def supportSeparator (tested : Nat) : Nat → Fin 5 :=
  fun x => if x = tested then 2 else 3

def singletonSeparator : Nat → Fin 5 :=
  fun _ => 1

def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun x => if x = tested then 4 else 3

def pairSeparator (penultimate final : Nat) : Nat → Fin 5 :=
  fun x =>
    if x = final then 1 else
      if x = penultimate then 4 else 3

private theorem pairSeparator_ne_signal
    (penultimate final value : Nat) :
    pairSeparator penultimate final value ≠ (2 : Fin 5) := by
  unfold pairSeparator
  split
  · decide
  · split <;> decide

private def pairSignature
    (stem : List Nat) (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat) : Prop :=
  actualPenultimate = candidatePenultimate ∧
    actualFinal = candidateFinal ∧
    candidateFinal ≠ candidatePenultimate ∧
    candidateFinal ∉ stem

private theorem pairSignature_cons_iff
    (x : Nat) (stem : List Nat)
    (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat)
    (xNeFinal : x ≠ candidateFinal) :
    pairSignature (x :: stem) actualPenultimate actualFinal
        candidatePenultimate candidateFinal ↔
      pairSignature stem actualPenultimate actualFinal
        candidatePenultimate candidateFinal := by
  constructor
  · rintro ⟨penultimateEq, finalEq, candidatesDifferent, finalAbsent⟩
    exact ⟨penultimateEq, finalEq, candidatesDifferent,
      fun member => finalAbsent (List.mem_cons_of_mem x member)⟩
  · rintro ⟨penultimateEq, finalEq, candidatesDifferent, finalAbsent⟩
    exact ⟨penultimateEq, finalEq, candidatesDifferent,
      by simpa [List.mem_cons, Ne.symm xNeFinal] using finalAbsent⟩

@[simp]
private theorem wordOfTerminalPair_cons
    (x : Nat) (stem : List Nat) (penultimate final : Nat) :
    wordOfTerminalPair (x :: stem) penultimate final =
      Word.singleton x ++
        wordOfTerminalPair stem penultimate final := rfl

@[simp]
private theorem table_semigroup_mul (left right : Fin 5) :
    Generated.Catalogue.S5_303.table.semigroup.mul left right =
      Generated.Catalogue.S5_303.mul left right := rfl

private theorem supportHit_ne_pass (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 2 value ≠ 3 := by
  decide +revert

private theorem supportPass_eq_pass_iff (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 3 value = 3 ↔ value = 3 := by
  decide +revert

private theorem projection_mul_eq_sink (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 1 value = 0 := by
  decide +revert

private theorem finalPass_eq_marker_iff (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 3 value = 4 ↔ value = 4 := by
  decide +revert

private theorem finalMarker_eq_marker_iff (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 4 value = 4 ↔ value = 4 := by
  decide +revert

private theorem pairFinal_ne_signal (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 1 value ≠ 2 := by
  decide +revert

private theorem pairPenultimate_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 4 value = 2 ↔
      value = 1 ∨ value = 2 := by
  decide +revert

private theorem pairDefault_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 3 value = 2 ↔ value = 2 := by
  decide +revert

private theorem mul_ne_terminal (left right : Fin 5) :
    Generated.Catalogue.S5_303.mul left right ≠ 1 := by
  decide +revert

private theorem evalSupportPrefix_eq_pass_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_303.table.semigroup.eval
          (supportSeparator tested)
          (wordOfPrefixFinal stem final) = (3 : Fin 5) ↔
        tested ∉ stem ∧ final ≠ tested
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, supportSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue : supportSeparator tested x = (2 : Fin 5) := by
          simp [supportSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (supportHit_ne_pass _ equality).elim
        · intro absent
          exfalso
          exact absent.1 (by simp [xTested])
      · have headValue : supportSeparator tested x = (3 : Fin 5) := by
          simp [supportSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_303.mul 3
                (Generated.Catalogue.S5_303.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final)) = (3 : Fin 5) ↔
              Generated.Catalogue.S5_303.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final) = (3 : Fin 5) :=
            supportPass_eq_pass_iff _
          _ ↔ tested ∉ xs ∧ final ≠ tested :=
            evalSupportPrefix_eq_pass_iff tested xs final
          _ ↔ tested ∉ x :: xs ∧ final ≠ tested := by
            simp [Ne.symm xTested]

private theorem evalSingletonPrefix_eq_projection_iff :
    ∀ stem final,
      Generated.Catalogue.S5_303.table.semigroup.eval
          singletonSeparator
          (wordOfPrefixFinal stem final) = (1 : Fin 5) ↔
        stem = []
  | [], final => by
      simp [wordOfPrefixFinal, singletonSeparator]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      simp_all [singletonSeparator, projection_mul_eq_sink]

private theorem evalFinalPrefix_eq_marker_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_303.table.semigroup.eval
          (finalSeparator tested)
          (wordOfPrefixFinal stem final) = (4 : Fin 5) ↔
        final = tested
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, finalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue : finalSeparator tested x = (4 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_303.mul 4
                (Generated.Catalogue.S5_303.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (4 : Fin 5) ↔
              Generated.Catalogue.S5_303.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final) = (4 : Fin 5) :=
            finalMarker_eq_marker_iff _
          _ ↔ final = tested :=
            evalFinalPrefix_eq_marker_iff tested xs final
      · have headValue : finalSeparator tested x = (3 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_303.mul 3
                (Generated.Catalogue.S5_303.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (4 : Fin 5) ↔
              Generated.Catalogue.S5_303.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final) = (4 : Fin 5) :=
            finalPass_eq_marker_iff _
          _ ↔ final = tested :=
            evalFinalPrefix_eq_marker_iff tested xs final

private theorem evalPair_ne_terminal
    (candidatePenultimate candidateFinal
      actualPenultimate actualFinal : Nat) :
    ∀ stem,
      Generated.Catalogue.S5_303.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem
            actualPenultimate actualFinal) ≠ (1 : Fin 5)
  | [] => by
      change
        Generated.Catalogue.S5_303.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal
              actualFinal) ≠ 1
      exact mul_ne_terminal _ _
  | x :: xs => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_terminal _ _

private theorem evalPairPrefix_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) :
    ∀ stem actualPenultimate actualFinal,
      Generated.Catalogue.S5_303.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem
            actualPenultimate actualFinal) = (2 : Fin 5) ↔
        pairSignature stem actualPenultimate actualFinal
          candidatePenultimate candidateFinal
  | [], actualPenultimate, actualFinal => by
      change
        Generated.Catalogue.S5_303.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal
              actualFinal) = 2 ↔
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
          Generated.Catalogue.S5_303.mul, penEqCandidate, penEqFinal,
          finalEqCandidate, finalEqFinal, eq_comm]
  | x :: xs, actualPenultimate, actualFinal => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xEqFinal : x = candidateFinal
      · have headValue :
            pairSeparator candidatePenultimate candidateFinal x =
              (1 : Fin 5) := by
          simp [pairSeparator, xEqFinal]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (pairFinal_ne_signal _ equality).elim
        · rintro ⟨_, _, _, finalAbsent⟩
          exfalso
          apply finalAbsent
          simp [xEqFinal]
      · by_cases xEqPenultimate : x = candidatePenultimate
        · have penultimateNeFinal :
              candidatePenultimate ≠ candidateFinal := by
            intro equality
            exact xEqFinal (xEqPenultimate.trans equality)
          have restNe :=
            evalPair_ne_terminal
              candidatePenultimate candidateFinal
              actualPenultimate actualFinal xs
          have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (4 : Fin 5) := by
            rw [xEqPenultimate]
            simp [pairSeparator, penultimateNeFinal]
          rw [headValue, table_semigroup_mul]
          calc
            Generated.Catalogue.S5_303.mul 4
                  (Generated.Catalogue.S5_303.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal)) =
                (2 : Fin 5) ↔
              Generated.Catalogue.S5_303.table.semigroup.eval
                      (pairSeparator candidatePenultimate candidateFinal)
                      (wordOfTerminalPair xs actualPenultimate actualFinal) =
                  (1 : Fin 5) ∨
                Generated.Catalogue.S5_303.table.semigroup.eval
                      (pairSeparator candidatePenultimate candidateFinal)
                      (wordOfTerminalPair xs actualPenultimate actualFinal) =
                  (2 : Fin 5) := pairPenultimate_eq_signal_iff _
            _ ↔ Generated.Catalogue.S5_303.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal) =
                (2 : Fin 5) := by
              simp [restNe]
            _ ↔ pairSignature xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal
            _ ↔ pairSignature (x :: xs) actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              (pairSignature_cons_iff x xs actualPenultimate actualFinal
                candidatePenultimate candidateFinal xEqFinal).symm
        · have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (3 : Fin 5) := by
            simp [pairSeparator, xEqFinal, xEqPenultimate]
          rw [headValue, table_semigroup_mul]
          calc
            Generated.Catalogue.S5_303.mul 3
                  (Generated.Catalogue.S5_303.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal)) =
                (2 : Fin 5) ↔
              Generated.Catalogue.S5_303.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal) =
                (2 : Fin 5) := pairDefault_eq_signal_iff _
            _ ↔ pairSignature xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal
            _ ↔ pairSignature (x :: xs) actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              (pairSignature_cons_iff x xs actualPenultimate actualFinal
                candidatePenultimate candidateFinal xEqFinal).symm

/-- Exact support-absence certificate under the one-based assignment
`tested=3`, `default=4`. -/
theorem evalSupport_eq_pass_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_303.table.semigroup.eval
        (supportSeparator tested) word = (3 : Fin 5) ↔
      tested ∉ word.toList := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      by_cases finalTested : final = tested
      · simp [TerminalSplit.renderWord, supportSeparator, finalTested]
      · simp [TerminalSplit.renderWord, supportSeparator, finalTested,
          Ne.symm finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      rw [← reconstruct]
      simp only [TerminalSplit.renderWord]
      rw [evalSupportPrefix_eq_pass_iff tested
        (stem ++ [penultimate]) final]
      constructor
      · rintro ⟨prefixAbsent, finalNe⟩ wholeMember
        rw [toList_wordOfPrefixFinal, List.mem_append] at wholeMember
        rcases wholeMember with prefixMember | finalMember
        · exact prefixAbsent prefixMember
        · have finalEq : tested = final := by
            simpa using finalMember
          exact finalNe finalEq.symm
      · intro wholeAbsent
        constructor
        · intro prefixMember
          apply wholeAbsent
          rw [toList_wordOfPrefixFinal, List.mem_append]
          exact Or.inl prefixMember
        · intro finalEq
          subst final
          apply wholeAbsent
          rw [toList_wordOfPrefixFinal, List.mem_append]
          exact Or.inr (by simp)

/-- Exact singleton certificate under the constant one-based value `2`. -/
theorem evalSingleton_eq_projection_iff (word : Word Nat) :
    Generated.Catalogue.S5_303.table.semigroup.eval
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

/-- Exact literal-final certificate from the right-zero pair of one-based
states `4` and `5`. -/
theorem evalFinal_eq_marker_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_303.table.semigroup.eval
        (finalSeparator tested) word = (4 : Fin 5) ↔
      FinalLetter word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold FinalLetter
      rw [splitEq, ← reconstruct]
      by_cases finalTested : final = tested <;>
        simp [TerminalSplit.renderWord, finalSeparator, finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold FinalLetter
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair] using
        evalFinalPrefix_eq_marker_iff tested
          (stem ++ [penultimate]) final

/-- Exact unique-final ordered-pair certificate under the one-based
assignment `p=5`, `t=2`, and every other variable `4`. -/
theorem evalPair_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat)
    (word : Word Nat) :
    Generated.Catalogue.S5_303.table.semigroup.eval
        (pairSeparator candidatePenultimate candidateFinal) word =
          (2 : Fin 5) ↔
      UniqueFinalPair word
        candidatePenultimate candidateFinal := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinalPair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord] using
        pairSeparator_ne_signal candidatePenultimate candidateFinal final
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinalPair
      rw [splitEq, ← reconstruct]
      simp only [TerminalSplit.renderWord]
      have evaluated := evalPairPrefix_eq_signal_iff
          candidatePenultimate candidateFinal
          stem penultimate final
      simp only [wordOfTerminalPair] at evaluated
      rw [evaluated]
      unfold pairSignature
      constructor
      · rintro ⟨penultimateEq, finalEq, different, absent⟩
        refine ⟨penultimateEq, finalEq, ?_, ?_⟩
        · simpa only [penultimateEq, finalEq] using different
        · simpa only [finalEq] using absent
      · rintro ⟨penultimateEq, finalEq, different, absent⟩
        refine ⟨penultimateEq, finalEq, ?_, ?_⟩
        · simpa only [penultimateEq, finalEq] using different
        · simpa only [finalEq] using absent

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_303.table.semigroup) :
    SameSupport identity.lhs identity.rhs := by
  intro tested
  have evaluated := valid (supportSeparator tested)
  have absent :
      tested ∉ identity.lhs.toList ↔
        tested ∉ identity.rhs.toList := by
    calc
      tested ∉ identity.lhs.toList ↔
          Generated.Catalogue.S5_303.table.semigroup.eval
              (supportSeparator tested) identity.lhs = (3 : Fin 5) :=
        (evalSupport_eq_pass_iff tested identity.lhs).symm
      _ ↔
          Generated.Catalogue.S5_303.table.semigroup.eval
              (supportSeparator tested) identity.rhs = (3 : Fin 5) := by
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
        Generated.Catalogue.S5_303.table.semigroup) :
    IsSingletonWord identity.lhs ↔
      IsSingletonWord identity.rhs := by
  have evaluated := valid singletonSeparator
  calc
    IsSingletonWord identity.lhs ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            singletonSeparator identity.lhs = (1 : Fin 5) :=
      (evalSingleton_eq_projection_iff identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            singletonSeparator identity.rhs = (1 : Fin 5) := by
      rw [evaluated]
    _ ↔ IsSingletonWord identity.rhs :=
      evalSingleton_eq_projection_iff identity.rhs

theorem valid_finalLetter
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_303.table.semigroup) :
    ∀ tested,
      FinalLetter identity.lhs tested ↔
        FinalLetter identity.rhs tested := by
  intro tested
  have evaluated := valid (finalSeparator tested)
  calc
    FinalLetter identity.lhs tested ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            (finalSeparator tested) identity.lhs = (4 : Fin 5) :=
      (evalFinal_eq_marker_iff tested identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            (finalSeparator tested) identity.rhs = (4 : Fin 5) := by
      rw [evaluated]
    _ ↔ FinalLetter identity.rhs tested :=
      evalFinal_eq_marker_iff tested identity.rhs

theorem valid_uniqueFinalPair
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_303.table.semigroup) :
    ∀ penultimate final,
      UniqueFinalPair identity.lhs penultimate final ↔
        UniqueFinalPair identity.rhs penultimate final := by
  intro penultimate final
  have evaluated := valid (pairSeparator penultimate final)
  calc
    UniqueFinalPair identity.lhs penultimate final ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            (pairSeparator penultimate final) identity.lhs = (2 : Fin 5) :=
      (evalPair_eq_signal_iff
        penultimate final identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_303.table.semigroup.eval
            (pairSeparator penultimate final) identity.rhs = (2 : Fin 5) := by
      rw [evaluated]
    _ ↔ UniqueFinalPair identity.rhs penultimate final :=
      evalPair_eq_signal_iff penultimate final identity.rhs

theorem valid_signature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_303.table.semigroup) :
    SameContentEndpointSignature identity.lhs identity.rhs :=
  ⟨valid_support identity valid,
    valid_singleton identity valid,
    valid_finalLetter identity valid,
    valid_uniqueFinalPair identity valid⟩

/-- The two one-based pass states form a right-zero pair. -/
theorem passStates_certificate (left right : Fin 2) :
    Generated.Catalogue.S5_303.mul
        (if left = 0 then 3 else 4)
        (if right = 0 then 3 else 4) =
      (if right = 0 then 3 else 4) := by
  revert left right
  decide

/-- One-based state `3` collapses every right factor. -/
theorem contentCollapse_certificate (value : Fin 5) :
    Generated.Catalogue.S5_303.mul 2 value = 0 := by
  revert value
  decide

end SemigroupBasis.CoRoots.S5_303
