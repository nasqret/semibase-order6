import SemigroupBasis.CoRoots.S5_83Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part01

namespace SemigroupBasis.CoRoots.S5_83Factors

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

def supportSeparator (tested : Nat) : Nat → Fin 5 :=
  fun x => if x = tested then 2 else 4

def singletonSeparator : Nat → Fin 5 :=
  fun _ => 1

def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun x => if x = tested then 3 else 4

def pairSeparator (penultimate final : Nat) : Nat → Fin 5 :=
  fun x => if x = penultimate then 3 else if x = final then 2 else 4

def pairSignature
    (stem : List Nat) (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat) : Prop :=
  actualPenultimate = candidatePenultimate ∧
    actualFinal = candidateFinal ∧
    candidatePenultimate ∉ stem ∧
    candidateFinal ≠ candidatePenultimate ∧
    candidateFinal ∉ stem

private theorem pairSeparator_ne_signal
    (penultimate final value : Nat) :
    pairSeparator penultimate final value ≠ (1 : Fin 5) := by
  unfold pairSeparator
  split
  · decide
  · split <;> decide

private theorem pairSignature_cons_iff
    (x : Nat) (stem : List Nat)
    (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat)
    (xNeCandidate : x ≠ candidatePenultimate)
    (xNeFinal : x ≠ candidateFinal) :
    pairSignature (x :: stem) actualPenultimate actualFinal
        candidatePenultimate candidateFinal ↔
      pairSignature stem actualPenultimate actualFinal
        candidatePenultimate candidateFinal := by
  constructor
  · rintro ⟨penultimateEq, finalEq, candidateAbsent,
      candidatesDifferent, finalAbsent⟩
    exact ⟨penultimateEq, finalEq,
      fun member => candidateAbsent (List.mem_cons_of_mem x member),
      candidatesDifferent,
      fun member => finalAbsent (List.mem_cons_of_mem x member)⟩
  · rintro ⟨penultimateEq, finalEq, candidateAbsent,
      candidatesDifferent, finalAbsent⟩
    exact ⟨penultimateEq, finalEq,
      by simpa [List.mem_cons, Ne.symm xNeCandidate] using candidateAbsent,
      candidatesDifferent,
      by simpa [List.mem_cons, Ne.symm xNeFinal] using finalAbsent⟩

/-- The extra S5_84 pair-separator signal: the penultimate candidate is absent
and the final candidate is the globally unique final variable. -/
def absentPenultimateSignal
    (stem : List Nat) (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat) : Prop :=
  candidatePenultimate ∉ stem ∧
    candidatePenultimate ≠ actualPenultimate ∧
    candidatePenultimate ≠ actualFinal ∧
    actualFinal = candidateFinal ∧
    actualFinal ≠ actualPenultimate ∧
    actualFinal ∉ stem

private theorem absentPenultimateSignal_cons_iff
    (x : Nat) (stem : List Nat)
    (actualPenultimate actualFinal : Nat)
    (candidatePenultimate candidateFinal : Nat)
    (xNeCandidate : x ≠ candidatePenultimate)
    (xNeFinal : x ≠ candidateFinal) :
    absentPenultimateSignal (x :: stem)
        actualPenultimate actualFinal
        candidatePenultimate candidateFinal ↔
      absentPenultimateSignal stem actualPenultimate actualFinal
        candidatePenultimate candidateFinal := by
  constructor
  · rintro ⟨candidateAbsent, candidateNePenultimate,
      candidateNeFinal, finalEq, finalNePenultimate, finalAbsent⟩
    exact ⟨fun member =>
        candidateAbsent (List.mem_cons_of_mem x member),
      candidateNePenultimate, candidateNeFinal, finalEq,
      finalNePenultimate,
      fun member => finalAbsent (List.mem_cons_of_mem x member)⟩
  · rintro ⟨candidateAbsent, candidateNePenultimate,
      candidateNeFinal, finalEq, finalNePenultimate, finalAbsent⟩
    have actualFinalNeX : actualFinal ≠ x := by
      intro actualFinalEqX
      apply xNeFinal
      calc
        x = actualFinal := actualFinalEqX.symm
        _ = candidateFinal := finalEq
    exact ⟨by
        simpa [List.mem_cons, Ne.symm xNeCandidate] using candidateAbsent,
      candidateNePenultimate, candidateNeFinal, finalEq,
      finalNePenultimate,
      by simpa [List.mem_cons, actualFinalNeX] using finalAbsent⟩

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

@[simp]
private theorem wordOfTerminalPair_cons
    (x : Nat) (stem : List Nat) (penultimate final : Nat) :
    wordOfTerminalPair (x :: stem) penultimate final =
      Word.singleton x ++
        wordOfTerminalPair stem penultimate final := rfl

private theorem support_of_absence_equivalence
    {G : Semigroup (Fin 5)}
    (evalSupport :
      ∀ tested word,
        G.eval (supportSeparator tested) word = (4 : Fin 5) ↔
          tested ∉ word.toList)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    SameSupport identity.lhs identity.rhs := by
  intro tested
  have evaluated := valid (supportSeparator tested)
  have absent :
      tested ∉ identity.lhs.toList ↔
        tested ∉ identity.rhs.toList := by
    calc
      tested ∉ identity.lhs.toList ↔
          G.eval (supportSeparator tested) identity.lhs = 4 :=
        (evalSupport tested identity.lhs).symm
      _ ↔ G.eval (supportSeparator tested) identity.rhs = 4 := by
        rw [evaluated]
      _ ↔ tested ∉ identity.rhs.toList :=
        evalSupport tested identity.rhs
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    exact (absent.mpr rightAbsent) leftMember
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    exact (absent.mp leftAbsent) rightMember

private theorem singleton_of_eval_equivalence
    {G : Semigroup (Fin 5)}
    (evalSingleton :
      ∀ word,
        G.eval singletonSeparator word = (1 : Fin 5) ↔
          IsSingletonWord word)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    IsSingletonWord identity.lhs ↔
      IsSingletonWord identity.rhs := by
  have evaluated := valid singletonSeparator
  calc
    IsSingletonWord identity.lhs ↔
        G.eval singletonSeparator identity.lhs = 1 :=
      (evalSingleton identity.lhs).symm
    _ ↔ G.eval singletonSeparator identity.rhs = 1 := by
      rw [evaluated]
    _ ↔ IsSingletonWord identity.rhs :=
      evalSingleton identity.rhs

private theorem uniqueFinal_of_eval_equivalence
    {G : Semigroup (Fin 5)}
    (evalFinal :
      ∀ tested word,
        G.eval (finalSeparator tested) word = (3 : Fin 5) ↔
          UniqueFinal word tested)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G) :
    ∀ tested,
      UniqueFinal identity.lhs tested ↔
        UniqueFinal identity.rhs tested := by
  intro tested
  have evaluated := valid (finalSeparator tested)
  calc
    UniqueFinal identity.lhs tested ↔
        G.eval (finalSeparator tested) identity.lhs = 3 :=
      (evalFinal tested identity.lhs).symm
    _ ↔ G.eval (finalSeparator tested) identity.rhs = 3 := by
      rw [evaluated]
    _ ↔ UniqueFinal identity.rhs tested :=
      evalFinal tested identity.rhs

namespace S5_83

@[simp]
private theorem table_semigroup_mul (left right : Fin 5) :
    Generated.Catalogue.S5_83.table.semigroup.mul left right =
      Generated.Catalogue.S5_83.mul left right := rfl

private theorem supportHit_ne_pass (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 2 value ≠ 4 := by
  decide +revert

private theorem supportPass_eq_pass_iff (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 4 value = 4 ↔ value = 4 := by
  decide +revert

private theorem projection_mul_eq_sink (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 1 value = 0 := by
  decide +revert

private theorem finalMarker_ne_marker (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 3 value ≠ 3 := by
  decide +revert

private theorem finalPass_eq_marker_iff (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 4 value = 3 ↔ value = 3 := by
  decide +revert

private theorem pairMarker_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 3 value = 1 ↔ value = 2 := by
  decide +revert

private theorem pairContent_ne_signal (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 2 value ≠ 1 := by
  decide +revert

private theorem pairPass_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_83.mul 4 value = 1 ↔ value = 1 := by
  decide +revert

private theorem mul_ne_content (left right : Fin 5) :
    Generated.Catalogue.S5_83.mul left right ≠ 2 := by
  decide +revert

private theorem evalSupportPrefix_eq_pass_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_83.table.semigroup.eval
          (supportSeparator tested)
          (wordOfPrefixFinal stem final) = (4 : Fin 5) ↔
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
      · have headValue : supportSeparator tested x = (4 : Fin 5) := by
          simp [supportSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_83.mul 4
                (Generated.Catalogue.S5_83.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final)) = (4 : Fin 5) ↔
              Generated.Catalogue.S5_83.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final) = (4 : Fin 5) :=
            supportPass_eq_pass_iff _
          _ ↔ tested ∉ xs ∧ final ≠ tested :=
            evalSupportPrefix_eq_pass_iff tested xs final
          _ ↔ tested ∉ x :: xs ∧ final ≠ tested := by
            simp [Ne.symm xTested]

private theorem evalSingletonPrefix_eq_projection_iff :
    ∀ stem final,
      Generated.Catalogue.S5_83.table.semigroup.eval
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
      Generated.Catalogue.S5_83.table.semigroup.eval
          (finalSeparator tested)
          (wordOfPrefixFinal stem final) = (3 : Fin 5) ↔
        final = tested ∧ tested ∉ stem
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, finalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue : finalSeparator tested x = (3 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (finalMarker_ne_marker _ equality).elim
        · intro condition
          exfalso
          exact condition.2 (by simp [xTested])
      · have headValue : finalSeparator tested x = (4 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_83.mul 4
                (Generated.Catalogue.S5_83.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (3 : Fin 5) ↔
              Generated.Catalogue.S5_83.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final) = (3 : Fin 5) :=
            finalPass_eq_marker_iff _
          _ ↔ final = tested ∧ tested ∉ xs :=
            evalFinalPrefix_eq_marker_iff tested xs final
          _ ↔ final = tested ∧ tested ∉ x :: xs := by
            simp [Ne.symm xTested]

private theorem evalPair_ne_content
    (candidatePenultimate candidateFinal actualPenultimate actualFinal : Nat) :
    ∀ stem,
      Generated.Catalogue.S5_83.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem actualPenultimate actualFinal) ≠
        (2 : Fin 5)
  | [] => by
      change
        Generated.Catalogue.S5_83.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal actualFinal) ≠ 2
      exact mul_ne_content _ _
  | x :: xs => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_content _ _

private theorem evalPairPrefix_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) :
    ∀ stem actualPenultimate actualFinal,
      Generated.Catalogue.S5_83.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem actualPenultimate actualFinal) =
            (1 : Fin 5) ↔
        pairSignature stem actualPenultimate actualFinal
          candidatePenultimate candidateFinal
  | [], actualPenultimate, actualFinal => by
      change
        Generated.Catalogue.S5_83.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal actualFinal) =
              1 ↔
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
          Generated.Catalogue.S5_83.mul, penEqCandidate, penEqFinal,
          finalEqCandidate, finalEqFinal, eq_comm]
  | x :: xs, actualPenultimate, actualFinal => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xEqCandidate : x = candidatePenultimate
      · have restNe :=
          evalPair_ne_content candidatePenultimate candidateFinal
            actualPenultimate actualFinal xs
        have headValue :
            pairSeparator candidatePenultimate candidateFinal x =
              (3 : Fin 5) := by
          simp [pairSeparator, xEqCandidate]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (restNe ((pairMarker_eq_signal_iff _).mp equality)).elim
        · rintro ⟨_, _, candidateAbsent, _, _⟩
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
                (2 : Fin 5) := by
            rw [xEqFinal]
            simp [pairSeparator, finalNeCandidate]
          rw [headValue, table_semigroup_mul]
          constructor
          · intro equality
            exact (pairContent_ne_signal _ equality).elim
          · rintro ⟨_, _, _, _, finalAbsent⟩
            exfalso
            apply finalAbsent
            simp [xEqFinal]
        · have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (4 : Fin 5) := by
            simp [pairSeparator, xEqCandidate, xEqFinal]
          rw [headValue, table_semigroup_mul]
          calc
            Generated.Catalogue.S5_83.mul 4
                  (Generated.Catalogue.S5_83.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal)) =
                (1 : Fin 5) ↔
              Generated.Catalogue.S5_83.table.semigroup.eval
                    (pairSeparator candidatePenultimate candidateFinal)
                    (wordOfTerminalPair xs actualPenultimate actualFinal) =
                (1 : Fin 5) := pairPass_eq_signal_iff _
            _ ↔ pairSignature xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal
            _ ↔ pairSignature (x :: xs) actualPenultimate actualFinal
                  candidatePenultimate candidateFinal :=
              (pairSignature_cons_iff x xs actualPenultimate actualFinal
                candidatePenultimate candidateFinal xEqCandidate
                xEqFinal).symm

theorem evalSupport_eq_pass_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_83.table.semigroup.eval
        (supportSeparator tested) word = (4 : Fin 5) ↔
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
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        toList_wordOfPrefixFinal, List.mem_append, eq_comm,
        and_assoc] using
        evalSupportPrefix_eq_pass_iff tested
          (stem ++ [penultimate]) final

theorem evalSingleton_eq_projection_iff (word : Word Nat) :
    Generated.Catalogue.S5_83.table.semigroup.eval
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

theorem evalFinal_eq_marker_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_83.table.semigroup.eval
        (finalSeparator tested) word = (3 : Fin 5) ↔
      UniqueFinal word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      by_cases finalTested : final = tested <;>
        simp [TerminalSplit.renderWord, finalSeparator, finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        List.mem_append, finalCondition_iff, eq_comm] using
        evalFinalPrefix_eq_marker_iff tested
          (stem ++ [penultimate]) final

theorem evalPair_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_83.table.semigroup.eval
        (pairSeparator candidatePenultimate candidateFinal) word =
          (1 : Fin 5) ↔
      UniqueTerminalPair word candidatePenultimate candidateFinal := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueTerminalPair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord] using
        pairSeparator_ne_signal candidatePenultimate candidateFinal final
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueTerminalPair
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, pairSignature] using
        evalPairPrefix_eq_signal_iff
          candidatePenultimate candidateFinal
          stem penultimate final

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_83.table.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  support_of_absence_equivalence evalSupport_eq_pass_iff identity valid

theorem valid_singleton
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_83.table.semigroup) :
    IsSingletonWord identity.lhs ↔
      IsSingletonWord identity.rhs :=
  singleton_of_eval_equivalence evalSingleton_eq_projection_iff
    identity valid

theorem valid_uniqueFinal
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_83.table.semigroup) :
    ∀ tested,
      UniqueFinal identity.lhs tested ↔
        UniqueFinal identity.rhs tested :=
  uniqueFinal_of_eval_equivalence evalFinal_eq_marker_iff identity valid

theorem valid_uniqueTerminalPair
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_83.table.semigroup) :
    ∀ penultimate final,
      UniqueTerminalPair identity.lhs penultimate final ↔
        UniqueTerminalPair identity.rhs penultimate final := by
  intro penultimate final
  have evaluated := valid (pairSeparator penultimate final)
  calc
    UniqueTerminalPair identity.lhs penultimate final ↔
        Generated.Catalogue.S5_83.table.semigroup.eval
            (pairSeparator penultimate final) identity.lhs =
              (1 : Fin 5) :=
      (evalPair_eq_signal_iff penultimate final identity.lhs).symm
    _ ↔
        Generated.Catalogue.S5_83.table.semigroup.eval
            (pairSeparator penultimate final) identity.rhs =
              (1 : Fin 5) := by
      rw [evaluated]
    _ ↔ UniqueTerminalPair identity.rhs penultimate final :=
      evalPair_eq_signal_iff penultimate final identity.rhs

theorem valid_signature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_83.table.semigroup) :
    SameTerminalUniqueSuffixSignature identity.lhs identity.rhs :=
  ⟨valid_support identity valid,
    valid_singleton identity valid,
    valid_uniqueFinal identity valid,
    valid_uniqueTerminalPair identity valid⟩

end S5_83

namespace S5_84

@[simp]
private theorem table_semigroup_mul (left right : Fin 5) :
    Generated.Catalogue.S5_84.table.semigroup.mul left right =
      Generated.Catalogue.S5_84.mul left right := rfl

private theorem supportHit_ne_pass (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 2 value ≠ 4 := by
  decide +revert

private theorem supportPass_eq_pass_iff (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 4 value = 4 ↔ value = 4 := by
  decide +revert

private theorem projection_mul_eq_sink (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 1 value = 0 := by
  decide +revert

private theorem finalMarker_ne_marker (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 3 value ≠ 3 := by
  decide +revert

private theorem finalPass_eq_marker_iff (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 4 value = 3 ↔ value = 3 := by
  decide +revert

private theorem pairMarker_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 3 value = 1 ↔ value = 2 := by
  decide +revert

private theorem pairContent_ne_signal (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 2 value ≠ 1 := by
  decide +revert

private theorem pairPass_eq_signal_iff (value : Fin 5) :
    Generated.Catalogue.S5_84.mul 4 value = 1 ↔
      value = 1 ∨ value = 2 := by
  decide +revert

private theorem mul_ne_content (left right : Fin 5) :
    Generated.Catalogue.S5_84.mul left right ≠ 2 := by
  decide +revert

private theorem evalSupportPrefix_eq_pass_iff (tested : Nat) :
    ∀ stem final,
      Generated.Catalogue.S5_84.table.semigroup.eval
          (supportSeparator tested)
          (wordOfPrefixFinal stem final) = (4 : Fin 5) ↔
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
      · have headValue : supportSeparator tested x = (4 : Fin 5) := by
          simp [supportSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_84.mul 4
                (Generated.Catalogue.S5_84.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final)) = (4 : Fin 5) ↔
              Generated.Catalogue.S5_84.table.semigroup.eval
                  (supportSeparator tested)
                  (wordOfPrefixFinal xs final) = (4 : Fin 5) :=
            supportPass_eq_pass_iff _
          _ ↔ tested ∉ xs ∧ final ≠ tested :=
            evalSupportPrefix_eq_pass_iff tested xs final
          _ ↔ tested ∉ x :: xs ∧ final ≠ tested := by
            simp [Ne.symm xTested]

private theorem evalSingletonPrefix_eq_projection_iff :
    ∀ stem final,
      Generated.Catalogue.S5_84.table.semigroup.eval
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
      Generated.Catalogue.S5_84.table.semigroup.eval
          (finalSeparator tested)
          (wordOfPrefixFinal stem final) = (3 : Fin 5) ↔
        final = tested ∧ tested ∉ stem
  | [], final => by
      by_cases finalTested : final = tested <;>
        simp [wordOfPrefixFinal, finalSeparator, finalTested]
  | x :: xs, final => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xTested : x = tested
      · have headValue : finalSeparator tested x = (3 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (finalMarker_ne_marker _ equality).elim
        · intro condition
          exfalso
          exact condition.2 (by simp [xTested])
      · have headValue : finalSeparator tested x = (4 : Fin 5) := by
          simp [finalSeparator, xTested]
        rw [headValue, table_semigroup_mul]
        calc
          Generated.Catalogue.S5_84.mul 4
                (Generated.Catalogue.S5_84.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final)) = (3 : Fin 5) ↔
              Generated.Catalogue.S5_84.table.semigroup.eval
                  (finalSeparator tested)
                  (wordOfPrefixFinal xs final) = (3 : Fin 5) :=
            finalPass_eq_marker_iff _
          _ ↔ final = tested ∧ tested ∉ xs :=
            evalFinalPrefix_eq_marker_iff tested xs final
          _ ↔ final = tested ∧ tested ∉ x :: xs := by
            simp [Ne.symm xTested]

private theorem evalPair_ne_content
    (candidatePenultimate candidateFinal actualPenultimate actualFinal : Nat) :
    ∀ stem,
      Generated.Catalogue.S5_84.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem actualPenultimate actualFinal) ≠
        (2 : Fin 5)
  | [] => by
      change
        Generated.Catalogue.S5_84.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal actualFinal) ≠ 2
      exact mul_ne_content _ _
  | x :: xs => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      exact mul_ne_content _ _

private theorem evalPairPrefix_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) :
    ∀ stem actualPenultimate actualFinal,
      Generated.Catalogue.S5_84.table.semigroup.eval
          (pairSeparator candidatePenultimate candidateFinal)
          (wordOfTerminalPair stem actualPenultimate actualFinal) =
            (1 : Fin 5) ↔
        absentPenultimateSignal stem actualPenultimate actualFinal
            candidatePenultimate candidateFinal ∨
          pairSignature stem actualPenultimate actualFinal
            candidatePenultimate candidateFinal
  | [], actualPenultimate, actualFinal => by
      change
        Generated.Catalogue.S5_84.mul
            (pairSeparator candidatePenultimate candidateFinal
              actualPenultimate)
            (pairSeparator candidatePenultimate candidateFinal actualFinal) =
              1 ↔
          absentPenultimateSignal [] actualPenultimate actualFinal
              candidatePenultimate candidateFinal ∨
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
        simp_all [pairSeparator, pairSignature, absentPenultimateSignal,
          Generated.Catalogue.S5_84.mul, penEqCandidate, penEqFinal,
          finalEqCandidate, finalEqFinal, eq_comm]
  | x :: xs, actualPenultimate, actualFinal => by
      rw [wordOfTerminalPair_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases xEqCandidate : x = candidatePenultimate
      · have restNe :=
          evalPair_ne_content candidatePenultimate candidateFinal
            actualPenultimate actualFinal xs
        have headValue :
            pairSeparator candidatePenultimate candidateFinal x =
              (3 : Fin 5) := by
          simp [pairSeparator, xEqCandidate]
        rw [headValue, table_semigroup_mul]
        constructor
        · intro equality
          exact (restNe ((pairMarker_eq_signal_iff _).mp equality)).elim
        · rintro (absent | signature)
          · rcases absent with ⟨candidateAbsent, _, _, _, _, _⟩
            exfalso
            apply candidateAbsent
            simp [xEqCandidate]
          · rcases signature with ⟨_, _, candidateAbsent, _, _⟩
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
                (2 : Fin 5) := by
            rw [xEqFinal]
            simp [pairSeparator, finalNeCandidate]
          rw [headValue, table_semigroup_mul]
          constructor
          · intro equality
            exact (pairContent_ne_signal _ equality).elim
          · rintro (absent | signature)
            · rcases absent with
                ⟨_, _, _, actualFinalEq, _, actualFinalAbsent⟩
              exfalso
              apply actualFinalAbsent
              simp [xEqFinal, actualFinalEq]
            · rcases signature with ⟨_, _, _, _, finalAbsent⟩
              exfalso
              apply finalAbsent
              simp [xEqFinal]
        · have restNe :=
            evalPair_ne_content candidatePenultimate candidateFinal
              actualPenultimate actualFinal xs
          have headValue :
              pairSeparator candidatePenultimate candidateFinal x =
                (4 : Fin 5) := by
            simp [pairSeparator, xEqCandidate, xEqFinal]
          rw [headValue, table_semigroup_mul]
          constructor
          · intro equality
            have restSignal := (pairPass_eq_signal_iff _).mp equality
            have restOne := restSignal.resolve_right restNe
            have recursiveSignal :=
              (evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal).mp restOne
            rcases recursiveSignal with absent | signature
            · exact Or.inl
                ((absentPenultimateSignal_cons_iff x xs
                  actualPenultimate actualFinal candidatePenultimate
                  candidateFinal xEqCandidate xEqFinal).mpr absent)
            · exact Or.inr
                ((pairSignature_cons_iff x xs actualPenultimate actualFinal
                  candidatePenultimate candidateFinal xEqCandidate
                  xEqFinal).mpr signature)
          · intro signal
            have recursiveSignal :
                absentPenultimateSignal xs actualPenultimate actualFinal
                    candidatePenultimate candidateFinal ∨
                  pairSignature xs actualPenultimate actualFinal
                    candidatePenultimate candidateFinal := by
              rcases signal with absent | signature
              · exact Or.inl
                  ((absentPenultimateSignal_cons_iff x xs
                    actualPenultimate actualFinal candidatePenultimate
                    candidateFinal xEqCandidate xEqFinal).mp absent)
              · exact Or.inr
                  ((pairSignature_cons_iff x xs actualPenultimate actualFinal
                    candidatePenultimate candidateFinal xEqCandidate
                    xEqFinal).mp signature)
            have restOne :=
              (evalPairPrefix_eq_signal_iff candidatePenultimate
                candidateFinal xs actualPenultimate actualFinal).mpr
                  recursiveSignal
            exact (pairPass_eq_signal_iff _).mpr (Or.inl restOne)

theorem evalSupport_eq_pass_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_84.table.semigroup.eval
        (supportSeparator tested) word = (4 : Fin 5) ↔
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
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        toList_wordOfPrefixFinal, List.mem_append, eq_comm,
        and_assoc] using
        evalSupportPrefix_eq_pass_iff tested
          (stem ++ [penultimate]) final

theorem evalSingleton_eq_projection_iff (word : Word Nat) :
    Generated.Catalogue.S5_84.table.semigroup.eval
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

theorem evalFinal_eq_marker_iff (tested : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_84.table.semigroup.eval
        (finalSeparator tested) word = (3 : Fin 5) ↔
      UniqueFinal word tested := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      by_cases finalTested : final = tested <;>
        simp [TerminalSplit.renderWord, finalSeparator, finalTested]
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      unfold UniqueFinal
      rw [splitEq, ← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        List.mem_append, finalCondition_iff, eq_comm] using
        evalFinalPrefix_eq_marker_iff tested
          (stem ++ [penultimate]) final

private def pairFallback
    (word : Word Nat) (candidatePenultimate candidateFinal : Nat) : Prop :=
  candidatePenultimate ∉ word.toList ∧
    UniqueFinal word candidateFinal ∧
    ¬ IsSingletonWord word

private theorem evalPair_eq_signal_iff
    (candidatePenultimate candidateFinal : Nat) (word : Word Nat) :
    Generated.Catalogue.S5_84.table.semigroup.eval
        (pairSeparator candidatePenultimate candidateFinal) word =
          (1 : Fin 5) ↔
      pairFallback word candidatePenultimate candidateFinal ∨
        UniqueTerminalPair word candidatePenultimate candidateFinal := by
  cases splitEq : terminalSplit word with
  | singleton final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      simp [pairFallback, UniqueFinal, IsSingletonWord,
        UniqueTerminalPair, splitEq]
      rw [← reconstruct]
      simpa [TerminalSplit.renderWord] using
        pairSeparator_ne_signal candidatePenultimate candidateFinal final
  | pair stem penultimate final =>
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      simp only [pairFallback, UniqueFinal, IsSingletonWord,
        UniqueTerminalPair, splitEq, not_false_eq_true, and_true]
      rw [← reconstruct]
      simpa [TerminalSplit.renderWord, wordOfTerminalPair,
        toList_wordOfPrefixFinal, List.mem_append,
        absentPenultimateSignal, pairSignature, eq_comm,
        and_assoc] using
        evalPairPrefix_eq_signal_iff
          candidatePenultimate candidateFinal
          stem penultimate final

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_84.table.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  support_of_absence_equivalence evalSupport_eq_pass_iff identity valid

theorem valid_singleton
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_84.table.semigroup) :
    IsSingletonWord identity.lhs ↔
      IsSingletonWord identity.rhs :=
  singleton_of_eval_equivalence evalSingleton_eq_projection_iff
    identity valid

theorem valid_uniqueFinal
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_84.table.semigroup) :
    ∀ tested,
      UniqueFinal identity.lhs tested ↔
        UniqueFinal identity.rhs tested :=
  uniqueFinal_of_eval_equivalence evalFinal_eq_marker_iff identity valid

theorem valid_uniqueTerminalPair
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_84.table.semigroup) :
    ∀ penultimate final,
      UniqueTerminalPair identity.lhs penultimate final ↔
        UniqueTerminalPair identity.rhs penultimate final := by
  intro penultimate final
  have support := valid_support identity valid
  have evaluated := valid (pairSeparator penultimate final)
  constructor
  · intro leftPair
    have leftSignal :
        Generated.Catalogue.S5_84.table.semigroup.eval
            (pairSeparator penultimate final) identity.lhs =
              (1 : Fin 5) :=
      (evalPair_eq_signal_iff
        penultimate final identity.lhs).2 (Or.inr leftPair)
    have rightSignal :
        Generated.Catalogue.S5_84.table.semigroup.eval
            (pairSeparator penultimate final) identity.rhs =
              (1 : Fin 5) :=
      evaluated.symm.trans leftSignal
    rcases
        (evalPair_eq_signal_iff
          penultimate final identity.rhs).1 rightSignal with
      rightFallback | rightPair
    · have leftMember :
          penultimate ∈ identity.lhs.toList :=
        uniqueTerminalPair_penultimate_mem leftPair
      have rightMember := (support penultimate).mp leftMember
      exact False.elim (rightFallback.1 rightMember)
    · exact rightPair
  · intro rightPair
    have rightSignal :
        Generated.Catalogue.S5_84.table.semigroup.eval
            (pairSeparator penultimate final) identity.rhs =
              (1 : Fin 5) :=
      (evalPair_eq_signal_iff
        penultimate final identity.rhs).2 (Or.inr rightPair)
    have leftSignal :
        Generated.Catalogue.S5_84.table.semigroup.eval
            (pairSeparator penultimate final) identity.lhs =
              (1 : Fin 5) :=
      evaluated.trans rightSignal
    rcases
        (evalPair_eq_signal_iff
          penultimate final identity.lhs).1 leftSignal with
      leftFallback | leftPair
    · have rightMember :
          penultimate ∈ identity.rhs.toList :=
        uniqueTerminalPair_penultimate_mem rightPair
      have leftMember := (support penultimate).mpr rightMember
      exact False.elim (leftFallback.1 leftMember)
    · exact leftPair

theorem valid_signature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_84.table.semigroup) :
    SameTerminalUniqueSuffixSignature identity.lhs identity.rhs :=
  ⟨valid_support identity valid,
    valid_singleton identity valid,
    valid_uniqueFinal identity valid,
    valid_uniqueTerminalPair identity valid⟩

end S5_84

end SemigroupBasis.CoRoots.S5_83Factors
