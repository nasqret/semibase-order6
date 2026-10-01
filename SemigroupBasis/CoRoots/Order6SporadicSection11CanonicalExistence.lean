import SemigroupBasis.CoRoots.Order6SporadicSection11PivotDecomposition

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

private abbrev ListDerives :=
  S5_107.ListDerives basis

/-- A protected block prefix is canonical when its final letter is simple, or
when every block after the first final-letter copy is a singleton. -/
def CanonicalProtectedPrefix (stem : List Nat) (final : Nat) : Prop :=
  S5_530.S5_530Normal stem ∧
    stem.count final ≤ 2 ∧
    (final ∉ stem ∨
      ∃ before after,
        stem = before ++ [final] ++ after ∧
          final ∉ before ∧ after.Nodup)

def CanonicalProtectedWord (word : Word Nat) : Prop :=
  ∃ stem final,
    word = wordOfPrefixFinal stem final ∧
      CanonicalProtectedPrefix stem final

/-- Convert a protected block normal form to a canonical protected owner. -/
theorem protectedBlockNormal_listDerives_canonical
    {source : List Nat} (normalForm : ProtectedBlockNormal source) :
    ∃ targetPrefix targetFinal,
      ListDerives source (targetPrefix ++ [targetFinal]) ∧
        CanonicalProtectedPrefix targetPrefix targetFinal := by
  rcases normalForm with
    ⟨stem, final, rfl, prefixNormal, finalBound⟩
  by_cases finalMem : final ∈ stem
  · rcases normal_terminalOwnerSplit
        prefixNormal finalMem finalBound with canonical | pivoted
    · rcases canonical with
        ⟨before, after, prefixEq, finalNotBefore, afterNodup⟩
      refine ⟨stem, final, S5_107.ListDerives.refl _, ?_⟩
      exact ⟨prefixNormal, finalBound,
        Or.inr ⟨before, after, prefixEq, finalNotBefore, afterNodup⟩⟩
    · rcases pivoted with
        ⟨before, middle, pivot, right, prefixEq,
          pivotNotTargetBefore, targetNormal,
          rightNodup, pivotBound⟩
      let targetPrefix :=
        before ++ [final, final] ++ middle ++ [pivot] ++ right
      have changed :=
        listDerivesChangeTerminalOwner
          before middle right final pivot
      have derivation :
          ListDerives
            (stem ++ [final]) (targetPrefix ++ [pivot]) := by
        simpa [prefixEq, targetPrefix, List.append_assoc] using changed
      refine ⟨targetPrefix, pivot, derivation, targetNormal,
        pivotBound, Or.inr ?_⟩
      exact ⟨before ++ [final, final] ++ middle, right,
        by simp [targetPrefix, List.append_assoc],
        pivotNotTargetBefore, rightNodup⟩
  · refine ⟨stem, final, S5_107.ListDerives.refl _, ?_⟩
    exact ⟨prefixNormal, finalBound, Or.inl finalMem⟩

/-- Every word derives to some canonical protected block word. -/
theorem derives_canonicalProtectedWord (word : Word Nat) :
    ∃ target : Word Nat,
      Derives basis word target ∧ CanonicalProtectedWord target := by
  obtain ⟨targetPrefix, targetFinal, listDerivation, canonical⟩ :=
    protectedBlockNormal_listDerives_canonical
      (gatheredWord_protectedBlockNormal word)
  let target := wordOfPrefixFinal targetPrefix targetFinal
  have targetList :
      targetPrefix ++ [targetFinal] = target.toList := by
    simpa [target] using
      (toList_wordOfPrefixFinal targetPrefix targetFinal).symm
  rw [targetList] at listDerivation
  have gatheredToTarget :
      Derives basis (gatheredWord word) target := by
    cases sourceEquation : gatheredWord word with
    | mk sourceHead sourceTail =>
        cases targetEquation : target with
        | mk targetHead targetTail =>
            apply S5_107.ListDerives.toWord
            simpa [sourceEquation, targetEquation] using listDerivation
  refine ⟨target, (derivesGatheredWord word).trans gatheredToTarget, ?_⟩
  exact ⟨targetPrefix, targetFinal, rfl, canonical⟩

end SemigroupBasis.CoRoots.Order6SporadicSection11
