import SemigroupBasis.CoRoots.S5_207Normalization

namespace SemigroupBasis.CoRoots.S5_207

open SemigroupBasis
open SemigroupBasis.Examples
open DirectCompletenessArchitecture

namespace DirectCompletenessArchitecture

/-- The concrete table output corresponding to each of the five marker
states. These are zero-based versions of the recorded outputs 5, 4, 3, 2, 1. -/
def markerOutput : MarkerState -> Fin 5
  | .absent => 4
  | .finalOnly => 3
  | .oneNonfinal => 2
  | .oneNonfinalAndFinal => 1
  | .atLeastTwoNonfinal => 0

theorem markerOutput_injective : Function.Injective markerOutput := by
  intro left right equal
  cases left <;> cases right <;>
    simp [markerOutput] at equal ⊢

/-- Prefixing one tested letter advances the marker automaton by one capped
nonfinal occurrence. -/
def advanceMarkerState : MarkerState -> MarkerState
  | .absent => .oneNonfinal
  | .finalOnly => .oneNonfinalAndFinal
  | .oneNonfinal => .atLeastTwoNonfinal
  | .oneNonfinalAndFinal => .atLeastTwoNonfinal
  | .atLeastTwoNonfinal => .atLeastTwoNonfinal

@[simp]
theorem markerStateFrom_succ
    (prefixCount : Nat) (finalIsLetter : Bool) :
    markerStateFrom (prefixCount + 1) finalIsLetter =
      advanceMarkerState
        (markerStateFrom prefixCount finalIsLetter) := by
  cases prefixCount with
  | zero =>
      cases finalIsLetter <;> rfl
  | succ prefixCount =>
      cases prefixCount with
      | zero =>
          cases finalIsLetter <;> rfl
      | succ prefixCount =>
          have currentAtLeast : 2 ≤ prefixCount + 1 + 1 := by
            omega
          have nextAtLeast : 2 ≤ prefixCount + 1 + 1 + 1 := by
            omega
          cases finalIsLetter <;>
            simp [markerStateFrom, advanceMarkerState,
              Nat.min_eq_right currentAtLeast,
              Nat.min_eq_right nextAtLeast]

/-- Assign the tested variable to table element 4 and every other variable to
table element 5, using one-based catalogue terminology. -/
def markerValuation (tested value : Nat) : Fin 5 :=
  if value = tested then 3 else 4

private theorem markerDefault_mul (state : MarkerState) :
    table.semigroup.mul (4 : Fin 5) (markerOutput state) =
      markerOutput state := by
  cases state <;> decide

private theorem markerTested_mul (state : MarkerState) :
    table.semigroup.mul (3 : Fin 5) (markerOutput state) =
      markerOutput (advanceMarkerState state) := by
  cases state <;> decide

/-- Exact replay of the five-state marker automaton in the generated
`S5_207` table. -/
theorem eval_markerValuation
    (tested : Nat) (stem : List Nat) (final : Nat) :
    table.semigroup.eval (markerValuation tested)
        (wordOfPrefixFinal stem final) =
      markerOutput (splitMarkerState stem final tested) := by
  induction stem with
  | nil =>
      by_cases finalEq : final = tested
      · subst final
        simp [wordOfPrefixFinal, markerValuation, splitMarkerState,
          markerStateFrom, markerOutput]
      · have finalBeq : (final == tested) = false :=
          beq_eq_false_iff_ne.mpr finalEq
        simp [wordOfPrefixFinal, markerValuation, splitMarkerState,
          markerStateFrom, markerOutput, finalEq, finalBeq]
  | cons head tail ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      simp only [splitMarkerState]
      by_cases headEq : head = tested
      · subst head
        rw [List.count_cons_self, markerStateFrom_succ]
        simpa [markerValuation] using
          markerTested_mul
            (markerStateFrom (tail.count tested) (final == tested))
      · rw [List.count_cons_of_ne headEq]
        simpa [markerValuation, headEq] using
          markerDefault_mul
            (markerStateFrom (tail.count tested) (final == tested))

end DirectCompletenessArchitecture

/-- Every identity valid in the exact catalogue table has the complete
five-state marker signature. -/
theorem valid_sameMarkerSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameMarkerSignature identity.lhs identity.rhs := by
  intro tested
  let leftSplit := splitPrefixFinal identity.lhs
  let rightSplit := splitPrefixFinal identity.rhs
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  have evaluated := valid (markerValuation tested)
  rw [← leftReconstruct, ← rightReconstruct,
    eval_markerValuation, eval_markerValuation] at evaluated
  have splitStateEq := markerOutput_injective evaluated
  rw [← leftReconstruct, ← rightReconstruct,
    markerState_wordOfPrefixFinal,
    markerState_wordOfPrefixFinal]
  exact splitStateEq

set_option maxRecDepth 100000 in
/-- Every derivation from the displayed basis preserves the marker signature,
including through arbitrary contexts and substitutions. -/
theorem derives_sameMarkerSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameMarkerSignature left right :=
  valid_sameMarkerSignature ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

/-- Every displayed basis law preserves the marker signature after an
arbitrary simultaneous nonempty-word substitution. -/
theorem basisLaw_bind_sameMarkerSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    SameMarkerSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameMarkerSignature <|
    Derives.subst
      (Derives.fromBasis (basis := basis) member) substitution

end SemigroupBasis.CoRoots.S5_207
