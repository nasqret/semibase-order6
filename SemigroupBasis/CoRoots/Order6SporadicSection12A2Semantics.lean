import SemigroupBasis.CoRoots.Order6SporadicSection12A2Normalization
import SemigroupBasis.CoRoots.Order6SporadicSection12Semantics
import SemigroupBasis.CoRoots.S5_207Invariant
import SemigroupBasis.CoRoots.S5_345Factors

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open S5_207.DirectCompletenessArchitecture

namespace A2Semantics

/-- The exact A2 semantic signature used in Proposition 12.1: initial order,
global multiplicity truncated at two, the optional globally simple final
variable, and the direct `5/6` terminal probe from the paper. -/
structure SameSignature (left right : Word Nat) : Prop where
  firstOccurrences :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleFinal :
    S5_345.simpleFinalVariable left =
      S5_345.simpleFinalVariable right
  marker :
    ∀ letter, markerState left letter = markerState right letter

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  ⟨rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSignature left right) :
    SameSignature right left :=
  ⟨same.firstOccurrences.symm,
    fun letter => (same.capped letter).symm,
    same.simpleFinal.symm,
    fun letter => (same.marker letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle)
    (second : SameSignature middle right) :
    SameSignature left right :=
  ⟨first.firstOccurrences.trans second.firstOccurrences,
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    first.simpleFinal.trans second.simpleFinal,
    fun letter =>
      (first.marker letter).trans (second.marker letter)⟩

end SameSignature

/-- Pull the initial-order detector `L_2^1 = S3_16` back from A2. -/
theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S6_5597.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have factorValid := S6_5597.valid_l_2_1 identity valid
  rw [Generated.S3_16.table_eq_catalogue_model] at factorValid
  exact
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity factorValid

/-- Pull the absent/simple/multiple detector `N_2^1 = S3_8` back from A2. -/
theorem valid_cappedMultiplicity_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S6_5597.table.semigroup) :
    ∀ letter,
      S5_107.cappedMultiplicity identity.lhs letter =
        S5_107.cappedMultiplicity identity.rhs letter := by
  have factorValid := S6_5597.valid_n_2_1 identity valid
  rw [Generated.S3_8.table_eq_catalogue_model] at factorValid
  intro letter
  simpa [S5_107.cappedMultiplicity, Nat.min_comm] using
    exponentValid_capped_count_eq identity factorValid letter

/-- Pull the globally-simple-final detector `J = S3_6` back from A2. -/
theorem valid_simpleFinalVariable_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S6_5597.table.semigroup) :
    S5_345.simpleFinalVariable identity.lhs =
      S5_345.simpleFinalVariable identity.rhs := by
  have factorValid := S6_5597.valid_j identity valid
  rw [Generated.S3_6.table_eq_catalogue_model] at factorValid
  exact
    S5_345Factors.finalMarkerThreeValid_simpleFinalVariable_eq
      identity factorValid

/-- Zero-based outputs of the paper's `5/6` valuation. The catalogue
relabeling sends one-based element `5` to zero-based `3` and fixes `6` as
zero-based `5`. -/
def markerOutput : MarkerState -> Fin 6
  | .absent => 5
  | .finalOnly => 3
  | .oneNonfinal => 2
  | .oneNonfinalAndFinal => 1
  | .atLeastTwoNonfinal => 0

theorem markerOutput_injective : Function.Injective markerOutput := by
  intro left right equal
  cases left <;> cases right <;>
    simp [markerOutput] at equal ⊢

def markerValuation (tested value : Nat) : Fin 6 :=
  if value = tested then 3 else 5

private theorem markerDefault_mul (state : MarkerState) :
    S6_5597.table.semigroup.mul (5 : Fin 6) (markerOutput state) =
      markerOutput state := by
  cases state <;> decide

private theorem markerTested_mul (state : MarkerState) :
    S6_5597.table.semigroup.mul (3 : Fin 6) (markerOutput state) =
      markerOutput (advanceMarkerState state) := by
  cases state <;> decide

/-- Exact evaluation of the paper's `5/6` valuation in the A2 catalogue
table, expressed by the shared five-state prefix/final marker. -/
theorem eval_terminalProbe
    (tested : Nat) (stem : List Nat) (final : Nat) :
    S6_5597.table.semigroup.eval (markerValuation tested)
        (wordOfPrefixFinal stem final) =
      markerOutput (splitMarkerState stem final tested) := by
  induction stem with
  | nil =>
      by_cases finalEq : final = tested
      · subst final
        rw [wordOfPrefixFinal_nil, Semigroup.eval_singleton]
        simp [markerValuation, splitMarkerState, markerStateFrom,
          markerOutput]
      · rw [wordOfPrefixFinal_nil, Semigroup.eval_singleton]
        have finalBeq : (final == tested) = false :=
          beq_eq_false_iff_ne.mpr finalEq
        simp [markerValuation, splitMarkerState, markerStateFrom,
          markerOutput, finalEq, finalBeq]
  | cons head tail induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
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

/-- Every A2 identity preserves the exact capped-prefix/final marker state. -/
theorem valid_markerState_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S6_5597.table.semigroup) :
    ∀ tested,
      markerState identity.lhs tested =
        markerState identity.rhs tested := by
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
    eval_terminalProbe, eval_terminalProbe] at evaluated
  have splitStateEq := markerOutput_injective evaluated
  rw [← leftReconstruct, ← rightReconstruct,
    markerState_wordOfPrefixFinal,
    markerState_wordOfPrefixFinal]
  exact splitStateEq

/-- Every identity valid in the exact A2 table has the full semantic
signature required by the canonical uniqueness argument. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S6_5597.table.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  refine
    ⟨valid_firstOccurrenceSequence_eq identity valid,
      valid_cappedMultiplicity_eq identity valid,
      valid_simpleFinalVariable_eq identity valid, ?_⟩
  exact valid_markerState_eq identity valid

end A2Semantics

end SemigroupBasis.CoRoots.Order6SporadicSection12
