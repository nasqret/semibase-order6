import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank025
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Exact final-occurrence separator for the S5_832 rank-025 factor

The catalogue states `3` (pass), `1` (transient), and `0` (absorbing) detect
whether the common final variable occurs exactly once.  The theorem is
uniform in the alphabet and the word length; no finite-word bound is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_832

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev factor := Generated.Catalogue.S5_832.table.semigroup

def markerValuation (marker : Nat) (letter : Nat) : Fin 5 :=
  if letter = marker then 1 else 3

private theorem markerMul_eq_pass_iff
    (marker letter : Nat) (state : Fin 5) :
    Generated.Catalogue.S5_832.mul state (markerValuation marker letter) = 3 ↔
      state = 3 ∧ letter ≠ marker := by
  by_cases equal : letter = marker
  · subst letter
    simp [markerValuation]
    revert state
    decide
  · simp [markerValuation, equal]
    revert state
    decide

private theorem markerFold_eq_pass_iff
    (marker : Nat) (letters : List Nat) (state : Fin 5) :
    letters.foldl
        (fun accumulator letter =>
          Generated.Catalogue.S5_832.mul accumulator
            (markerValuation marker letter)) state = 3 ↔
      state = 3 ∧ marker ∉ letters := by
  induction letters generalizing state with
  | nil => simp
  | cons letter rest induction =>
      rw [List.foldl_cons, induction, markerMul_eq_pass_iff]
      simp [eq_comm, and_assoc]

private theorem markerMul_transient_eq_transient_iff
    (state : Fin 5) :
    Generated.Catalogue.S5_832.mul state 1 = 1 ↔ state = 3 := by
  revert state
  decide

private theorem marker_pass_is_left_identity
    (marker letter : Nat) :
    Generated.Catalogue.S5_832.mul 3 (markerValuation marker letter) =
      markerValuation marker letter := by
  by_cases equal : letter = marker <;>
    simp [markerValuation, equal, Generated.Catalogue.S5_832.mul]

private theorem marker_eval_eq_full_fold
    (marker : Nat) (word : Word Nat) :
    factor.eval (markerValuation marker) word =
      word.toList.foldl
        (fun accumulator letter =>
          Generated.Catalogue.S5_832.mul accumulator
            (markerValuation marker letter)) 3 := by
  cases word with
  | mk first rest =>
      change
        rest.foldl
          (fun accumulator letter =>
            Generated.Catalogue.S5_832.mul accumulator
              (markerValuation marker letter))
          (markerValuation marker first) =
        (first :: rest).foldl
          (fun accumulator letter =>
            Generated.Catalogue.S5_832.mul accumulator
              (markerValuation marker letter)) 3
      rw [List.foldl_cons, marker_pass_is_left_identity]

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

/-- Under `final -> 1` and every other variable `-> 3`, a word ending in
`final` evaluates to `1` exactly when that variable occurs only once. -/
theorem finalMarker_eval_eq_transient_iff
    (word : Word Nat) :
    factor.eval (markerValuation word.final) word = (1 : Fin 5) ↔
      word.toList.count word.final = 1 := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  have split :
      word.toList =
        (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] :=
    reconstructed.symm
  have splitFinal : (splitPrefixFinal word).2 = word.final := by
    have sameFinal := congrArg Word.final (wordOfPrefixFinal_split word)
    rw [final_wordOfPrefixFinal] at sameFinal
    exact sameFinal
  rw [marker_eval_eq_full_fold, split, splitFinal,
    List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [show markerValuation word.final word.final = (1 : Fin 5) by
    simp [markerValuation]]
  rw [markerMul_transient_eq_transient_iff,
    markerFold_eq_pass_iff]
  simp [List.count_append, List.count_eq_zero]

/-- Validity in `S5_832` preserves simplicity of the common final variable. -/
theorem finalCountOneIff_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy factor)
    (finalEqual : identity.lhs.final = identity.rhs.final) :
    identity.lhs.toList.count identity.lhs.final = 1 ↔
      identity.rhs.toList.count identity.rhs.final = 1 := by
  rw [← finalMarker_eval_eq_transient_iff,
    ← finalMarker_eval_eq_transient_iff]
  have evaluations := valid (markerValuation identity.lhs.final)
  rw [← finalEqual, evaluations]

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_832
