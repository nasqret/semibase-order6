import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871RelativeLift
import SemigroupBasis.CoRoots.S5_869Family
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Independent unrestricted S3_15op × S5_871 rank-028 seed

Unlike the preceding S5_832 seed, frozen target law 02 duplicates the final
of EVERY nonsingleton word. The exact S5_871 constant-one valuation separates
singleton words from every longer word. Thus a structural lower-order lift
under the common final closes unrestricted completeness without a
multiplicity detector, right-reductive cancellation, or a bounded premise.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank028.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_871.table.semigroup

private theorem rank028_leftTable_eq :
    Rank028.leftTable =
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable := by
  change
    SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S3_15.table =
      SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.S3_15.table
  rw [SemigroupBasis.Generated.S3_15.table_eq_canonical_catalogue]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank028.basis toFinThree (by decide)

theorem modelsRight : Models rightFactor targetBasis :=
  Rank028.rightModels

private theorem zero_absorbing (value : Fin 5) :
    rightFactor.mul (0 : Fin 5) value = (0 : Fin 5) := by
  decide +revert

private theorem one_times_one :
    rightFactor.mul (1 : Fin 5) (1 : Fin 5) = (0 : Fin 5) := by
  decide

private theorem constantOne_fold_zero :
    ∀ letters : List Nat,
      letters.foldl
        (fun current _ => rightFactor.mul current (1 : Fin 5))
          (0 : Fin 5) = (0 : Fin 5)
  | [] => rfl
  | _ :: rest => by
      simp only [List.foldl_cons]
      rw [zero_absorbing]
      exact constantOne_fold_zero rest

/-- The exact finite factor distinguishes singleton words from every longer
word by its constant valuation at the nonidempotent state `1`. -/
theorem s5_871_constantOne_eval (word : Word Nat) :
    rightFactor.eval (fun _ => (1 : Fin 5)) word =
      if word.tail = [] then (1 : Fin 5) else 0 := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          change
            rest.foldl
              (fun current _ => rightFactor.mul current (1 : Fin 5))
              (rightFactor.mul (1 : Fin 5) (1 : Fin 5)) = (0 : Fin 5)
          rw [one_times_one]
          exact constantOne_fold_zero rest

/-- Validity in S5_871 preserves singleton-versus-nonsingleton shape. -/
theorem s5_871_singleton_iff_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 5))
  rw [s5_871_constantOne_eval, s5_871_constantOne_eval] at evaluated
  constructor
  · intro leftEmpty
    by_cases rightEmpty : identity.rhs.tail = []
    · exact rightEmpty
    · simp [leftEmpty, rightEmpty] at evaluated
  · intro rightEmpty
    by_cases leftEmpty : identity.lhs.tail = []
    · exact leftEmpty
    · simp [leftEmpty, rightEmpty] at evaluated

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

private theorem splitStem_nonempty_of_tail_nonempty
    (word : Word Nat) (nonempty : word.tail ≠ []) :
    (splitPrefixFinal word).1 ≠ [] := by
  intro empty
  have shape := toList_eq_splitPrefixFinal word
  rw [empty] at shape
  have lengths := congrArg List.length shape
  cases word with
  | mk first rest =>
      have restLength : rest.length = 0 := by
        simpa [Word.toList] using lengths
      cases rest with
      | nil => exact nonempty rfl
      | cons next remainder => simp at restLength

private theorem listWordOfCons_append_final
    (first : Nat) (rest : List Nat) (final : Nat) :
    SemigroupBasis.CoRoots.S5_107.listWordOfCons first rest ++
        Word.singleton final =
      wordOfPrefixFinal (first :: rest) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

/-- Literal frozen tail duplication duplicates the final of every
nonsingleton word, regardless of that variable's earlier multiplicity. -/
theorem derivesDuplicateFinal
    (word : Word Nat) (nonempty : word.tail ≠ []) :
    Derives targetBasis word
      (word ++ Word.singleton word.final) := by
  have stemNonempty :=
    splitStem_nonempty_of_tail_nonempty word nonempty
  cases stemShape : (splitPrefixFinal word).1 with
  | nil =>
      exact False.elim (stemNonempty stemShape)
  | cons first rest =>
      let stem := SemigroupBasis.CoRoots.S5_107.listWordOfCons first rest
      have shape :
          stem ++ Word.singleton (splitPrefixFinal word).2 = word := by
        calc
          stem ++ Word.singleton (splitPrefixFinal word).2 =
              wordOfPrefixFinal (first :: rest)
                (splitPrefixFinal word).2 := by
            simpa [stem] using
              listWordOfCons_append_final
                first rest (splitPrefixFinal word).2
          _ = wordOfPrefixFinal
                (splitPrefixFinal word).1
                (splitPrefixFinal word).2 := by
            rw [stemShape]
          _ = word := wordOfPrefixFinal_split word
      have duplicated :=
        derivesTailExpansion stem
          (Word.singleton (splitPrefixFinal word).2)
      rw [shape] at duplicated
      simpa only [split_final_eq] using duplicated

private theorem word_eq_singleton_final_of_tail_empty
    (word : Word Nat) (empty : word.tail = []) :
    word = Word.singleton word.final := by
  cases word with
  | mk first rest =>
      cases rest with
      | nil => rfl
      | cons next remainder =>
          contradiction

/-- Independent unrestricted completeness for the exact frozen S5_871 block. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_869Family.S5_871.basis_complete.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
      identity leftValid
  have finalEq := same.final_eq
  have singletonIff :=
    s5_871_singleton_iff_of_valid identity rightValid
  by_cases leftEmpty : identity.lhs.tail = []
  · have rightEmpty := singletonIff.mp leftEmpty
    have leftSingleton :=
      word_eq_singleton_final_of_tail_empty identity.lhs leftEmpty
    have rightSingleton :=
      word_eq_singleton_final_of_tail_empty identity.rhs rightEmpty
    have equal : identity.lhs = identity.rhs :=
      leftSingleton.trans <|
        (congrArg Word.singleton finalEq).trans rightSingleton.symm
    rw [equal]
    exact Derives.refl _
  · have rightNonempty : identity.rhs.tail ≠ [] := by
      intro rightEmpty
      exact leftEmpty (singletonIff.mpr rightEmpty)
    have leftDuplicate := derivesDuplicateFinal identity.lhs leftEmpty
    have rightDuplicate :=
      derivesDuplicateFinal identity.rhs rightNonempty
    have lifted :=
      liftS5_869UnderGuardIdentity sourceDerivation
        (Word.singleton identity.lhs.final)
    have guarded :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans <| guarded.trans rightDuplicate.symm

def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Exact unrestricted intersection basis for the frozen S5_871 rank block. -/
def intersectionBasis :
    IntersectionBasis
      Rank028.leftTable.semigroup
      Rank028.rightTable.semigroup
      Rank028.basis := by
  rw [rank028_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization is introduced only after independent completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank028.leftTable.semigroup
      Rank028.rightTable.semigroup
      Rank028.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The authenticated surviving ordinal-005 rank-028 representative. -/
theorem representative_basis_S6_13759 :
    BasisFor Rank028.S6_13759.table.semigroup Rank028.basis :=
  Rank028.S6_13759.representative_basis_of_normalizer
    intersectionNormalizer

/-- Its exact reversed-basis opposite orientation. -/
theorem opposite_basis_S6_13759 :
    BasisFor Rank028.S6_13759.table.semigroup.opposite
      (reversedBasis Rank028.basis) :=
  Rank028.S6_13759.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871
