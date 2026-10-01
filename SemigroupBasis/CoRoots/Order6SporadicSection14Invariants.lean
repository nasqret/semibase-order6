import SemigroupBasis.CoRoots.Order6SporadicSection14Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.LeftZeroTwo

namespace SemigroupBasis.CoRoots.Order6SporadicSection14

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Factor invariants used in Lemmas 14.3 and 14.6 -/

/-- Validity in the embedded copy of `L_2^1` preserves first-occurrence
order. -/
theorem lrbValid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S3_16.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  exact
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity (by
        simpa [Generated.S3_16.table, leftRegularBandThree] using valid)

private theorem reverse_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).reverse =
      Word.mk final stem.reverse := by
  apply Word.toList_injective
  rw [Word.toList_reverse, toList_wordOfPrefixFinal]
  simp [Word.toList]

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem splitPrefixFinal_snd_eq_final (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  calc
    word.reverse.head =
        (wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2).reverse.head :=
      congrArg (fun rebuilt : Word Nat => rebuilt.reverse.head)
        (wordOfPrefixFinal_split word).symm
    _ = (splitPrefixFinal word).2 :=
      congrArg Word.head <|
        reverse_wordOfPrefixFinal
          (splitPrefixFinal word).1
          (splitPrefixFinal word).2
    _ = word.final := splitPrefixFinal_snd_eq_final word

private theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat -> Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, different, Ne.symm different] at evaluated

/-- Validity in the embedded right-zero factor preserves the final letter. -/
theorem rightZeroValid_final_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.S2_4.table.semigroup.opposite) :
    identity.lhs.final = identity.rhs.final := by
  have rightZeroValid :
      identity.SatisfiedBy leftZeroTwo.semigroup.opposite := by
    simpa [Generated.S2_4.table, leftZeroTwo] using valid
  have reversedValid :
      identity.reversed.SatisfiedBy leftZeroTwo.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity leftZeroTwo.semigroup).1 rightZeroValid
  have heads := leftZeroValid_head_eq identity.reversed reversedValid
  simpa [Identity.reversed, reverse_head_eq_final] using heads

/-- Validity in the embedded copy of `J` preserves the optional globally
simple final variable. -/
theorem finalMarkerValid_simpleFinalVariable_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.S3_6.table.semigroup) :
    S5_345.simpleFinalVariable identity.lhs =
      S5_345.simpleFinalVariable identity.rhs := by
  exact
    S5_345Factors.finalMarkerThreeValid_simpleFinalVariable_eq
      identity (by
        simpa [Generated.S3_6.table, finalMarkerThree] using valid)

/-! ## Validity after canonicalization -/

def alphaCanonicalIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨alphaCanonicalWord identity.lhs, alphaCanonicalWord identity.rhs⟩

def betaCanonicalIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨betaCanonicalWord identity.lhs, betaCanonicalWord identity.rhs⟩

/-- Sound normalization transports an identity valid in an alpha target to
the identity between its two canonical representatives. -/
theorem alphaCanonicalIdentity_valid
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate alphaBasis)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate) :
    (alphaCanonicalIdentity identity).SatisfiedBy candidate := by
  intro valuation
  exact
    ((Alpha.derivesCanonicalWord identity.lhs).sound
      models valuation).symm.trans <|
      (valid valuation).trans
        ((Alpha.derivesCanonicalWord identity.rhs).sound models valuation)

/-- Sound normalization transports an identity valid in a beta target to the
identity between its two canonical representatives. -/
theorem betaCanonicalIdentity_valid
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate betaBasis)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate) :
    (betaCanonicalIdentity identity).SatisfiedBy candidate := by
  intro valuation
  exact
    ((Beta.derivesCanonicalWord identity.lhs).sound
      models valuation).symm.trans <|
      (valid valuation).trans
        ((Beta.derivesCanonicalWord identity.rhs).sound models valuation)

end SemigroupBasis.CoRoots.Order6SporadicSection14
