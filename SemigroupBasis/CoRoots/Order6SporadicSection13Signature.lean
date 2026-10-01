import SemigroupBasis.CoRoots.Order6SporadicSection13Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.AffineParityFour
import SemigroupBasis.Generated.S3_16

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis
open SemigroupBasis.Examples

/-- The `L_2^1` subsemigroup `{3,1,4}` of
`O = S4_96` opposite, in zero-based catalogue coordinates. -/
def oLeftRegularBandEmbedding :
    Embedding Generated.S3_16.table.semigroup
      Generated.S4_96.table.semigroup.opposite where
  toFun := fun value : Fin 3 =>
    if value = 0 then (2 : Fin 4)
    else if value = 1 then (0 : Fin 4)
    else (3 : Fin 4)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def pairParity (word : Word Nat) (tested marker : Nat) : Nat :=
  if tested = marker then 0
  else affineParitySuffixParity tested marker word.toList.reverse

/-- The complete combinatorial information used in the proof of Proposition
13.1.  Pair parity is retained for all ordered variable pairs; the diagonal
coordinates are harmless and avoid a partial signature. -/
structure JoinSignature where
  firstOccurrences : List Nat
  totalParity : Nat → Nat
  pairParity : Nat → Nat → Nat
  simpleFinal : Option Nat

namespace JoinSignature

@[ext]
theorem ext {left right : JoinSignature}
    (firstOccurrences : left.firstOccurrences = right.firstOccurrences)
    (totalParity : left.totalParity = right.totalParity)
    (pairParity : left.pairParity = right.pairParity)
    (simpleFinal : left.simpleFinal = right.simpleFinal) :
    left = right := by
  cases left
  cases right
  cases firstOccurrences
  cases totalParity
  cases pairParity
  cases simpleFinal
  rfl

end JoinSignature

def joinSignature (word : Word Nat) : JoinSignature where
  firstOccurrences := firstOccurrenceSequence word.toList
  totalParity := fun letter => word.toList.count letter % 2
  pairParity := pairParity word
  simpleFinal := S5_345.simpleFinalVariable word

theorem oValid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  have factorValid :=
    oLeftRegularBandEmbedding.pullback_identity identity valid
  rw [Generated.S3_16.table_eq_catalogue_model] at factorValid
  exact
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity factorValid

private theorem oValid_directReversed
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite) :
    identity.reversed.SatisfiedBy affineParityFour.semigroup := by
  apply (Identity.satisfiedBy_opposite_iff_reversed
    identity affineParityFour.semigroup).1
  simpa [Generated.S4_96.table] using valid

theorem oValid_totalParity_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite) :
    ∀ letter,
      identity.lhs.toList.count letter % 2 =
        identity.rhs.toList.count letter % 2 := by
  have parity :=
    affineParityValid_totalParity identity.reversed
      (oValid_directReversed identity valid)
  simpa [Identity.reversed] using parity

theorem oValid_pairParity_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite) :
    ∀ tested marker,
      pairParity identity.lhs tested marker =
        pairParity identity.rhs tested marker := by
  intro tested marker
  by_cases same : tested = marker
  · simp [pairParity, same]
  · have parity :=
      affineParityValid_suffixParity identity.reversed
        (oValid_directReversed identity valid)
        tested marker same
    simpa [pairParity, same, Identity.reversed] using parity

theorem jValid_simpleFinalVariable_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.S3_6.table.semigroup) :
    S5_345.simpleFinalVariable identity.lhs =
      S5_345.simpleFinalVariable identity.rhs := by
  rw [Generated.S3_6.table_eq_catalogue_model] at valid
  exact
    S5_345Factors.finalMarkerThreeValid_simpleFinalVariable_eq
      identity valid

theorem joinSignature_eq_of_factors
    (identity : Identity Nat)
    (jValid : identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (oValid :
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite) :
    joinSignature identity.lhs = joinSignature identity.rhs := by
  apply JoinSignature.ext
  · exact oValid_firstOccurrenceSequence_eq identity oValid
  · funext letter
    exact oValid_totalParity_eq identity oValid letter
  · funext tested marker
    exact oValid_pairParity_eq identity oValid tested marker
  · exact jValid_simpleFinalVariable_eq identity jValid

end SemigroupBasis.CoRoots.Order6SporadicSection13
