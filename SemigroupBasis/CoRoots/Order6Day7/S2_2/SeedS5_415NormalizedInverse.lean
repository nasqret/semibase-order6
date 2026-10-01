import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415RepeatedCellRegularity
import SemigroupBasis.InverseSemigroup

/-!
# Rank040: actual normalized inverses and their complete factor signatures

The inner-inverse normalization from msg-0368 is genuine, and its parity
is the parity of the original word. For an already two-sided witness it
is derivably the SAME inverse. Inverse uniqueness is used only in models
of the frozen laws or in their term quotient, never as factor completeness.

Zero parity and a diagonal Brandt TERM FUNCTION are retained explicitly.
An ambient graph class is not a replacement for the full Brandt signature.
No regular-pair or diagonal comparison field is asserted in this module.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.NormalizedInverse

open SemigroupBasis
open BrandtParityBridge RepeatedCellRegularity ExposureReplay

def normalize (word inner : Word Nat) : Word Nat :=
  (inner ++ word) ++ inner

/-- Both actual inverse equations are inherited from the existing
associative construction; no new basis identity is needed. -/
def normalizeWitness (word inner : Word Nat)
    (reduces : Derives Rank040.basis ((word ++ inner) ++ word) word) : RankInverse word :=
  inverseWitnessOfInner word inner reduces

theorem normalizedParity (word inner : Word Nat) :
    SameOccurrenceParity word (normalize word inner) := by
  intro letter
  change word.toList.count letter % 2 = (normalize word inner).toList.count letter % 2
  simp only [normalize, Word.toList_append, List.count_append]
  omega

/-- In fact EVERY genuine inverse already has the word's parity. -/
theorem inverseParity {word : Word Nat} (witness : RankInverse word) :
    SameOccurrenceParity word witness.inverse := by
  intro letter
  have counts := (signature_of_derives witness.word_inverse_word).parity letter
  simp only [Word.toList_append, List.count_append] at counts
  change word.toList.count letter % 2 = witness.inverse.toList.count letter % 2
  omega

def reverseWitness {word : Word Nat} (witness : RankInverse word) : RankInverse witness.inverse where
  inverse := word
  word_inverse_word := witness.inverse_word_inverse
  inverse_word_inverse := witness.word_inverse_word

/-- Normalizing an already two-sided witness does not manufacture a new
equivalence class of inverse candidates. -/
theorem normalizedExistingInverseDerives {word : Word Nat} (witness : RankInverse word) :
    Derives Rank040.basis (normalize word witness.inverse) witness.inverse :=
  witness.inverse_word_inverse

theorem inverseDerivesUnique {word : Word Nat} (first second : RankInverse word) :
    Derives Rank040.basis first.inverse second.inverse := by
  apply (termClass_eq_iff_derives Rank040.basis).mp
  exact Semigroup.IdempotentsCommute.inverse_unique
    (modelIdempotentsCommute (termSemigroup Rank040.basis) (termSemigroup_models Rank040.basis))
    first.termInverse second.termInverse

theorem modelInverseEq_of_wordEq {S : Type} (G : Semigroup S) (models : Models G Rank040.basis)
    {left right : Word Nat} (leftWitness : RankInverse left) (rightWitness : RankInverse right)
    (valuation : Nat → S) (same : G.eval valuation left = G.eval valuation right) :
    G.eval valuation leftWitness.inverse = G.eval valuation rightWitness.inverse := by
  have rightInverse := rightWitness.model G models valuation
  rw [← same] at rightInverse
  exact Semigroup.IdempotentsCommute.inverse_unique
    (modelIdempotentsCommute G models) (leftWitness.model G models valuation) rightInverse

/-- Equal FULL factor signatures transport through actual chosen inverses,
including valuations at which either Brandt word is zero. -/
theorem sameFactorSignatureInverse {left right : Word Nat}
    (leftWitness : RankInverse left) (rightWitness : RankInverse right)
    (same : SameFactorSignature left right) :
    SameFactorSignature leftWitness.inverse rightWitness.inverse := by
  apply sameFactorSignature_of_factorValid
    (Identity.mk leftWitness.inverse rightWitness.inverse)
  · intro valuation
    exact modelInverseEq_of_wordEq leftTable.semigroup leftModels leftWitness rightWitness valuation
      (leftValid_of_sameOccurrenceParity (Identity.mk left right) same.parity valuation)
  · intro valuation
    exact modelInverseEq_of_wordEq rightTable.semigroup rightModels leftWitness rightWitness valuation
      (rightValid_of_sameBrandtSignature (Identity.mk left right) same.brandt valuation)

theorem sameFactorSignatureAppend {left left' right right' : Word Nat}
    (first : SameFactorSignature left left') (second : SameFactorSignature right right') :
    SameFactorSignature (left ++ right) (left' ++ right') := by
  apply sameFactorSignature_of_factorValid (Identity.mk (left ++ right) (left' ++ right'))
  · intro valuation
    simp only [Semigroup.eval_append]
    rw [leftValid_of_sameOccurrenceParity (Identity.mk left left') first.parity valuation,
      leftValid_of_sameOccurrenceParity (Identity.mk right right') second.parity valuation]
  · intro valuation
    simp only [Semigroup.eval_append]
    rw [rightValid_of_sameBrandtSignature (Identity.mk left left') first.brandt valuation,
      rightValid_of_sameBrandtSignature (Identity.mk right right') second.brandt valuation]

/-- The semantic half of section 2 is unrestrictedly true. This result
returns BOTH FACTOR SIGNATURES, deliberately not a rank040 derivation. -/
theorem commonInnerFactorSignature {left right : Word Nat}
    (witness : RankInverse left) (same : SameFactorSignature left right) :
    SameFactorSignature ((right ++ witness.inverse) ++ right) right := by
  apply sameFactorSignature_of_factorValid (Identity.mk ((right ++ witness.inverse) ++ right) right)
  · intro valuation
    have equality := leftValid_of_sameOccurrenceParity (Identity.mk left right) same.parity valuation
    simp only [Semigroup.eval_append]
    rw [← equality]
    exact (witness.model leftTable.semigroup leftModels valuation).1
  · intro valuation
    have equality := rightValid_of_sameBrandtSignature (Identity.mk left right) same.brandt valuation
    simp only [Semigroup.eval_append]
    rw [← equality]
    exact (witness.model rightTable.semigroup rightModels valuation).1

theorem commonOuterFactorSignature {left right : Word Nat}
    (witness : RankInverse left) (same : SameFactorSignature left right) :
    SameFactorSignature ((witness.inverse ++ right) ++ witness.inverse) witness.inverse := by
  apply sameFactorSignature_of_factorValid
    (Identity.mk ((witness.inverse ++ right) ++ witness.inverse) witness.inverse)
  · intro valuation
    have equality := leftValid_of_sameOccurrenceParity (Identity.mk left right) same.parity valuation
    simp only [Semigroup.eval_append]
    rw [← equality]
    exact (witness.model leftTable.semigroup leftModels valuation).2
  · intro valuation
    have equality := rightValid_of_sameBrandtSignature (Identity.mk left right) same.brandt valuation
    simp only [Semigroup.eval_append]
    rw [← equality]
    exact (witness.model rightTable.semigroup rightModels valuation).2

def brandtInverseValue (value : Fin 5) : Fin 5 :=
  if value = 1 then 2 else if value = 2 then 1 else value

theorem brandtValueInverse (value : Fin 5) :
    rightTable.semigroup.IsInverse value (brandtInverseValue value) := by
  unfold Semigroup.IsInverse
  decide +revert

theorem inverseBrandtValue {word : Word Nat} (witness : RankInverse word) (valuation : Nat → Fin 5) :
    rightTable.semigroup.eval valuation witness.inverse =
      brandtInverseValue (rightTable.semigroup.eval valuation word) := by
  exact Semigroup.IdempotentsCommute.inverse_unique
    (modelIdempotentsCommute rightTable.semigroup rightModels)
    (witness.model rightTable.semigroup rightModels valuation)
    (brandtValueInverse (rightTable.semigroup.eval valuation word))

/-- This is the exact all-valuations version of section 1(d), not just
the nonzero matrix-unit case e_ij -> e_ji. -/
theorem normalizedInverseBrandtValue (word inner : Word Nat)
    (reduces : Derives Rank040.basis ((word ++ inner) ++ word) word)
    (valuation : Nat → Fin 5) :
    rightTable.semigroup.eval valuation (normalize word inner) =
      brandtInverseValue (rightTable.semigroup.eval valuation word) :=
  inverseBrandtValue (normalizeWitness word inner reduces) valuation

def ZeroParity (word : Word Nat) : Prop :=
  ∀ letter, word.toList.count letter % 2 = 0

/-- Every valuation is included, with zero allowed. This is an intrinsic
diagonal Brandt term function, NOT a chosen ambient graph class. -/
def DiagonalBrandt (word : Word Nat) : Prop :=
  ∀ valuation : Nat → Fin 5,
    rightTable.semigroup.IsIdempotent (rightTable.semigroup.eval valuation word)

theorem zeroParityInverseProduct {word : Word Nat} (witness : RankInverse word) :
    ZeroParity (word ++ witness.inverse) := by
  intro letter
  have same := inverseParity witness letter
  simp only [Word.toList_append, List.count_append]
  omega

theorem zeroParityReverseInverseProduct {word : Word Nat} (witness : RankInverse word) :
    ZeroParity (witness.inverse ++ word) :=
  zeroParityInverseProduct (reverseWitness witness)

theorem diagonalBrandtInverseProduct {word : Word Nat} (witness : RankInverse word) :
    DiagonalBrandt (word ++ witness.inverse) := by
  intro valuation
  simpa only [Semigroup.eval_append] using
    (witness.model rightTable.semigroup rightModels valuation).mul_idempotent

theorem diagonalBrandtReverseInverseProduct {word : Word Nat} (witness : RankInverse word) :
    DiagonalBrandt (witness.inverse ++ word) :=
  diagonalBrandtInverseProduct (reverseWitness witness)

theorem zeroParityOfSignature {left right : Word Nat}
    (same : SameFactorSignature left right) (zero : ZeroParity left) : ZeroParity right := by
  intro letter
  exact (same.parity letter).symm.trans (zero letter)

theorem diagonalBrandtOfSignature {left right : Word Nat}
    (same : SameFactorSignature left right) (diagonal : DiagonalBrandt left) : DiagonalBrandt right := by
  intro valuation
  have equality := rightValid_of_sameBrandtSignature (Identity.mk left right) same.brandt valuation
  rw [← equality]
  exact diagonal valuation

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.NormalizedInverse
