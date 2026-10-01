import SemigroupBasis.CoRoots.Order6LeeZhang23_12Normalization

/-!
# Completeness of the Lee--Zhang Proposition 23.9 basis

The non-simple branch is the direct combination of the simple-endpoint
normalizer and Lemma 23.13 endpoint padding.  If no letter is multiple, the
canonical list is literally the source list on both sides; signature equality
then makes the two source words equal, so reflexivity closes the branch.

The resulting signature theorem discharges the exact product-hull
derivational obligation for `S2_4 x S5_402^op`.  Every derivation remains in
the published four-law basis `B4Basis`.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Completeness

open SemigroupBasis
open Order6LeeZhang23_9Syntax
open Order6LeeZhang23_9Moves
open Order6LeeZhang23_9Invariant
open Order6LeeZhang23_9CanonicalData
open Order6LeeZhang23_9CanonicalBridges
open Order6LeeZhang23_12Normalization
open Order6LeeZhang23_13Padding

/-- Absence of a multiple letter transfers across the compact Lee--Zhang
signature. -/
private theorem noMultiples_right_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (leftNoMultiples :
      ¬ ∃ marker, 2 ≤ left.toList.count marker) :
    ¬ ∃ marker, 2 ≤ right.toList.count marker := by
  rintro ⟨marker, rightMultiple⟩
  apply leftNoMultiples
  refine ⟨marker, ?_⟩
  have cappedEqual := same.reversedS5_402.capped marker
  change
    Nat.min 2 (left.reverse.toList.count marker) =
      Nat.min 2 (right.reverse.toList.count marker) at cappedEqual
  simp only [Word.toList_reverse, List.count_reverse] at cappedEqual
  have leftCapped :
      Nat.min 2 (left.toList.count marker) = 2 :=
    cappedEqual.trans (Nat.min_eq_left rightMultiple)
  by_cases leftMultiple : 2 ≤ left.toList.count marker
  · exact leftMultiple
  · have leftBelow : left.toList.count marker < 2 := by omega
    have leftMin :
        Nat.min 2 (left.toList.count marker) =
          left.toList.count marker :=
      Nat.min_eq_right (Nat.le_of_lt leftBelow)
    have leftEqualsTwo : left.toList.count marker = 2 :=
      leftMin.symm.trans leftCapped
    omega

/-- Equal compact Lee--Zhang signatures are derivably equal in the published
four-law basis, in the original orientation. -/
theorem derivesOfSameLeeZhang23_9Signature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    Derives B4Basis left right := by
  by_cases leftNonSimple :
      ∃ marker, 2 ≤ left.toList.count marker
  · exact derives_of_sameLeeZhang23_9Signature_of_nonSimple
      derivesOfSameLeeZhang23_9Signature_of_simpleEndpoints
      same leftNonSimple
  · have rightNoMultiples :=
      noMultiples_right_of_sameSignature same leftNonSimple
    have leftCanonical :=
      canonicalList_eq_toList_of_no_multiples left leftNonSimple
    have rightCanonical :=
      canonicalList_eq_toList_of_no_multiples right rightNoMultiples
    have canonicalEqual :=
      canonicalList_eq_of_sameSignature same
    have listsEqual : left.toList = right.toList := by
      calc
        left.toList = canonicalList left := leftCanonical.symm
        _ = canonicalList right := canonicalEqual
        _ = right.toList := rightCanonical
    have wordsEqual : left = right :=
      Word.toList_injective listsEqual
    subst right
    exact Derives.refl _

/-- The published B4 derivation theorem discharges the exact product-hull
obligation using only the factor-validity signature bridge. -/
theorem derivationalObligation :
    SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.DerivationalObligation := by
  intro identity leftValid rightValid
  exact derivesOfSameLeeZhang23_9Signature
    (sameLeeZhang23_9Signature_of_factorValidity
      identity leftValid rightValid)

/-- The published four laws are a basis for the exact product hull. -/
theorem publishedProductBasisFor :
    BasisFor
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.P
      B4Basis :=
  SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.prod_basisFor_of_obligation
    derivationalObligation

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Completeness
