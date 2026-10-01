import SemigroupBasis.CoRoots.Order6LeeZhang23_12FactorNormalization
import SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalBridges
import SemigroupBasis.CoRoots.Order6LeeZhang23_13Padding

/-!
# Lee--Zhang Lemma 23.12 word normalization

This module is the word-level assembly for the simple-endpoint branch of
Proposition 23.9.  The factor normalizer supplies a list derivation to the
deterministic canonical list.  Nonemptiness and `ListDerives.from_cons` lift
that derivation back to semigroup words.  Equal Lee--Zhang signatures give
literally equal canonical words, so the left and right normalizations join.

The final-simplicity argument remains in the public callback contract used
by Lemma 23.13.  The current factor normalizer needs only the simple head;
the final factor is kept fixed by its reversed-inventory construction.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_12Normalization

open SemigroupBasis
open Order6LeeZhang23_9Syntax
open Order6LeeZhang23_9Invariant
open Order6LeeZhang23_9Moves
open Order6LeeZhang23_9CanonicalData
open Order6LeeZhang23_9InventoryBridge
open Order6LeeZhang23_9CanonicalBridges
open Order6LeeZhang23_12FactorNormalization
open Order6LeeZhang23_13Padding

/-! ## Signature transfers needed by the two normalizations -/

private theorem nonSimple_right_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (leftNonSimple :
      ∃ marker, 2 ≤ left.toList.count marker) :
    ∃ marker, 2 ≤ right.toList.count marker := by
  obtain ⟨marker, leftMultiple⟩ := leftNonSimple
  refine ⟨marker, ?_⟩
  have cappedEqual := same.reversedS5_402.capped marker
  change
    Nat.min 2 (left.reverse.toList.count marker) =
      Nat.min 2 (right.reverse.toList.count marker) at cappedEqual
  simp only [Word.toList_reverse, List.count_reverse] at cappedEqual
  have rightCapped :
      Nat.min 2 (right.toList.count marker) = 2 :=
    cappedEqual.symm.trans (Nat.min_eq_left leftMultiple)
  by_cases rightMultiple : 2 ≤ right.toList.count marker
  · exact rightMultiple
  · have rightBelow : right.toList.count marker < 2 := by omega
    have rightMin :
        Nat.min 2 (right.toList.count marker) =
          right.toList.count marker :=
      Nat.min_eq_right (Nat.le_of_lt rightBelow)
    have rightCountEq : right.toList.count marker = 2 :=
      rightMin.symm.trans rightCapped
    omega

private theorem rightHeadSimple_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right)
    (leftHeadSimple :
      S5_402.GloballySimple left left.head) :
    S5_402.GloballySimple right right.head := by
  have published :=
    samePublishedLeeZhang23_9Signature_of_compact same
  have rightSimpleAtLeftHead :
      S5_402.GloballySimple right left.head :=
    (published.globallySimple left.head).mp leftHeadSimple
  simpa [published.head] using rightSimpleAtLeftHead

/-! ## Exact list-to-word lift -/

private theorem derivesCanonicalWord_of_head_simple
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head)
    (inventory : ReversedInventoryDecomposition word) :
    Derives B4Basis word (canonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :
          B4ListDerives
            (head :: tail)
            (canonicalList (Word.mk head tail)) := by
        simpa [Word.toList] using
          listDerivesCanonicalList_of_head_simple
            (Word.mk head tail) headSimple inventory
      obtain
          ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            canonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        rw [canonicalWord_toList]
        simpa [S5_107.listWordOfCons] using targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

/-! ## The simple-endpoint consumer exported to Lemma 23.13 -/

/-- Equal Lee--Zhang signatures with a non-simple letter normalize to the
same canonical word.  This is the exact callback consumed by the endpoint
padding theorem. -/
theorem derivesOfSameLeeZhang23_9Signature_of_simpleEndpoints :
    SimpleEndpointNormalizer := by
  intro left right same leftNonSimple leftHeadSimple _leftFinalSimple
  have rightNonSimple :=
    nonSimple_right_of_sameSignature same leftNonSimple
  have rightHeadSimple :=
    rightHeadSimple_of_sameSignature same leftHeadSimple
  obtain ⟨leftInventory⟩ :=
    exists_reversedInventoryDecomposition left leftNonSimple
  obtain ⟨rightInventory⟩ :=
    exists_reversedInventoryDecomposition right rightNonSimple
  have leftNormalized :
      Derives B4Basis left (canonicalWord left) :=
    derivesCanonicalWord_of_head_simple
      left leftHeadSimple leftInventory
  have rightNormalized :
      Derives B4Basis right (canonicalWord right) :=
    derivesCanonicalWord_of_head_simple
      right rightHeadSimple rightInventory
  rw [canonicalWord_eq_of_sameSignature same] at leftNormalized
  exact leftNormalized.trans rightNormalized.symm

end SemigroupBasis.CoRoots.Order6LeeZhang23_12Normalization
