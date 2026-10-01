import SemigroupBasis.CoRoots.Order6L3Root7.GeneratedAuxiliary
import SemigroupBasis.CoRoots.Order6L3Root7.GeneratedCollapse
import SemigroupBasis.CoRoots.Order6L3Root7.GeneratedFresh
import SemigroupBasis.CoRoots.Order6L3Root7.GeneratedSecond
import SemigroupBasis.CoRoots.Order6L3Root3.Common
import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Subdirect

/-!
# Unrestricted FCLP completeness for `S2_2 × S4_110`

The normal-band factor fixes the first letter, final letter, and support.  The
cyclic factor fixes every multiplicity modulo two.  We triple-expand each word,
remove its common endpoints, transport the complete commutative-parity
derivation through those fixed endpoint contexts, and contract again.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3Root7

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L3Root3

/-! ## Fixed-endpoint transport of commutative parity -/

/-- Lift a commutative-parity derivation through two nonempty endpoint blocks.
The explicit substitution parameter makes the `Derives.subst` case composable:
the endpoints themselves are never substituted. -/
theorem liftParityDerivation
    {left right : Word Nat}
    (derivation :
      Derives commutativeParityBasis left right)
    (initial final : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basis
      (initial ++ (left.bind substitution ++ final))
      (initial ++ (right.bind substitution ++ final)) := by
  induction derivation generalizing initial final substitution with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have expanded :=
          Derives.appendRight
            (Derives.prepend initial
              (derivesLaw00Power (substitution 0)))
            final
        simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.singleton, Word.append, Word.append_assoc] using expanded
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          derivesAuxiliaryShape000 final initial
            (substitution 0) (substitution 1)
  | refl word =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih initial final substitution)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans
        (ih₁ initial final substitution)
        (ih₂ initial final substitution)
  | prepend prefixWord _ ih =>
      have lifted :=
        ih (initial ++ prefixWord.bind substitution) final substitution
      simpa [bind_append, Word.append_assoc] using lifted
  | appendRight _ suffix ih =>
      have lifted :=
        ih initial (suffix.bind substitution ++ final) substitution
      simpa [bind_append, Word.append_assoc] using lifted
  | subst _ inner ih =>
      have lifted :=
        ih initial final
          (fun letter => (inner letter).bind substitution)
      simpa [bind_bind] using lifted

/-! ## A nonempty triple interior -/

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => Word.mk head tail

@[simp]
private theorem toList_wordOfListOr_of_ne_nil
    (fallback : Nat) {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfListOr fallback letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

def finalLetter (word : Word Nat) : Nat :=
  word.tail.getLastD word.head

/-- After tripling a word, remove the first letter of the first copy and the
last letter of the third copy.  The complete second copy remains inside. -/
def tripleMiddleList (word : Word Nat) : List Nat :=
  word.tail ++ word.toList ++ word.toList.dropLast

theorem tripleMiddleList_ne_nil (word : Word Nat) :
    tripleMiddleList word ≠ [] := by
  cases word with
  | mk head tail =>
      simp [tripleMiddleList, Word.toList]

def tripleMiddleWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (tripleMiddleList word)

@[simp]
theorem tripleMiddleWord_toList (word : Word Nat) :
    (tripleMiddleWord word).toList = tripleMiddleList word := by
  exact toList_wordOfListOr_of_ne_nil word.head
    (tripleMiddleList_ne_nil word)

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

theorem tripleEndpointDecomposition (word : Word Nat) :
    word ++ (word ++ word) =
      Word.singleton word.head ++
        (tripleMiddleWord word ++
          Word.singleton (finalLetter word)) := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_append,
    Word.toList_append, Word.toList_append,
    Word.toList_singleton,
    tripleMiddleWord_toList, Word.toList_singleton]
  cases word with
  | mk head tail =>
      simp only [Word.toList, tripleMiddleList, finalLetter]
      rw [List.cons_append]
      simp only [List.append_assoc]
      rw [dropLast_append_final head tail]
      rfl

private theorem tripleMiddle_count_equation
    (tested : Nat) (word : Word Nat) :
    [word.head].count tested +
          (tripleMiddleList word).count tested +
          [finalLetter word].count tested =
      word.toList.count tested +
          word.toList.count tested +
          word.toList.count tested := by
  have listDecomposed :=
    congrArg Word.toList (tripleEndpointDecomposition word)
  rw [Word.toList_append, Word.toList_append,
    Word.toList_append, Word.toList_append,
    Word.toList_singleton, tripleMiddleWord_toList,
    Word.toList_singleton] at listDecomposed
  have decomposed :=
    congrArg (fun letters : List Nat => letters.count tested)
      listDecomposed
  simp [List.count_cons, List.count_append,
    Nat.add_assoc] at decomposed ⊢
  omega

theorem tripleMiddle_mem_iff
    (tested : Nat) (word : Word Nat) :
    tested ∈ tripleMiddleList word ↔ tested ∈ word.toList := by
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  have equation := tripleMiddle_count_equation tested word
  have headBound : [word.head].count tested ≤ 1 := by
    simpa using
      (List.count_le_length (a := tested) (l := [word.head]))
  have finalBound : [finalLetter word].count tested ≤ 1 := by
    simpa using
      (List.count_le_length (a := tested) (l := [finalLetter word]))
  omega

theorem tripleMiddle_parity_eq
    {left right : Word Nat}
    (heads : left.head = right.head)
    (finals : finalLetter left = finalLetter right)
    (parity :
      ∀ tested,
        left.toList.count tested % 2 =
          right.toList.count tested % 2) :
    ∀ tested,
      (tripleMiddleList left).count tested % 2 =
        (tripleMiddleList right).count tested % 2 := by
  intro tested
  have leftEquation := tripleMiddle_count_equation tested left
  have rightEquation := tripleMiddle_count_equation tested right
  have headCount :
      [left.head].count tested = [right.head].count tested := by
    rw [heads]
  have finalCount :
      [finalLetter left].count tested =
        [finalLetter right].count tested := by
    rw [finals]
  have wholeParity := parity tested
  omega

/-! ## Interior normalization and unrestricted factor intersection -/

theorem parityDerivesOfSupportParity
    (left right : Word Nat)
    (support :
      ∀ tested, tested ∈ left.toList ↔ tested ∈ right.toList)
    (parity :
      ∀ tested,
        left.toList.count tested % 2 =
          right.toList.count tested % 2) :
    Derives commutativeParityBasis left right := by
  have reducedPerm :
      (positiveParityReduce left.toList).Perm
        (positiveParityReduce right.toList) :=
    positiveParityReduce_perm support parity
  have leftNormal := positiveParityDerivesNormal left
  have rightNormal := positiveParityDerivesNormal right
  cases hl : positiveParityReduce left.toList with
  | nil =>
      have present :
          left.head ∈ positiveParityReduce left.toList :=
        (mem_positiveParityReduce_iff _ _).mpr (by
          simp [Word.toList])
      simp [hl] at present
  | cons x xs =>
      cases hr : positiveParityReduce right.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at leftNormal
          rw [hr] at rightNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans leftNormal <|
            Derives.trans
              (parityDerivesPermutation
                (⟨x, xs⟩ : Word Nat)
                (⟨y, ys⟩ : Word Nat)
                reducedPerm)
              (Derives.symm rightNormal)

theorem derivesOfSameFCLP
    (left right : Word Nat)
    (heads : left.head = right.head)
    (finals : finalLetter left = finalLetter right)
    (support :
      ∀ tested, tested ∈ left.toList ↔ tested ∈ right.toList)
    (parity :
      ∀ tested,
        left.toList.count tested % 2 =
          right.toList.count tested % 2) :
    Derives basis left right := by
  have middleSupport :
      ∀ tested,
        tested ∈ (tripleMiddleWord left).toList ↔
          tested ∈ (tripleMiddleWord right).toList := by
    intro tested
    rw [tripleMiddleWord_toList, tripleMiddleWord_toList,
      tripleMiddle_mem_iff, tripleMiddle_mem_iff]
    exact support tested
  have middleParity :
      ∀ tested,
        (tripleMiddleWord left).toList.count tested % 2 =
          (tripleMiddleWord right).toList.count tested % 2 := by
    intro tested
    rw [tripleMiddleWord_toList, tripleMiddleWord_toList]
    exact tripleMiddle_parity_eq heads finals parity tested
  have middleDerivation :=
    parityDerivesOfSupportParity
      (tripleMiddleWord left) (tripleMiddleWord right)
      middleSupport middleParity
  have lifted :=
    liftParityDerivation middleDerivation
      (Word.singleton left.head)
      (Word.singleton (finalLetter left))
      Word.singleton
  have lifted' :
      Derives basis
        (Word.singleton left.head ++
          (tripleMiddleWord left ++
            Word.singleton (finalLetter left)))
        (Word.singleton right.head ++
          (tripleMiddleWord right ++
            Word.singleton (finalLetter right))) := by
    simpa [bind_singleton, heads, finals] using lifted
  have leftExpansion := derivesLaw00Power left
  have rightContraction := Derives.symm (derivesLaw00Power right)
  exact Derives.trans leftExpansion <|
    Derives.trans
      (by
        rw [tripleEndpointDecomposition]
        exact lifted')
      (by
        simpa [tripleEndpointDecomposition] using rightContraction)

theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_110.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  have normalValid :
      identity.SatisfiedBy normalBandFour.semigroup := by
    simpa [SemigroupBasis.Generated.S4_110.table] using s4Valid
  exact derivesOfSameFCLP identity.lhs identity.rhs
    (normalBandValid_head_eq identity normalValid)
    (normalBandValid_final_eq identity normalValid)
    (normalBandValid_support_eq identity normalValid)
    (cyclicValid_parity_eq identity cyclicValid)

/-- The exact 15 msg-0600 laws form the unrestricted identity-theory
intersection of `S2_2` and `S4_110`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.S4_110.table.semigroup
      basis where
  leftModels := basis_s2_2_models
  rightModels := basis_s4_110_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L3Root7
