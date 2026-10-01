import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_381RelativeLift
import SemigroupBasis.CoRoots.S5_381Family
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Unrestricted Layer-C transfer for `S3_15^op x S5_381`

Validity in the left factor fixes the final variable.  The complete
`S5_381` derivation is therefore lifted relative to that common final.
A globally simple final is stripped by the exact table's right reductivity;
a repeated final is duplicated, used as a suffix guard, and contracted.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_381

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_17bbc703ba9dbee0.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup

private theorem targetBasis_eq_block :
    targetBasis =
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381 := by
  decide

theorem modelsLeft : Models leftFactor targetBasis := by
  rw [targetBasis_eq_block]
  exact
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381_left_models

theorem modelsRight : Models rightFactor targetBasis := by
  rw [targetBasis_eq_block]
  exact
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381_right_models

/-! ## Final-coordinate syntax -/

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

private theorem splitFinal_not_mem_prefix_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    (splitPrefixFinal word).2 ∉ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  have countOne' :
      word.toList.count (splitPrefixFinal word).2 = 1 := by
    simpa [finalEq] using countOne
  rw [toList_eq_splitPrefixFinal, List.count_append] at countOne'
  simp only [List.count_singleton_self] at countOne'
  have prefixCount :
      (splitPrefixFinal word).1.count (splitPrefixFinal word).2 = 0 := by
    omega
  exact List.count_eq_zero.mp prefixCount

private theorem splitFinal_mem_prefix_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.final ≠ 1) :
    (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 := by
  have finalEq := split_final_eq word
  have countNotOne' :
      word.toList.count (splitPrefixFinal word).2 ≠ 1 := by
    simpa [finalEq] using countNotOne
  have countShape :
      word.toList.count (splitPrefixFinal word).2 =
        (splitPrefixFinal word).1.count (splitPrefixFinal word).2 + 1 := by
    rw [toList_eq_splitPrefixFinal, List.count_append]
    simp
  have positive :
      0 < (splitPrefixFinal word).1.count (splitPrefixFinal word).2 := by
    omega
  exact List.count_pos_iff.mp positive

/-! ## Simple-final consequences of the exact S5 signature -/

private theorem finalCountOne_of_sameSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1) :
    right.toList.count right.final = 1 := by
  have leftCapped :
      SemigroupBasis.CoRoots.S5_107.cappedMultiplicity left left.final = 1 :=
    (SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff
      left left.final).2 leftSimple
  have rightCappedAtLeft :
      SemigroupBasis.CoRoots.S5_107.cappedMultiplicity right left.final = 1 :=
    (same.capped left.final).symm ▸ leftCapped
  have rightCapped :
      SemigroupBasis.CoRoots.S5_107.cappedMultiplicity right right.final = 1 := by
    simpa only [finalEq] using rightCappedAtLeft
  exact
    (SemigroupBasis.CoRoots.S5_107.cappedMultiplicity_eq_one_iff
      right right.final).1 rightCapped

private theorem finalCountOneIff
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right)
    (finalEq : left.final = right.final) :
    left.toList.count left.final = 1 ↔
      right.toList.count right.final = 1 := by
  constructor
  · exact finalCountOne_of_sameSignature same finalEq
  · exact finalCountOne_of_sameSignature same.symm finalEq.symm

private theorem splitPrefix_nil_of_sameSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (rightSimple : right.toList.count right.final = 1)
    (leftPrefixEmpty : (splitPrefixFinal left).1 = []) :
    (splitPrefixFinal right).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightPrefixMember
  have rightMember : letter ∈ right.toList := by
    rw [toList_eq_splitPrefixFinal]
    exact List.mem_append_left _ rightPrefixMember
  have leftMember : letter ∈ left.toList :=
    (same.support letter).2 rightMember
  have letterIsLeftFinal : letter = (splitPrefixFinal left).2 := by
    rw [toList_eq_splitPrefixFinal, leftPrefixEmpty] at leftMember
    simpa using leftMember
  have splitFinals :
      (splitPrefixFinal left).2 = (splitPrefixFinal right).2 :=
    (split_final_eq left).trans <|
      finalEq.trans (split_final_eq right).symm
  have letterIsRightFinal : letter = (splitPrefixFinal right).2 :=
    letterIsLeftFinal.trans splitFinals
  have rightFinalAbsent :=
    splitFinal_not_mem_prefix_of_count_one right rightSimple
  exact rightFinalAbsent (letterIsRightFinal ▸ rightPrefixMember)

private theorem splitPrefix_nil_iff_of_sameSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1) :
    (splitPrefixFinal left).1 = [] ↔
      (splitPrefixFinal right).1 = [] := by
  constructor
  · exact splitPrefix_nil_of_sameSignature
      same finalEq rightSimple
  · exact splitPrefix_nil_of_sameSignature
      same.symm finalEq.symm leftSimple

/-! ## Right-reductive stripping in the exact order-five factor -/

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S) :
    forall (letters : List Nat) (initial : S),
      (forall letter, letter ∈ letters ->
        leftValuation letter = rightValuation letter) ->
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S)
    (word : Word Nat)
    (agree :
      forall letter, letter ∈ word.toList ->
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

theorem s5_381_right_reductive
    (left right : Fin 5)
    (equalRows : forall marker : Fin 5,
      rightFactor.mul left marker = rightFactor.mul right marker) :
    left = right := by
  revert left right
  decide

theorem s5_381_prefix_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  apply s5_381_right_reductive
  intro marker
  let lifted : Nat -> Fin 5 :=
    fun letter => if letter = final then marker else valuation letter
  have leftAgree :
      rightFactor.eval valuation left =
        rightFactor.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree :
      rightFactor.eval valuation right =
        rightFactor.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal : lifted final = marker := by
    simp [lifted]
  rw [liftedFinal] at evaluated
  calc
    rightFactor.mul (rightFactor.eval valuation left) marker =
        rightFactor.mul (rightFactor.eval lifted left) marker :=
      congrArg (fun value => rightFactor.mul value marker) leftAgree
    _ = rightFactor.mul (rightFactor.eval lifted right) marker :=
      evaluated
    _ = rightFactor.mul (rightFactor.eval valuation right) marker :=
      congrArg (fun value => rightFactor.mul value marker)
        rightAgree.symm

private theorem listWordOfCons_append_final
    (head : Nat) (tail : List Nat) (final : Nat) :
    SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail ++
        Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

/-! ## Duplicating a repeated final -/

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private theorem derives_of_listDerives_toList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives targetBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private theorem listDerivesPowerExpansion (letter : Nat) :
    ListDerives [letter, letter] [letter, letter, letter] := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesPower (Word.singleton letter)))

private theorem listDerivesRightDuplication
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesRightDuplication
        (Word.singleton letter)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons gapHead gapTail)))

private theorem listDerivesDuplicateFinal
    (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final]) (stem ++ [final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesPowerExpansion final))
  | cons gapHead gapTail =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesRightDuplication final gapHead gapTail))

private theorem derivesDuplicateFinal
    (word : Word Nat)
    (seen : word.final ∈ (splitPrefixFinal word).1) :
    Derives targetBasis word
      (word ++ Word.singleton word.final) := by
  have listed :=
    listDerivesDuplicateFinal
      (splitPrefixFinal word).1 word.final seen
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_singleton,
    toList_eq_splitPrefixFinal, split_final_eq]
  simpa [List.append_assoc] using listed

/-! ## Unrestricted relative deduction -/

theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_381Family.S5_381.basis_complete.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.S5_381FamilyInvariant.S5_381.valid_sameSignature
      identity rightValid
  have finalEq : identity.lhs.final = identity.rhs.final :=
    (SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
      identity leftValid).final_eq
  have countIff := finalCountOneIff same finalEq
  by_cases leftSimple :
      identity.lhs.toList.count identity.lhs.final = 1
  · have rightSimple :
        identity.rhs.toList.count identity.rhs.final = 1 :=
      countIff.mp leftSimple
    have prefixesEmpty :=
      splitPrefix_nil_iff_of_sameSignature
        same finalEq leftSimple rightSimple
    cases leftPrefix : (splitPrefixFinal identity.lhs).1 with
    | nil =>
        have rightPrefix : (splitPrefixFinal identity.rhs).1 = [] :=
          prefixesEmpty.mp leftPrefix
        have leftReconstructed := wordOfPrefixFinal_split identity.lhs
        have rightReconstructed := wordOfPrefixFinal_split identity.rhs
        rw [leftPrefix] at leftReconstructed
        rw [rightPrefix] at rightReconstructed
        simp only [wordOfPrefixFinal_nil] at leftReconstructed
        simp only [wordOfPrefixFinal_nil] at rightReconstructed
        have splitFinals :
            (splitPrefixFinal identity.lhs).2 =
              (splitPrefixFinal identity.rhs).2 :=
          (split_final_eq identity.lhs).trans <|
            finalEq.trans (split_final_eq identity.rhs).symm
        rw [← leftReconstructed, ← rightReconstructed, splitFinals]
        exact Derives.refl _
    | cons leftHead leftTail =>
        cases rightPrefix : (splitPrefixFinal identity.rhs).1 with
        | nil =>
            have impossible := prefixesEmpty.mpr rightPrefix
            rw [leftPrefix] at impossible
            contradiction
        | cons rightHead rightTail =>
            let leftPrefixWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                leftHead leftTail
            let rightPrefixWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                rightHead rightTail
            let final := (splitPrefixFinal identity.lhs).2
            have splitFinals :
                (splitPrefixFinal identity.lhs).2 =
                  (splitPrefixFinal identity.rhs).2 :=
              (split_final_eq identity.lhs).trans <|
                finalEq.trans (split_final_eq identity.rhs).symm
            have leftFinalAbsentRaw :=
              splitFinal_not_mem_prefix_of_count_one
                identity.lhs leftSimple
            rw [leftPrefix] at leftFinalAbsentRaw
            have leftFinalAbsent : final ∉ leftPrefixWord.toList := by
              simpa [final, leftPrefixWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using leftFinalAbsentRaw
            have rightFinalAbsentRaw :=
              splitFinal_not_mem_prefix_of_count_one
                identity.rhs rightSimple
            rw [rightPrefix] at rightFinalAbsentRaw
            have rightFinalAbsent : final ∉ rightPrefixWord.toList := by
              simpa [final, splitFinals, rightPrefixWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using rightFinalAbsentRaw
            have leftShape :
                leftPrefixWord ++ Word.singleton final = identity.lhs := by
              calc
                leftPrefixWord ++ Word.singleton final =
                    wordOfPrefixFinal (leftHead :: leftTail) final := by
                  simpa [leftPrefixWord] using
                    listWordOfCons_append_final leftHead leftTail final
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.lhs).1
                    (splitPrefixFinal identity.lhs).2 := by
                  rw [leftPrefix]
                _ = identity.lhs := wordOfPrefixFinal_split identity.lhs
            have rightShape :
                rightPrefixWord ++ Word.singleton final = identity.rhs := by
              calc
                rightPrefixWord ++ Word.singleton final =
                    rightPrefixWord ++ Word.singleton
                      (splitPrefixFinal identity.rhs).2 := by
                  simp only [final, splitFinals]
                _ = wordOfPrefixFinal
                    (rightHead :: rightTail)
                    (splitPrefixFinal identity.rhs).2 := by
                  simpa [rightPrefixWord] using
                    listWordOfCons_append_final rightHead rightTail
                      (splitPrefixFinal identity.rhs).2
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.rhs).1
                    (splitPrefixFinal identity.rhs).2 := by
                  rw [rightPrefix]
                _ = identity.rhs := wordOfPrefixFinal_split identity.rhs
            have wholeValid :
                (Identity.mk
                  (leftPrefixWord ++ Word.singleton final)
                  (rightPrefixWord ++ Word.singleton final)).SatisfiedBy
                    rightFactor := by
              simpa only [leftShape, rightShape] using rightValid
            have prefixValid :=
              s5_381_prefix_valid final leftPrefixWord rightPrefixWord
                leftFinalAbsent rightFinalAbsent wholeValid
            have prefixDerivation :=
              SemigroupBasis.CoRoots.S5_381Family.S5_381.basis_complete.2
                (Identity.mk leftPrefixWord rightPrefixWord) prefixValid
            have lifted :=
              liftS5_381UnderSuffixIdentity
                prefixDerivation (Word.singleton final)
            simpa only [leftShape, rightShape] using lifted
  · have rightNotSimple :
        identity.rhs.toList.count identity.rhs.final ≠ 1 := by
      intro rightSimple
      exact leftSimple (countIff.mpr rightSimple)
    have leftFinalSeen :
        identity.lhs.final ∈ (splitPrefixFinal identity.lhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_prefix_of_count_ne_one identity.lhs leftSimple
    have rightFinalSeen :
        identity.rhs.final ∈ (splitPrefixFinal identity.rhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_prefix_of_count_ne_one identity.rhs rightNotSimple
    have leftDuplicate :=
      derivesDuplicateFinal identity.lhs leftFinalSeen
    have rightDuplicate :=
      derivesDuplicateFinal identity.rhs rightFinalSeen
    have lifted :=
      liftS5_381UnderSuffixIdentity sourceDerivation
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

/-- Unrestricted intersection basis for the exact Layer-B block. -/
def intersectionBasisS5_381 :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_381 := by
  simpa only [targetBasis_eq_block] using displayedIntersectionBasis

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_381
