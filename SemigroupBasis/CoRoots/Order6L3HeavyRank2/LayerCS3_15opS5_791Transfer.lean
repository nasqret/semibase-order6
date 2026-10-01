import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_791FinalSignature
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_791RelativeLift
import SemigroupBasis.CoRoots.S5_791Family
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Unrestricted Layer-C transfer for `S3_15^op x S5_791`

Validity in the left factor fixes the final variable.  Equality of the exact
`S5_791` ordered-component signature preserves whether that final is globally
simple.  A simple final is stripped by right reductivity and restored with the
relative lift; a repeated final is duplicated, used as the suffix guard, and
contracted.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_791

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_791.table.semigroup

theorem modelsLeft : Models leftFactor targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_791_left_models

theorem modelsRight : Models rightFactor targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_15opS5_791_right_models

/-! ## Empty-prefix alignment for a globally simple final -/

private theorem splitPrefix_nil_of_sameLastSupport
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.SameLastSupport left right)
    (rightSimple : right.toList.count right.final = 1)
    (leftPrefixEmpty : (splitPrefixFinal left).1 = []) :
    (splitPrefixFinal right).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightPrefixMember
  have rightMember : letter ∈ right.toList := by
    rw [toList_eq_splitPrefixFinal]
    exact List.mem_append_left _ rightPrefixMember
  have leftMember : letter ∈ left.toList :=
    (same.support_eq letter).2 rightMember
  have letterIsLeftFinal : letter = (splitPrefixFinal left).2 := by
    rw [toList_eq_splitPrefixFinal, leftPrefixEmpty] at leftMember
    simpa using leftMember
  have splitFinals :
      (splitPrefixFinal left).2 = (splitPrefixFinal right).2 :=
    (splitFinal_eq left).trans <|
      same.final_eq.trans (splitFinal_eq right).symm
  have letterIsRightFinal : letter = (splitPrefixFinal right).2 :=
    letterIsLeftFinal.trans splitFinals
  have rightFinalAbsent :=
    splitFinal_not_mem_prefix_of_count_one right rightSimple
  exact rightFinalAbsent (letterIsRightFinal ▸ rightPrefixMember)

private theorem splitPrefix_nil_iff_of_sameLastSupport
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.SameLastSupport left right)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1) :
    (splitPrefixFinal left).1 = [] ↔
      (splitPrefixFinal right).1 = [] := by
  constructor
  · exact splitPrefix_nil_of_sameLastSupport
      same rightSimple
  · exact splitPrefix_nil_of_sameLastSupport
      same.symm leftSimple

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

theorem s5_791_right_reductive
    (left right : Fin 5)
    (equalRows : forall marker : Fin 5,
      rightFactor.mul left marker = rightFactor.mul right marker) :
    left = right := by
  revert left right
  decide

theorem s5_791_prefix_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  apply s5_791_right_reductive
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

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def xx : Word Nat := w 0 [0]
private def xxx : Word Nat := w 0 [0, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xyxx : Word Nat := w 0 [1, 0, 0]

private theorem targetPower :
    Derives targetBasis xx xxx :=
  Derives.fromBasis (e := Identity.mk xx xxx) (by decide)

private theorem targetRightDuplication :
    Derives targetBasis xyx xyxx :=
  Derives.fromBasis (e := Identity.mk xyx xyxx) (by decide)

private def instantiateWords
    (first second : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

private theorem derivesPower (word : Word Nat) :
    Derives targetBasis (word ++ word) ((word ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetPower (instantiateWords word word)
  simpa [xx, xxx, w, instantiateWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

private theorem derivesRightDuplication (word middle : Word Nat) :
    Derives targetBasis
      ((word ++ middle) ++ word)
      (((word ++ middle) ++ word) ++ word) := by
  have substituted :=
    Derives.subst targetRightDuplication (instantiateWords word middle)
  simpa [xyx, xyxx, w, instantiateWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

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
    toList_eq_splitPrefixFinal, splitFinal_eq]
  simpa [List.append_assoc] using listed

/-! ## Unrestricted relative deduction -/

theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_791Family.S5_791.basis_complete.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.S5_791FamilyInvariant.S5_791.valid_sameSignature
      identity rightValid
  have sameLastSupport :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
      identity leftValid
  have finalEq : identity.lhs.final = identity.rhs.final :=
    sameLastSupport.final_eq
  have countIff := finalCountOneIff same finalEq
  by_cases leftSimple :
      identity.lhs.toList.count identity.lhs.final = 1
  · have rightSimple :
        identity.rhs.toList.count identity.rhs.final = 1 :=
      countIff.mp leftSimple
    have prefixesEmpty :=
      splitPrefix_nil_iff_of_sameLastSupport
        sameLastSupport leftSimple rightSimple
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
          (splitFinal_eq identity.lhs).trans <|
            finalEq.trans (splitFinal_eq identity.rhs).symm
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
              (splitFinal_eq identity.lhs).trans <|
                finalEq.trans (splitFinal_eq identity.rhs).symm
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
              s5_791_prefix_valid final leftPrefixWord rightPrefixWord
                leftFinalAbsent rightFinalAbsent wholeValid
            have prefixDerivation :=
              SemigroupBasis.CoRoots.S5_791Family.S5_791.basis_complete.2
                (Identity.mk leftPrefixWord rightPrefixWord) prefixValid
            have lifted :=
              liftS5_791UnderSuffixIdentity
                prefixDerivation (Word.singleton final)
            simpa only [leftShape, rightShape] using lifted
  · have rightNotSimple :
        identity.rhs.toList.count identity.rhs.final ≠ 1 := by
      intro rightSimple
      exact leftSimple (countIff.mpr rightSimple)
    have leftFinalSeen :
        identity.lhs.final ∈ (splitPrefixFinal identity.lhs).1 := by
      simpa only [splitFinal_eq] using
        splitFinal_mem_prefix_of_count_ne_one identity.lhs leftSimple
    have rightFinalSeen :
        identity.rhs.final ∈ (splitPrefixFinal identity.rhs).1 := by
      simpa only [splitFinal_eq] using
        splitFinal_mem_prefix_of_count_ne_one
          identity.rhs rightNotSimple
    have leftDuplicate :=
      derivesDuplicateFinal identity.lhs leftFinalSeen
    have rightDuplicate :=
      derivesDuplicateFinal identity.rhs rightFinalSeen
    have lifted :=
      liftS5_791UnderSuffixIdentity sourceDerivation
        (Word.singleton identity.lhs.final)
    have guarded :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans <| guarded.trans rightDuplicate.symm

def intersectionBasisS5_791 :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_15opS5_791
