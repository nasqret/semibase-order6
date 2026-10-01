import SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening
import SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeLift
import SemigroupBasis.CoRoots.Order6SporadicSection14Invariants
import SemigroupBasis.CoRoots.S5_788Family
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteCertificate

set_option maxRecDepth 100000

/-!
# Relative transfer for the `1ccaef90de83de0a` Ford--Lord system

The common final letter is detected by `S2_4^op`.  A globally simple final
is stripped semantically from the `S5_788` factor using right reductivity:
the five right-translation rows of the exact catalogue table are pairwise
distinct.  A repeated final is duplicated and contracted with the displayed
`1cca` power and right-duplication laws.  The generalized suffix lift then
turns completeness of the common twenty-four-law `S5_788` basis into the
requested intersection basis.  Finally, the left factor is widened to
`S3_15^op`, and the common right-factor theory is transferred to `S5_805`
and `S5_811`.

This module is source-staged.  It has not yet been elaborated or
kernel-checked.
-/

namespace SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FordLord1cca.basis

private abbrev smallLeftFactor :=
  SemigroupBasis.Generated.S2_4.table.semigroup.opposite

private abbrev targetLeftFactor :=
  SemigroupBasis.Generated.S3_15.table.semigroup.opposite

private abbrev s5_788Factor :=
  SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup

private abbrev s5_805Factor :=
  SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup

private abbrev s5_811Factor :=
  SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup

/-! ## Exact factor soundness -/

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def oppositeFiniteTable (table : FiniteTable) : FiniteTable where
  order := table.order
  mul := fun left right => table.mul right left
  assoc := fun left middle right =>
    (table.assoc right middle left).symm

private theorem oppositeFiniteTable_semigroup (table : FiniteTable) :
    (oppositeFiniteTable table).semigroup =
      table.semigroup.opposite := by
  rfl

theorem modelsS2_4Opposite : Models smallLeftFactor targetBasis := by
  change Models
    SemigroupBasis.Generated.S2_4.table.semigroup.opposite targetBasis
  rw [← oppositeFiniteTable_semigroup SemigroupBasis.Generated.S2_4.table]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable SemigroupBasis.Generated.S2_4.table)
    targetBasis toFinThree (by decide)

theorem modelsS3_15Opposite : Models targetLeftFactor targetBasis := by
  change Models
    SemigroupBasis.Generated.S3_15.table.semigroup.opposite targetBasis
  rw [← oppositeFiniteTable_semigroup SemigroupBasis.Generated.S3_15.table]
  exact FiniteCertificate.checkModels_sound
    (oppositeFiniteTable SemigroupBasis.Generated.S3_15.table)
    targetBasis toFinThree (by decide)

theorem modelsS5_788 : Models s5_788Factor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_788.table
    targetBasis toFinThree (by decide)

theorem modelsS5_805 : Models s5_805Factor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_805.table
    targetBasis toFinThree (by decide)

theorem modelsS5_811 : Models s5_811Factor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_811.table
    targetBasis toFinThree (by decide)

/-! ## Final-marker syntax -/

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
  have reconstructed := congrArg Word.final (wordOfPrefixFinal_split word)
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

/-! ## The simple-final branch from the exact-cut invariant -/

private theorem finalCountOne_of_sameSignature
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_788Invariant.SameSeparatorInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1) :
    right.toList.count right.final = 1 := by
  let leftPrefix := (splitPrefixFinal left).1
  have leftExact :
      SemigroupBasis.CoRoots.S5_441Invariant.ExactCutSignature
        left left.final leftPrefix [] := by
    refine ⟨leftPrefix, [], ?_, ?_, ?_⟩
    · refine ⟨?_, leftSimple, ?_⟩
      · simpa [leftPrefix, split_final_eq left] using
          (toList_eq_splitPrefixFinal left)
      · intro letter _ rightMember
        simpa using rightMember
    · intro letter
      rfl
    · intro letter
      rfl
  have rightExact :=
    (same.exactCuts left.final leftPrefix []).mp leftExact
  rcases rightExact with ⟨_, _, rightCut, _, _⟩
  have rightCount := rightCut.2.1
  simpa only [finalEq] using rightCount

private theorem finalCountOneIff
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_788Invariant.SameSeparatorInitialSignature
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
      SemigroupBasis.CoRoots.S5_788Invariant.SameSeparatorInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1)
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
      SemigroupBasis.CoRoots.S5_788Invariant.SameSeparatorInitialSignature
        left right)
    (finalEq : left.final = right.final)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1) :
    (splitPrefixFinal left).1 = [] ↔
      (splitPrefixFinal right).1 = [] := by
  constructor
  · exact splitPrefix_nil_of_sameSignature
      same finalEq leftSimple rightSimple
  · exact splitPrefix_nil_of_sameSignature
      same.symm finalEq.symm rightSimple leftSimple

/-! ## Right-reductive stripping in `S5_788` -/

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

/-- The exact `S5_788` table is right reductive: its five rows are pairwise
distinct.  This is the finite replacement for the false right-unit premise. -/
theorem s5_788_right_reductive
    (left right : Fin 5)
    (equalRows : forall marker : Fin 5,
      s5_788Factor.mul left marker = s5_788Factor.mul right marker) :
    left = right := by
  revert left right
  decide

/-- If a fresh final variable can be appended to two words and the resulting
identity is valid in `S5_788`, right reductivity strips that final variable. -/
theorem s5_788_prefix_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy s5_788Factor) :
    (Identity.mk left right).SatisfiedBy s5_788Factor := by
  intro valuation
  apply s5_788_right_reductive
  intro marker
  let lifted : Nat -> Fin 5 :=
    fun letter => if letter = final then marker else valuation letter
  have leftAgree :
      s5_788Factor.eval valuation left =
        s5_788Factor.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact finalNotLeft member
    simp [lifted, different]
  have rightAgree :
      s5_788Factor.eval valuation right =
        s5_788Factor.eval lifted right := by
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
    s5_788Factor.mul (s5_788Factor.eval valuation left) marker =
        s5_788Factor.mul (s5_788Factor.eval lifted left) marker :=
      congrArg (fun value => s5_788Factor.mul value marker) leftAgree
    _ = s5_788Factor.mul (s5_788Factor.eval lifted right) marker :=
      evaluated
    _ = s5_788Factor.mul (s5_788Factor.eval valuation right) marker :=
      congrArg (fun value => s5_788Factor.mul value marker)
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

/-! ## Duplicating a repeated final marker -/

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
      (SemigroupBasis.CoRoots.Order6FordLord1cca.derivesPower
        (Word.singleton letter)))

private theorem listDerivesRightDuplication
    (letter gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([letter] ++ (gapHead :: gapTail) ++ [letter])
      ([letter] ++ (gapHead :: gapTail) ++ [letter, letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (SemigroupBasis.CoRoots.Order6FordLord1cca.derivesRightDuplication
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

/-! ## Relative deduction for the base right factor -/

theorem derivesOfS5_788FactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy smallLeftFactor)
    (rightValid : identity.SatisfiedBy s5_788Factor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.S5_788.derives_sameSignature sourceDerivation
  have finalEq : identity.lhs.final = identity.rhs.final :=
    SemigroupBasis.CoRoots.Order6SporadicSection14.rightZeroValid_final_eq
      identity leftValid
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
                    s5_788Factor := by
              simpa only [leftShape, rightShape] using rightValid
            have prefixValid :=
              s5_788_prefix_valid final leftPrefixWord rightPrefixWord
                leftFinalAbsent rightFinalAbsent wholeValid
            have prefixDerivation :=
              SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete.2
                (Identity.mk leftPrefixWord rightPrefixWord) prefixValid
            have lifted :=
              SemigroupBasis.CoRoots.Order6FordLord1cca.liftS5_788UnderSuffixIdentity
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
      SemigroupBasis.CoRoots.Order6FordLord1cca.liftS5_788UnderSuffixIdentity
        sourceDerivation (Word.singleton identity.lhs.final)
    have guarded :
        Derives targetBasis
          (identity.lhs ++ Word.singleton identity.lhs.final)
          (identity.rhs ++ Word.singleton identity.rhs.final) := by
      simpa [finalEq] using lifted
    exact leftDuplicate.trans <| guarded.trans rightDuplicate.symm

def smallIntersectionBasisS5_788 :
    IntersectionBasis smallLeftFactor s5_788Factor targetBasis where
  leftModels := modelsS2_4Opposite
  rightModels := modelsS5_788
  complete := derivesOfS5_788FactorValid

/-! ## Transfer along the common complete right-factor basis -/

theorem s5_788Valid_of_s5_805Valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_805Factor) :
    identity.SatisfiedBy s5_788Factor := by
  have derivation :=
    SemigroupBasis.CoRoots.S5_788Family.S5_805.basis_complete.2
      identity valid
  intro valuation
  exact derivation.sound
    SemigroupBasis.CoRoots.S5_788Family.S5_788.models valuation

theorem s5_788Valid_of_s5_811Valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy s5_811Factor) :
    identity.SatisfiedBy s5_788Factor := by
  have derivation :=
    SemigroupBasis.CoRoots.S5_788Family.S5_811.basis_complete.2
      identity valid
  intro valuation
  exact derivation.sound
    SemigroupBasis.CoRoots.S5_788Family.S5_788.models valuation

def smallIntersectionBasisS5_805 :
    IntersectionBasis smallLeftFactor s5_805Factor targetBasis where
  leftModels := modelsS2_4Opposite
  rightModels := modelsS5_805
  complete := by
    intro identity leftValid rightValid
    exact derivesOfS5_788FactorValid identity leftValid
      (s5_788Valid_of_s5_805Valid identity rightValid)

def smallIntersectionBasisS5_811 :
    IntersectionBasis smallLeftFactor s5_811Factor targetBasis where
  leftModels := modelsS2_4Opposite
  rightModels := modelsS5_811
  complete := by
    intro identity leftValid rightValid
    exact derivesOfS5_788FactorValid identity leftValid
      (s5_788Valid_of_s5_811Valid identity rightValid)

/-! ## Widening to the requested order-three detector -/

private def widenLeftFactor
    {A : Type u} {B : Type v} {C : Type w} {X : Type z}
    {sourceLeft : Semigroup A} {targetLeft : Semigroup B}
    {fixedRight : Semigroup C}
    {candidate : List (Identity X)}
    (source : IntersectionBasis sourceLeft fixedRight candidate)
    (targetModels : Models targetLeft candidate)
    (into : Embedding sourceLeft targetLeft) :
    IntersectionBasis targetLeft fixedRight candidate where
  leftModels := targetModels
  rightModels := source.rightModels
  complete := by
    intro identity targetValid rightValid
    exact source.complete identity
      (into.pullback_identity identity targetValid) rightValid

def factorIntersectionBasisS5_788 :
    IntersectionBasis targetLeftFactor s5_788Factor targetBasis :=
  widenLeftFactor smallIntersectionBasisS5_788 modelsS3_15Opposite
    SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening.s2_4OppositeEmbeddingS3_15Opposite

def factorIntersectionBasisS5_805 :
    IntersectionBasis targetLeftFactor s5_805Factor targetBasis :=
  widenLeftFactor smallIntersectionBasisS5_805 modelsS3_15Opposite
    SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening.s2_4OppositeEmbeddingS3_15Opposite

def factorIntersectionBasisS5_811 :
    IntersectionBasis targetLeftFactor s5_811Factor targetBasis :=
  widenLeftFactor smallIntersectionBasisS5_811 modelsS3_15Opposite
    SemigroupBasis.CoRoots.Order6FactorPairS3_15OppositeWidening.s2_4OppositeEmbeddingS3_15Opposite

/-! ## Authoritative displayed-basis interfaces -/

def intersectionBasisS5_788 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLord1cca.basis_eq_displayed] using
    factorIntersectionBasisS5_788

def intersectionBasisS5_805 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_805.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLord1cca.basis_eq_displayed] using
    factorIntersectionBasisS5_805

def intersectionBasisS5_811 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_811.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLord1cca.basis_eq_displayed] using
    factorIntersectionBasisS5_811

end SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer
