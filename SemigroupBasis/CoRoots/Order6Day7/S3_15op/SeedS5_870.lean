import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_870RelativeLift
import SemigroupBasis.CoRoots.S5_870Family
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Independent unrestricted S3_15op × S5_870 rank-066 seed

The complete eight-law S5_870 gap-signature basis lifts under an arbitrary
nonempty final guard. Its independently certified capped multiplicities
preserve simplicity of the common final. Catalogue state `3` is an exact
right identity, so a fresh simple final can be removed semantically; the two
literal cap laws duplicate any already repeated final. Thus the exact
ten-law unrestricted intersection is proved BEFORE introducing its quotient
normalizer and both authenticated S6_13755 orientation endpoints.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_870

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank066.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_870.table.semigroup

private theorem rank066_leftTable_eq :
    Rank066.leftTable =
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable := by
  change
    SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S3_15.table =
      SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.S3_15.table
  rw [SemigroupBasis.Generated.S3_15.table_eq_canonical_catalogue]

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All ten exact frozen laws are checked on their full five-variable support. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank066.basis toFinFive (by decide)

theorem modelsRight : Models rightFactor targetBasis :=
  Rank066.rightModels

private theorem capped_two_eq_one_iff (count : Nat) :
    Nat.min count 2 = 1 ↔ count = 1 := by
  simp only [Nat.min_def]
  split <;> omega

/-- The exact certified S5_870 gap signature preserves final simplicity. -/
theorem finalCountOneIff_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor)
    (finalEq : identity.lhs.final = identity.rhs.final) :
    identity.lhs.toList.count identity.lhs.final = 1 ↔
      identity.rhs.toList.count identity.rhs.final = 1 := by
  have capped :=
    SemigroupBasis.CoRoots.S5_870.valid_capped_count_eq
      identity valid identity.lhs.final
  have aligned :
      Nat.min (identity.lhs.toList.count identity.lhs.final) 2 =
        Nat.min (identity.rhs.toList.count identity.rhs.final) 2 := by
    simpa only [finalEq] using capped
  constructor
  · intro simple
    apply (capped_two_eq_one_iff _).mp
    rw [← aligned]
    exact (capped_two_eq_one_iff _).mpr simple
  · intro simple
    apply (capped_two_eq_one_iff _).mp
    rw [aligned]
    exact (capped_two_eq_one_iff _).mpr simple

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

private theorem splitFinal_not_mem_stem_of_count_one
    (word : Word Nat)
    (countOne : word.toList.count word.final = 1) :
    (splitPrefixFinal word).2 ∉ (splitPrefixFinal word).1 := by
  have countOne' :
      word.toList.count (splitPrefixFinal word).2 = 1 := by
    simpa [split_final_eq] using countOne
  rw [toList_eq_splitPrefixFinal, List.count_append] at countOne'
  simp only [List.count_singleton_self] at countOne'
  have stemCount :
      (splitPrefixFinal word).1.count (splitPrefixFinal word).2 = 0 := by
    omega
  exact List.count_eq_zero.mp stemCount

private theorem splitFinal_mem_stem_of_count_ne_one
    (word : Word Nat)
    (countNotOne : word.toList.count word.final ≠ 1) :
    (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1 := by
  have countNotOne' :
      word.toList.count (splitPrefixFinal word).2 ≠ 1 := by
    simpa [split_final_eq] using countNotOne
  have countShape :
      word.toList.count (splitPrefixFinal word).2 =
        (splitPrefixFinal word).1.count (splitPrefixFinal word).2 + 1 := by
    rw [toList_eq_splitPrefixFinal, List.count_append]
    simp
  have positive :
      0 < (splitPrefixFinal word).1.count (splitPrefixFinal word).2 := by
    omega
  exact List.count_pos_iff.mp positive

private theorem splitStem_nil_of_sameLastSupport
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.SameLastSupport left right)
    (rightSimple : right.toList.count right.final = 1)
    (leftStemEmpty : (splitPrefixFinal left).1 = []) :
    (splitPrefixFinal right).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightStemMember
  have rightMember : letter ∈ right.toList := by
    rw [toList_eq_splitPrefixFinal]
    exact List.mem_append_left _ rightStemMember
  have leftMember : letter ∈ left.toList :=
    (same.support_eq letter).2 rightMember
  have letterIsLeftFinal : letter = (splitPrefixFinal left).2 := by
    rw [toList_eq_splitPrefixFinal, leftStemEmpty] at leftMember
    simpa using leftMember
  have splitFinals :
      (splitPrefixFinal left).2 = (splitPrefixFinal right).2 :=
    (split_final_eq left).trans <|
      same.final_eq.trans (split_final_eq right).symm
  have letterIsRightFinal : letter = (splitPrefixFinal right).2 :=
    letterIsLeftFinal.trans splitFinals
  have rightFinalAbsent :=
    splitFinal_not_mem_stem_of_count_one right rightSimple
  exact rightFinalAbsent (letterIsRightFinal ▸ rightStemMember)

private theorem splitStem_nil_iff_of_sameLastSupport
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.SameLastSupport left right)
    (leftSimple : left.toList.count left.final = 1)
    (rightSimple : right.toList.count right.final = 1) :
    (splitPrefixFinal left).1 = [] ↔
      (splitPrefixFinal right).1 = [] := by
  constructor
  · exact splitStem_nil_of_sameLastSupport same rightSimple
  · exact splitStem_nil_of_sameLastSupport same.symm leftSimple

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter)) initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk first rest =>
      simp only [Semigroup.eval]
      rw [agree first (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail first member)

/-- Zero-based catalogue state `3` is the exact S5_870 right identity. -/
theorem s5_870_right_identity (value : Fin 5) :
    rightFactor.mul value (3 : Fin 5) = value := by
  decide +revert

/-- A common fresh simple final is stripped by assigning it the exact identity. -/
theorem s5_870_stem_valid
    (final : Nat) (left right : Word Nat)
    (finalNotLeft : final ∉ left.toList)
    (finalNotRight : final ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy rightFactor) :
    (Identity.mk left right).SatisfiedBy rightFactor := by
  intro valuation
  let lifted : Nat → Fin 5 :=
    fun letter => if letter = final then (3 : Fin 5) else valuation letter
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
  have liftedFinal : lifted final = (3 : Fin 5) := by
    simp [lifted]
  rw [liftedFinal, s5_870_right_identity,
    s5_870_right_identity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem listWordOfCons_append_final
    (first : Nat) (rest : List Nat) (final : Nat) :
    SemigroupBasis.CoRoots.S5_107.listWordOfCons first rest ++
        Word.singleton final =
      wordOfPrefixFinal (first :: rest) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private abbrev ListDerives : List Nat → List Nat → Prop :=
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
    (letter gapFirst : Nat) (gapRest : List Nat) :
    ListDerives
      ([letter] ++ (gapFirst :: gapRest) ++ [letter])
      ([letter] ++ (gapFirst :: gapRest) ++ [letter, letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesRightExpansion
        (Word.singleton letter)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest)))

private theorem listDerivesDuplicateFinal
    (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final]) (stem ++ [final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesPowerExpansion final))
  | cons gapFirst gapRest =>
      simpa [shape, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before
          (listDerivesRightDuplication final gapFirst gapRest))

/-- Frozen rank-066 power and final-gap cap duplicate every repeated final. -/
theorem derivesDuplicateFinal
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

/-- Exact unrestricted completeness for the authenticated frozen rank 066. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceDerivation :=
    SemigroupBasis.CoRoots.S5_870Family.S5_870.basisFor.2
      identity rightValid
  have same :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
      identity leftValid
  have finalEq := same.final_eq
  have countIff := finalCountOneIff_of_valid identity rightValid finalEq
  by_cases leftSimple :
      identity.lhs.toList.count identity.lhs.final = 1
  · have rightSimple :
        identity.rhs.toList.count identity.rhs.final = 1 :=
      countIff.mp leftSimple
    have stemsEmpty :=
      splitStem_nil_iff_of_sameLastSupport same leftSimple rightSimple
    cases leftStem : (splitPrefixFinal identity.lhs).1 with
    | nil =>
        have rightStem : (splitPrefixFinal identity.rhs).1 = [] :=
          stemsEmpty.mp leftStem
        have leftReconstructed := wordOfPrefixFinal_split identity.lhs
        have rightReconstructed := wordOfPrefixFinal_split identity.rhs
        rw [leftStem] at leftReconstructed
        rw [rightStem] at rightReconstructed
        simp only [wordOfPrefixFinal_nil] at leftReconstructed
        simp only [wordOfPrefixFinal_nil] at rightReconstructed
        have splitFinals :
            (splitPrefixFinal identity.lhs).2 =
              (splitPrefixFinal identity.rhs).2 :=
          (split_final_eq identity.lhs).trans <|
            finalEq.trans (split_final_eq identity.rhs).symm
        rw [← leftReconstructed, ← rightReconstructed, splitFinals]
        exact Derives.refl _
    | cons leftFirst leftRest =>
        cases rightStem : (splitPrefixFinal identity.rhs).1 with
        | nil =>
            have impossible := stemsEmpty.mpr rightStem
            rw [leftStem] at impossible
            contradiction
        | cons rightFirst rightRest =>
            let leftStemWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                leftFirst leftRest
            let rightStemWord :=
              SemigroupBasis.CoRoots.S5_107.listWordOfCons
                rightFirst rightRest
            let final := (splitPrefixFinal identity.lhs).2
            have splitFinals :
                (splitPrefixFinal identity.lhs).2 =
                  (splitPrefixFinal identity.rhs).2 :=
              (split_final_eq identity.lhs).trans <|
                finalEq.trans (split_final_eq identity.rhs).symm
            have leftFinalAbsentRaw :=
              splitFinal_not_mem_stem_of_count_one
                identity.lhs leftSimple
            rw [leftStem] at leftFinalAbsentRaw
            have leftFinalAbsent : final ∉ leftStemWord.toList := by
              simpa [final, leftStemWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using leftFinalAbsentRaw
            have rightFinalAbsentRaw :=
              splitFinal_not_mem_stem_of_count_one
                identity.rhs rightSimple
            rw [rightStem] at rightFinalAbsentRaw
            have rightFinalAbsent : final ∉ rightStemWord.toList := by
              simpa [final, splitFinals, rightStemWord,
                SemigroupBasis.CoRoots.S5_107.listWordOfCons,
                Word.toList] using rightFinalAbsentRaw
            have leftShape :
                leftStemWord ++ Word.singleton final = identity.lhs := by
              calc
                leftStemWord ++ Word.singleton final =
                    wordOfPrefixFinal (leftFirst :: leftRest) final := by
                  simpa [leftStemWord] using
                    listWordOfCons_append_final leftFirst leftRest final
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.lhs).1
                    (splitPrefixFinal identity.lhs).2 := by
                  rw [leftStem]
                _ = identity.lhs := wordOfPrefixFinal_split identity.lhs
            have rightShape :
                rightStemWord ++ Word.singleton final = identity.rhs := by
              calc
                rightStemWord ++ Word.singleton final =
                    rightStemWord ++ Word.singleton
                      (splitPrefixFinal identity.rhs).2 := by
                  simp only [final, splitFinals]
                _ = wordOfPrefixFinal
                    (rightFirst :: rightRest)
                    (splitPrefixFinal identity.rhs).2 := by
                  simpa [rightStemWord] using
                    listWordOfCons_append_final rightFirst rightRest
                      (splitPrefixFinal identity.rhs).2
                _ = wordOfPrefixFinal
                    (splitPrefixFinal identity.rhs).1
                    (splitPrefixFinal identity.rhs).2 := by
                  rw [rightStem]
                _ = identity.rhs := wordOfPrefixFinal_split identity.rhs
            have wholeValid :
                (Identity.mk
                  (leftStemWord ++ Word.singleton final)
                  (rightStemWord ++ Word.singleton final)).SatisfiedBy
                    rightFactor := by
              simpa only [leftShape, rightShape] using rightValid
            have stemValid :=
              s5_870_stem_valid final leftStemWord rightStemWord
                leftFinalAbsent rightFinalAbsent wholeValid
            have stemDerivation :=
              SemigroupBasis.CoRoots.S5_870Family.S5_870.basisFor.2
                (Identity.mk leftStemWord rightStemWord) stemValid
            have lifted :=
              liftS5_870UnderGuardIdentity
                stemDerivation (Word.singleton final)
            simpa only [leftShape, rightShape] using lifted
  · have rightNotSimple :
        identity.rhs.toList.count identity.rhs.final ≠ 1 := by
      intro rightSimple
      exact leftSimple (countIff.mpr rightSimple)
    have leftFinalSeen :
        identity.lhs.final ∈ (splitPrefixFinal identity.lhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_stem_of_count_ne_one identity.lhs leftSimple
    have rightFinalSeen :
        identity.rhs.final ∈ (splitPrefixFinal identity.rhs).1 := by
      simpa only [split_final_eq] using
        splitFinal_mem_stem_of_count_ne_one identity.rhs rightNotSimple
    have leftDuplicate :=
      derivesDuplicateFinal identity.lhs leftFinalSeen
    have rightDuplicate :=
      derivesDuplicateFinal identity.rhs rightFinalSeen
    have lifted :=
      liftS5_870UnderGuardIdentity sourceDerivation
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

/-- Exact unrestricted intersection basis for the frozen S5_870 rank block. -/
def intersectionBasis :
    IntersectionBasis
      Rank066.leftTable.semigroup
      Rank066.rightTable.semigroup
      Rank066.basis := by
  rw [rank066_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization is introduced only after independent completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank066.leftTable.semigroup
      Rank066.rightTable.semigroup
      Rank066.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated S6_13755 representative endpoint. -/
theorem representative_basis_S6_13755 :
    BasisFor Rank066.S6_13755.table.semigroup Rank066.basis :=
  Rank066.S6_13755.representative_basis_of_normalizer intersectionNormalizer

/-- Its exact reversed-basis opposite orientation. -/
theorem opposite_basis_S6_13755 :
    BasisFor Rank066.S6_13755.table.semigroup.opposite
      (reversedBasis Rank066.basis) :=
  Rank066.S6_13755.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_870
