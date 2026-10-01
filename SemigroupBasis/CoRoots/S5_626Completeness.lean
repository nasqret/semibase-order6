import SemigroupBasis.CoRoots.S5_626AffineBridge

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis
open SemigroupBasis.Examples

private theorem affineMul_zero_left (value : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul 0 value = value := by
  decide +revert

private theorem affineMul_zero_right (value : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul value 0 = value := by
  decide +revert

private theorem affineMul_right_two (value : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul value 2 = 2 := by
  decide +revert

private theorem affineMul_right_three (value : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul value 3 = 3 := by
  decide +revert

private theorem affineMul_two_two :
    SemigroupBasis.Generated.Catalogue.S4_96.mul 2 2 = 2 := by
  decide

private def affineOppositeHeadSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun letter => if letter = tested then 2 else 3

private theorem affineOppositeFold_two
    (valuation : Nat → Fin 4) :
    ∀ letters : List Nat,
      letters.foldl
          (fun value letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation letter) value)
          (2 : Fin 4) = 2
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        SemigroupBasis.Generated.Catalogue.S4_96.mul
            (valuation letter) 2 = 2 by
          exact affineMul_right_two (valuation letter)]
      exact affineOppositeFold_two valuation rest

private theorem affineOppositeFold_three
    (valuation : Nat → Fin 4) :
    ∀ letters : List Nat,
      letters.foldl
          (fun value letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation letter) value)
          (3 : Fin 4) = 3
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        SemigroupBasis.Generated.Catalogue.S4_96.mul
            (valuation letter) 3 = 3 by
          exact affineMul_right_three (valuation letter)]
      exact affineOppositeFold_three valuation rest

theorem affineOppositeHeadSeparator_eval
    (tested : Nat) (word : Word Nat) :
    affineParityFour.semigroup.opposite.eval
        (affineOppositeHeadSeparator tested) word =
      affineOppositeHeadSeparator tested word.head := by
  cases word with
  | mk head tail =>
      by_cases same : head = tested
      · simp only [Semigroup.eval, affineOppositeHeadSeparator, same,
          if_pos]
        simpa [affineParityFour, FiniteTable.semigroup,
          Semigroup.opposite] using
            affineOppositeFold_two
              (affineOppositeHeadSeparator tested) tail
      · simp only [Semigroup.eval, affineOppositeHeadSeparator, same,
          if_neg]
        simpa [affineParityFour, FiniteTable.semigroup,
          Semigroup.opposite] using
            affineOppositeFold_three
              (affineOppositeHeadSeparator tested) tail

theorem sameHead_of_affineValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    identity.rhs.head = identity.lhs.head := by
  have directValid :
      identity.SatisfiedBy affineParityFour.semigroup.opposite := by
    simpa [affineParityFour] using valid
  have evaluated :=
    directValid
      (affineOppositeHeadSeparator identity.lhs.head)
  rw [affineOppositeHeadSeparator_eval,
    affineOppositeHeadSeparator_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  have reverseDifferent :
      identity.rhs.head ≠ identity.lhs.head := different
  simp [affineOppositeHeadSeparator, reverseDifferent] at evaluated

private def maskInitial
    (initial : Nat) (valuation : Nat → Fin 4) : Nat → Fin 4 :=
  fun letter => if letter = initial then 0 else valuation letter

private theorem affineParityFold_congr
    (leftValuation rightValuation : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply affineParityFold_congr leftValuation rightValuation
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem affineParityListEval_maskInitial
    (initial : Nat) (valuation : Nat → Fin 4)
    (letters : List Nat) (absent : initial ∉ letters) :
    affineParityListEval (maskInitial initial valuation) letters =
      affineParityListEval valuation letters := by
  unfold affineParityListEval
  apply affineParityFold_congr
  intro letter member
  have different : letter ≠ initial := by
    intro equal
    subst letter
    exact absent member
  simp [maskInitial, different]

private theorem affineParityListEval_maskedInitialSuffix
    (initial : Nat) (valuation : Nat → Fin 4)
    (letters : List Nat) (absent : initial ∉ letters) :
    affineParityListEval (maskInitial initial valuation)
        (letters.reverse ++ [initial]) =
      affineParityListEval valuation letters.reverse := by
  rw [affineParityListEval_append,
    affineParityListEval_maskInitial
      initial valuation letters.reverse (by simpa using absent)]
  simp [affineParityListEval, maskInitial,
    affineMul_zero_left, affineMul_zero_right]

theorem simpleInitial_tailListEval_eq
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (sameHead : identity.rhs.head = identity.lhs.head)
    (leftSimple : InitialOccursExactlyOnce identity.lhs)
    (rightSimple : InitialOccursExactlyOnce identity.rhs) :
    ∀ valuation : Nat → Fin 4,
      affineParityListEval valuation identity.lhs.tail.reverse =
        affineParityListEval valuation identity.rhs.tail.reverse := by
  intro valuation
  have directValid :
      identity.SatisfiedBy affineParityFour.semigroup.opposite := by
    simpa [affineParityFour] using affineValid
  have evaluated :=
    directValid (maskInitial identity.lhs.head valuation)
  rw [Semigroup.eval_opposite_eq_reverse,
    Semigroup.eval_opposite_eq_reverse,
    affineParityEval_eq_listEval,
    affineParityEval_eq_listEval,
    Word.toList_reverse, Word.toList_reverse] at evaluated
  have evaluated' :
      affineParityListEval (maskInitial identity.lhs.head valuation)
          (identity.lhs.tail.reverse ++ [identity.lhs.head]) =
        affineParityListEval (maskInitial identity.lhs.head valuation)
          (identity.rhs.tail.reverse ++ [identity.rhs.head]) := by
    simpa only [Word.toList, List.reverse_cons] using evaluated
  rw [sameHead,
    affineParityListEval_maskedInitialSuffix
      identity.lhs.head valuation identity.lhs.tail leftSimple,
    affineParityListEval_maskedInitialSuffix
      identity.lhs.head valuation identity.rhs.tail (by
        simpa [InitialOccursExactlyOnce, sameHead] using rightSimple)] at evaluated'
  exact evaluated'

private theorem affineParityFold_all_two :
    ∀ letters : List Nat,
      letters.foldl
          (fun value _ =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul value 2)
          2 = 2
  | [] => rfl
  | _ :: rest => by
      simp only [List.foldl_cons, affineMul_two_two]
      exact affineParityFold_all_two rest

private theorem affineParityListEval_all_two_cons
    (head : Nat) (tail : List Nat) :
    affineParityListEval (fun _ => (2 : Fin 4)) (head :: tail) = 2 := by
  unfold affineParityListEval
  simp only [List.foldl_cons, affineMul_zero_left]
  exact affineParityFold_all_two tail

private theorem affineParityListEval_all_two_of_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    affineParityListEval (fun _ => (2 : Fin 4)) letters = 2 := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      exact affineParityListEval_all_two_cons head tail

theorem simpleInitial_tails_sameEmptiness
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (sameHead : identity.rhs.head = identity.lhs.head)
    (leftSimple : InitialOccursExactlyOnce identity.lhs)
    (rightSimple : InitialOccursExactlyOnce identity.rhs) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have tailEval :=
    simpleInitial_tailListEval_eq identity affineValid sameHead
      leftSimple rightSimple (fun _ => 2)
  constructor
  · intro leftEmpty
    cases rightShape : identity.rhs.tail with
    | nil => rfl
    | cons head tail =>
        exfalso
        rw [leftEmpty, rightShape] at tailEval
        have rightValue :
            affineParityListEval (fun _ => (2 : Fin 4))
                (head :: tail).reverse = 2 :=
          affineParityListEval_all_two_of_ne_nil (by simp)
        rw [rightValue] at tailEval
        have impossible : (0 : Fin 4) = 2 := by
          simpa [affineParityListEval] using tailEval
        exact (by decide : (0 : Fin 4) ≠ 2) impossible
  · intro rightEmpty
    cases leftShape : identity.lhs.tail with
    | nil => rfl
    | cons head tail =>
        exfalso
        rw [leftShape, rightEmpty] at tailEval
        have leftValue :
            affineParityListEval (fun _ => (2 : Fin 4))
                (head :: tail).reverse = 2 :=
          affineParityListEval_all_two_of_ne_nil (by simp)
        rw [leftValue] at tailEval
        have impossible : (2 : Fin 4) = 0 := by
          simpa [affineParityListEval] using tailEval
        exact (by decide : (2 : Fin 4) ≠ 0) impossible

theorem derivesOfSimpleInitialAndAffineValid
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (sameHead : identity.rhs.head = identity.lhs.head)
    (leftSimple : InitialOccursExactlyOnce identity.lhs)
    (rightSimple : InitialOccursExactlyOnce identity.rhs) :
    Derives basis identity.lhs identity.rhs := by
  cases leftShape : identity.lhs.tail with
  | nil =>
      have rightEmpty :=
        (simpleInitial_tails_sameEmptiness identity affineValid
          sameHead leftSimple rightSimple).mp leftShape
      have wordsEqual : identity.lhs = identity.rhs := by
        apply Word.toList_injective
        simp [Word.toList, leftShape, rightEmpty, sameHead]
      rw [← wordsEqual]
      exact Derives.refl _
  | cons leftTailHead leftTailRest =>
      have rightNonempty : identity.rhs.tail ≠ [] := by
        intro rightEmpty
        have leftEmpty :=
          (simpleInitial_tails_sameEmptiness identity affineValid
            sameHead leftSimple rightSimple).mpr rightEmpty
        rw [leftShape] at leftEmpty
        contradiction
      cases rightShape : identity.rhs.tail with
      | nil => contradiction
      | cons rightTailHead rightTailRest =>
          let leftTailWord : Word Nat :=
            ⟨leftTailHead, leftTailRest⟩
          let rightTailWord : Word Nat :=
            ⟨rightTailHead, rightTailRest⟩
          have tailValid :
              (Identity.mk leftTailWord rightTailWord).SatisfiedBy
                affineParityFactorTable.semigroup.opposite := by
            intro valuation
            have tailEval :=
              simpleInitial_tailListEval_eq identity affineValid
                sameHead leftSimple rightSimple valuation
            rw [leftShape, rightShape] at tailEval
            change
              affineParityFour.semigroup.opposite.eval
                  valuation leftTailWord =
                affineParityFour.semigroup.opposite.eval
                  valuation rightTailWord
            rw [Semigroup.eval_opposite_eq_reverse,
              Semigroup.eval_opposite_eq_reverse,
              affineParityEval_eq_listEval,
              affineParityEval_eq_listEval,
              Word.toList_reverse, Word.toList_reverse]
            simpa [leftTailWord, rightTailWord, Word.toList,
              List.reverse_cons] using tailEval
          have lifted :=
            derivesAffineEquivalentUnderPrefix
              (Identity.mk leftTailWord rightTailWord) tailValid
              (Word.singleton identity.lhs.head)
          have leftWordEq :
              Word.singleton identity.lhs.head ++ leftTailWord =
                identity.lhs := by
            apply Word.toList_injective
            simp [leftTailWord, leftShape, Word.toList]
          have rightWordEq :
              Word.singleton identity.lhs.head ++ rightTailWord =
                identity.rhs := by
            apply Word.toList_injective
            simp [rightTailWord, rightShape, Word.toList, sameHead]
          rw [leftWordEq, rightWordEq] at lifted
          exact lifted

/-- The two exact hypotheses consumed by the globally simple and repeated
branches.  The combinatorial converse below supplies them from
`SameSegmentedFactorSignature`. -/
theorem derivesOfAffineValidAndInitialStatus
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (simpleIff :
      InitialOccursExactlyOnce identity.lhs ↔
        InitialOccursExactlyOnce identity.rhs) :
    Derives basis identity.lhs identity.rhs := by
  have sameHead := sameHead_of_affineValid identity affineValid
  by_cases leftSimple : InitialOccursExactlyOnce identity.lhs
  · exact derivesOfSimpleInitialAndAffineValid identity affineValid
      sameHead leftSimple (simpleIff.mp leftSimple)
  · have rightNotSimple :
        ¬ InitialOccursExactlyOnce identity.rhs := by
      intro rightSimple
      exact leftSimple (simpleIff.mpr rightSimple)
    have leftRepeated : identity.lhs.head ∈ identity.lhs.tail := by
      simpa [InitialOccursExactlyOnce] using leftSimple
    have rightRepeated : identity.rhs.head ∈ identity.rhs.tail := by
      simpa [InitialOccursExactlyOnce] using rightNotSimple
    exact derivesRepeatedInitialToRepeatedBase
      identity.lhs identity.rhs leftRepeated sameHead
      rightRepeated affineValid

private theorem converseBoundary_eq_of_signatures
    {leftSource rightSource : List Nat}
    (totalParity :
      ∀ tested,
        leftSource.count tested % 2 =
          rightSource.count tested % 2)
    (suffixParity :
      ∀ tested marker, tested ≠ marker →
        affineParitySuffixParity tested marker leftSource =
          affineParitySuffixParity tested marker rightSource)
    (previous : Option Nat) (tested : Nat) :
    affineParityBoundaryParity leftSource previous tested =
      affineParityBoundaryParity rightSource previous tested := by
  cases previous with
  | none =>
      exact totalParity tested
  | some marker =>
      by_cases same : tested = marker
      · simp [affineParityBoundaryParity, same]
      · simpa [affineParityBoundaryParity, same] using
          suffixParity tested marker same

private theorem converseBoundary_after_marker
    (source before block rest : List Nat)
    (marker tested : Nat)
    (sourceEq : source = before ++ block ++ marker :: rest)
    (markerAbsent : marker ∉ rest) :
    affineParityBoundaryParity source (some marker) tested =
      rest.count tested % 2 := by
  by_cases same : tested = marker
  · subst tested
    have countZero : rest.count marker = 0 :=
      List.count_eq_zero.mpr markerAbsent
    simp [affineParityBoundaryParity, countZero]
  · rw [sourceEq]
    simpa [affineParityBoundaryParity, same,
      List.append_assoc] using
        affineParitySuffixParity_append_marker
          tested marker same (before ++ block) rest markerAbsent

private theorem converseBlock_mem_iff
    (source : List Nat) (previous : Option Nat)
    (block rest : List Nat) (marker tested : Nat)
    (blockNodup : block.Nodup)
    (previousProfile :
      ∀ letter,
        affineParityBoundaryParity source previous letter =
          (block ++ marker :: rest).count letter % 2)
    (currentProfile :
      ∀ letter,
        affineParityBoundaryParity source (some marker) letter =
          rest.count letter % 2) :
    tested ∈ block ↔
      (affineParityBoundaryParity source previous tested +
          (if tested = marker then 1 else 0) +
        affineParityBoundaryParity source
          (some marker) tested) % 2 = 1 := by
  have previousEq := previousProfile tested
  have currentEq := currentProfile tested
  have markerCount :
      (marker :: rest).count tested =
        (if tested = marker then 1 else 0) +
          rest.count tested := by
    by_cases same : tested = marker
    · subst tested
      simp [Nat.add_comm]
    · rw [List.count_cons_of_ne (Ne.symm same)]
      simp [same]
  rw [List.count_append] at previousEq
  rw [blockNodup.count] at previousEq
  rw [markerCount] at previousEq
  rw [previousEq, currentEq]
  rw [show
    (((((if tested ∈ block then 1 else 0) +
          ((if tested = marker then 1 else 0) +
            rest.count tested)) % 2 +
        (if tested = marker then 1 else 0)) +
        rest.count tested % 2) % 2) =
      (if tested ∈ block then 1 else 0) % 2 by
        omega]
  by_cases member : tested ∈ block <;> simp [member]

private theorem conversePerm_of_nodup_mem_iff
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (same : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [same letter]

/-- Reconstruct every duplicate-free affine parity block from the boundary
parities before and after its marker. -/
private theorem converseSegmentsPerm :
    ∀ (leftSource rightSource : List Nat)
      (previous : Option Nat)
      (leftBefore rightBefore : List Nat)
      (left right : List AffineParitySegment),
      AffineParitySegmentsNormal left →
      AffineParitySegmentsNormal right →
      affineParityMarkers left = affineParityMarkers right →
      leftSource = leftBefore ++ affineParityRender left →
      rightSource = rightBefore ++ affineParityRender right →
      (∀ letter,
        affineParityBoundaryParity leftSource previous letter =
          (affineParityRender left).count letter % 2) →
      (∀ letter,
        affineParityBoundaryParity rightSource previous letter =
          (affineParityRender right).count letter % 2) →
      (∀ letter,
        leftSource.count letter % 2 =
          rightSource.count letter % 2) →
      (∀ tested marker, tested ≠ marker →
        affineParitySuffixParity tested marker leftSource =
          affineParitySuffixParity tested marker rightSource) →
      AffineParitySegmentsPerm left right
  | _, _, _, _, _, [], [], _, _, _, _, _, _, _, _, _ =>
      AffineParitySegmentsPerm.nil
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      [], _ :: _, _, _, markerEq, _, _, _, _, _, _ => by
      simp [affineParityMarkers] at markerEq
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      _ :: _, [], _, _, markerEq, _, _, _, _, _, _ => by
      simp [affineParityMarkers] at markerEq
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      ⟨leftBlock, leftMarker⟩ :: leftRest,
      ⟨rightBlock, rightMarker⟩ :: rightRest,
      leftNormal, rightNormal, markerEq,
      leftSourceEq, rightSourceEq,
      leftPreviousProfile, rightPreviousProfile,
      totalParity, suffixParity => by
      have markers :
          leftMarker = rightMarker ∧
            affineParityMarkers leftRest =
              affineParityMarkers rightRest := by
        simpa [affineParityMarkers] using markerEq
      rcases markers with ⟨rfl, restMarkers⟩
      cases leftNormal with
      | cons leftNodup leftMarkerFresh
          leftGuard leftRestNormal =>
          cases rightNormal with
          | cons rightNodup rightMarkerFresh
              rightGuard rightRestNormal =>
              have leftMarkerAbsent :
                  leftMarker ∉ affineParityRender leftRest :=
                AffineParitySegmentsNormal.marker_not_mem_render_rest
                  (AffineParitySegmentsNormal.cons
                    leftNodup leftMarkerFresh
                    leftGuard leftRestNormal)
              have rightMarkerAbsent :
                  leftMarker ∉ affineParityRender rightRest :=
                AffineParitySegmentsNormal.marker_not_mem_render_rest
                  (AffineParitySegmentsNormal.cons
                    rightNodup rightMarkerFresh
                    rightGuard rightRestNormal)
              have leftCurrentProfile :
                  ∀ letter,
                    affineParityBoundaryParity leftSource
                        (some leftMarker) letter =
                      (affineParityRender leftRest).count letter % 2 := by
                intro letter
                apply converseBoundary_after_marker
                  leftSource leftBefore leftBlock
                  (affineParityRender leftRest)
                  leftMarker letter
                · simpa [affineParityRender,
                    List.append_assoc] using leftSourceEq
                · exact leftMarkerAbsent
              have rightCurrentProfile :
                  ∀ letter,
                    affineParityBoundaryParity rightSource
                        (some leftMarker) letter =
                      (affineParityRender rightRest).count letter % 2 := by
                intro letter
                apply converseBoundary_after_marker
                  rightSource rightBefore rightBlock
                  (affineParityRender rightRest)
                  leftMarker letter
                · simpa [affineParityRender,
                    List.append_assoc] using rightSourceEq
                · exact rightMarkerAbsent
              have blockSame :
                  ∀ letter,
                    letter ∈ leftBlock ↔ letter ∈ rightBlock := by
                intro letter
                rw [converseBlock_mem_iff
                    leftSource previous leftBlock
                    (affineParityRender leftRest)
                    leftMarker letter leftNodup
                    (by
                      intro tested
                      simpa [affineParityRender] using
                        leftPreviousProfile tested)
                    leftCurrentProfile,
                  converseBlock_mem_iff
                    rightSource previous rightBlock
                    (affineParityRender rightRest)
                    leftMarker letter rightNodup
                    (by
                      intro tested
                      simpa [affineParityRender] using
                        rightPreviousProfile tested)
                    rightCurrentProfile]
                rw [converseBoundary_eq_of_signatures
                    totalParity suffixParity previous letter,
                  converseBoundary_eq_of_signatures
                    totalParity suffixParity
                    (some leftMarker) letter]
              have blockPerm : leftBlock.Perm rightBlock :=
                conversePerm_of_nodup_mem_iff
                  leftNodup rightNodup blockSame
              apply AffineParitySegmentsPerm.cons blockPerm
              apply converseSegmentsPerm
                leftSource rightSource (some leftMarker)
                (leftBefore ++ leftBlock ++ [leftMarker])
                (rightBefore ++ rightBlock ++ [leftMarker])
                leftRest rightRest
                leftRestNormal rightRestNormal restMarkers
              · simpa [affineParityRender,
                  List.append_assoc] using leftSourceEq
              · simpa [affineParityRender,
                  List.append_assoc] using rightSourceEq
              · exact leftCurrentProfile
              · exact rightCurrentProfile
              · exact totalParity
              · exact suffixParity

/-- Equal marker order, boundary parities, and total parity reconstruct
blockwise permutation-equivalent affine normal forms and hence an actual
derivation in the complete opposite affine basis. -/
theorem affineOppositeDerivesOfSameCombinatorics
    {left right : Word Nat}
    (same : SameAffineOppositeCombinatorics left right) :
    Derives affineParityFourOppositeBasis left right := by
  have leftDerivation := affineParityDerivesNormal left.reverse
  have rightDerivation := affineParityDerivesNormal right.reverse
  simp only [Word.toList_reverse] at leftDerivation rightDerivation
  have leftNormal :=
    affineParityNormalSegments_normal left.toList.reverse
  have rightNormal :=
    affineParityNormalSegments_normal right.toList.reverse
  cases leftEq :
      affineParityNormalSegments left.toList.reverse with
  | nil =>
      exact False.elim <|
        affineParityNormalSegments_cons_ne_nil
          left.reverse.head left.reverse.tail <| by
            change
              affineParityNormalSegments left.reverse.toList = []
            simpa using leftEq
  | cons leftHead leftRest =>
      rw [leftEq] at leftDerivation leftNormal
      cases rightEq :
          affineParityNormalSegments right.toList.reverse with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil
              right.reverse.head right.reverse.tail <| by
                change
                  affineParityNormalSegments right.reverse.toList = []
                simpa using rightEq
      | cons rightHead rightRest =>
          rw [rightEq] at rightDerivation rightNormal
          have markerEq :
              affineParityMarkers (leftHead :: leftRest) =
                affineParityMarkers (rightHead :: rightRest) := by
            have reversed := congrArg List.reverse same.markers
            simp [affineOppositeMarkers, leftEq, rightEq] at reversed
            exact reversed
          have leftValid :
              (Identity.mk left.reverse
                (affineParityRenderWord leftHead leftRest)).SatisfiedBy
                  affineParityFour.semigroup := by
            intro valuation
            exact leftDerivation.sound
              affineParityFourBasis_models valuation
          have rightValid :
              (Identity.mk right.reverse
                (affineParityRenderWord rightHead rightRest)).SatisfiedBy
                  affineParityFour.semigroup := by
            intro valuation
            exact rightDerivation.sound
              affineParityFourBasis_models valuation
          have totalParity :
              ∀ tested,
                (affineParityRender
                    (leftHead :: leftRest)).count tested % 2 =
                  (affineParityRender
                    (rightHead :: rightRest)).count tested % 2 := by
            intro tested
            have leftParity :=
              affineParityValid_totalParity
                (Identity.mk left.reverse
                  (affineParityRenderWord leftHead leftRest))
                leftValid tested
            have rightParity :=
              affineParityValid_totalParity
                (Identity.mk right.reverse
                  (affineParityRenderWord rightHead rightRest))
                rightValid tested
            have sourceParity :
                left.reverse.toList.count tested % 2 =
                  right.reverse.toList.count tested % 2 := by
              simpa only [Word.toList_reverse, List.count_reverse,
                affineOppositeFinalParity] using
                  same.finalParity tested
            calc
              (affineParityRender
                  (leftHead :: leftRest)).count tested % 2 =
                  left.reverse.toList.count tested % 2 := by
                    simpa only [affineParityRenderWord_toList] using
                      leftParity.symm
              _ = right.reverse.toList.count tested % 2 := sourceParity
              _ = (affineParityRender
                    (rightHead :: rightRest)).count tested % 2 := by
                    simpa only [affineParityRenderWord_toList] using
                      rightParity
          have suffixParity :
              ∀ tested marker, tested ≠ marker →
                affineParitySuffixParity tested marker
                    (affineParityRender (leftHead :: leftRest)) =
                  affineParitySuffixParity tested marker
                    (affineParityRender (rightHead :: rightRest)) := by
            intro tested marker different
            have leftParity :=
              affineParityValid_suffixParity
                (Identity.mk left.reverse
                  (affineParityRenderWord leftHead leftRest))
                leftValid tested marker different
            have rightParity :=
              affineParityValid_suffixParity
                (Identity.mk right.reverse
                  (affineParityRenderWord rightHead rightRest))
                rightValid tested marker different
            have sourceParity :
                affineParitySuffixParity tested marker
                    left.reverse.toList =
                  affineParitySuffixParity tested marker
                    right.reverse.toList := by
              simpa [affineOppositeBoundaryParity, different] using
                same.boundaryParity tested marker
            calc
              affineParitySuffixParity tested marker
                  (affineParityRender (leftHead :: leftRest)) =
                  affineParitySuffixParity tested marker
                    left.reverse.toList := by
                    simpa only [affineParityRenderWord_toList] using
                      leftParity.symm
              _ = affineParitySuffixParity tested marker
                    right.reverse.toList := sourceParity
              _ = affineParitySuffixParity tested marker
                    (affineParityRender
                      (rightHead :: rightRest)) := by
                    simpa only [affineParityRenderWord_toList] using
                      rightParity
          have segmentsPerm :
              AffineParitySegmentsPerm
                (leftHead :: leftRest) (rightHead :: rightRest) :=
            converseSegmentsPerm
              (affineParityRender (leftHead :: leftRest))
              (affineParityRender (rightHead :: rightRest))
              none [] []
              (leftHead :: leftRest) (rightHead :: rightRest)
              leftNormal rightNormal markerEq
              (by simp) (by simp)
              (by intro tested; rfl)
              (by intro tested; rfl)
              totalParity suffixParity
          have middle :=
            affineParitySegmentsPerm_derivesRendered
              segmentsPerm leftNormal rightNormal
          have direct :
              Derives affineParityFourBasis
                left.reverse right.reverse :=
            leftDerivation.trans <|
              middle.trans (Derives.symm rightDerivation)
          simpa [affineParityFourOppositeBasis] using direct.reverse

/-- The combinatorial affine coordinates are sufficient for equality of the
opposite-affine term functions. -/
theorem sameAffineOppositeCombinatorics_valid
    {left right : Word Nat}
    (same : SameAffineOppositeCombinatorics left right) :
    (Identity.mk left right).SatisfiedBy
      affineParityFactorTable.semigroup.opposite := by
  intro valuation
  have evaluated :=
    (affineOppositeDerivesOfSameCombinatorics same).sound
      affineParityFourOppositeBasis_complete.1 valuation
  simpa [affineParityFour] using evaluated

theorem affineValid_iff_sameAffineOppositeCombinatorics
    (identity : Identity Nat) :
    identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite ↔
      SameAffineOppositeCombinatorics
        identity.lhs identity.rhs :=
  ⟨sameAffineOppositeCombinatorics_of_valid identity,
    sameAffineOppositeCombinatorics_valid⟩

/-- The segmented factor signature is unconditionally sufficient for the
eleven-law basis. -/
theorem derivesOfSameSegmentedFactorSignature
    {left right : Word Nat}
    (same : SameSegmentedFactorSignature left right) :
    Derives basis left right :=
  derivesOfAffineValidAndInitialStatus
    (Identity.mk left right)
    (sameAffineOppositeCombinatorics_valid same.affine)
    same.initialOccursExactlyOnce

theorem sameSegmentedFactorSignature_valid
    {left right : Word Nat}
    (same : SameSegmentedFactorSignature left right) :
    (Identity.mk left right).SatisfiedBy table.semigroup := by
  intro valuation
  exact (derivesOfSameSegmentedFactorSignature same).sound
    models valuation

theorem valid_iff_sameSegmentedFactorSignature
    (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      SameSegmentedFactorSignature identity.lhs identity.rhs :=
  ⟨valid_segmentedFactorSignature identity,
    sameSegmentedFactorSignature_valid⟩

theorem derivesOfValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSegmentedFactorSignature
    (valid_segmentedFactorSignature identity valid)

theorem basisFor : BasisFor table.semigroup basis :=
  ⟨models, derivesOfValid⟩

theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

/- The direct and opposite `BasisFor` endpoints can be reached either from
actual table validity and the split factors or through the now-complete
`SameSegmentedFactorSignature` characterization. -/

end SemigroupBasis.CoRoots.S5_626
