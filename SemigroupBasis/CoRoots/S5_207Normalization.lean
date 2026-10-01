import SemigroupBasis.CoRoots.S5_207
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.S5_207

open SemigroupBasis
open SemigroupBasis.Examples
open DirectCompletenessArchitecture

namespace DirectCompletenessArchitecture

/-- The marker state written directly in terms of a prefix count and the
literal final-letter flag. -/
def markerStateFrom
    (prefixCount : Nat) (finalIsLetter : Bool) : MarkerState :=
  match min prefixCount 2, finalIsLetter with
  | 0, false => .absent
  | 0, true => .finalOnly
  | 1, false => .oneNonfinal
  | 1, true => .oneNonfinalAndFinal
  | _, _ => .atLeastTwoNonfinal

/-- The marker state of an explicitly split prefix/final word. -/
def splitMarkerState
    (stem : List Nat) (final letter : Nat) : MarkerState :=
  markerStateFrom (stem.count letter) (final == letter)

/-- Recover the capped prefix multiplicity from a marker state. -/
def prefixMultiplicityOfState : MarkerState -> Nat
  | .absent => 0
  | .finalOnly => 0
  | .oneNonfinal => 1
  | .oneNonfinalAndFinal => 1
  | .atLeastTwoNonfinal => 2

@[simp]
theorem prefixMultiplicity_markerStateFrom
    (prefixCount : Nat) (finalIsLetter : Bool) :
    prefixMultiplicityOfState
        (markerStateFrom prefixCount finalIsLetter) =
      min prefixCount 2 := by
  cases prefixCount with
  | zero =>
      cases finalIsLetter <;> rfl
  | succ prefixCount =>
      cases prefixCount with
      | zero =>
          cases finalIsLetter <;> rfl
      | succ prefixCount =>
          have twoLe : 2 <= Nat.succ (Nat.succ prefixCount) := by
            omega
          cases finalIsLetter <;>
            simp only [markerStateFrom, Nat.min_eq_right twoLe,
              prefixMultiplicityOfState]

@[simp]
theorem prefixLetters_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    prefixLetters (wordOfPrefixFinal stem final) = stem := by
  simp [prefixLetters, toList_wordOfPrefixFinal]

@[simp]
theorem isFinal_wordOfPrefixFinal
    (stem : List Nat) (final letter : Nat) :
    isFinal (wordOfPrefixFinal stem final) letter =
      (final == letter) := by
  simp [isFinal, toList_wordOfPrefixFinal]

@[simp]
theorem markerState_wordOfPrefixFinal
    (stem : List Nat) (final letter : Nat) :
    markerState (wordOfPrefixFinal stem final) letter =
      splitMarkerState stem final letter := by
  change
    markerStateFrom
        ((prefixLetters (wordOfPrefixFinal stem final)).count letter)
        (isFinal (wordOfPrefixFinal stem final) letter) =
      splitMarkerState stem final letter
  rw [prefixLetters_wordOfPrefixFinal, isFinal_wordOfPrefixFinal]
  rfl

end DirectCompletenessArchitecture

/-- Every permutation of a prefix is derivable while its literal final letter
is retained. -/
theorem derivesPrefixPermutation
    {prefix1 prefix2 : List Nat}
    (permutation : prefix1.Perm prefix2) (final : Nat) :
    Derives basis
      (wordOfPrefixFinal prefix1 final)
      (wordOfPrefixFinal prefix2 final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton head) ih
  | swap left right suffix =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesPrefixSwap
          (Word.singleton right) (Word.singleton left)
          (wordOfPrefixFinal suffix final)
  | trans _ _ first second =>
      exact first.trans second

/-- Retain the last two occurrences of every prefix letter. -/
def prefixCapTwo : List Nat -> List Nat
  | [] => []
  | letter :: suffix =>
      let reduced := prefixCapTwo suffix
      if reduced.count letter < 2 then letter :: reduced else reduced

/-- The reducer records exactly the threshold-two prefix multiplicity. -/
theorem count_prefixCapTwo
    (tested : Nat) (stem : List Nat) :
    (prefixCapTwo stem).count tested =
      min (stem.count tested) 2 := by
  induction stem with
  | nil =>
      simp [prefixCapTwo]
  | cons letter suffix ih =>
      simp only [prefixCapTwo]
      split <;> rename_i countSmall
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at countSmall
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal), ih]
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, ih]
          rw [ih] at countSmall
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal), ih]

theorem prefixCapTwo_count_le_two
    (tested : Nat) (stem : List Nat) :
    (prefixCapTwo stem).count tested <= 2 := by
  rw [count_prefixCapTwo]
  exact Nat.min_le_right _ _

private theorem perm_two_copies_front
    (letter : Nat) (letters : List Nat)
    (countEq : letters.count letter = 2) :
    letters.Perm
      (letter :: letter :: (letters.erase letter).erase letter) := by
  have present : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have once : (letters.erase letter).count letter = 1 := by
    rw [List.count_erase_self, countEq]
  have presentOnce : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  exact (List.perm_cons_erase present).trans <|
    List.Perm.cons letter (List.perm_cons_erase presentOnce)

private theorem derivesContractLeadingTriple
    (letter final : Nat) (remainder : List Nat) :
    Derives basis
      (wordOfPrefixFinal
        (letter :: letter :: letter :: remainder) final)
      (wordOfPrefixFinal
        (letter :: letter :: remainder) final) := by
  simpa [wordOfPrefixFinal, Word.append_assoc] using
    derivesPrefixMultiplicityCap
      (Word.singleton letter)
      (wordOfPrefixFinal remainder final)

private theorem derivesDeleteThirdPrefixCopy
    (final letter : Nat) (reduced : List Nat)
    (countEq : reduced.count letter = 2) :
    Derives basis
      (wordOfPrefixFinal (letter :: reduced) final)
      (wordOfPrefixFinal reduced final) := by
  let remainder := (reduced.erase letter).erase letter
  have reducedPerm :
      reduced.Perm (letter :: letter :: remainder) := by
    simpa [remainder] using
      perm_two_copies_front letter reduced countEq
  have sourcePerm :
      (letter :: reduced).Perm
        (letter :: letter :: letter :: remainder) :=
    List.Perm.cons letter reducedPerm
  exact
    (derivesPrefixPermutation sourcePerm final).trans <|
      (derivesContractLeadingTriple letter final remainder).trans <|
        derivesPrefixPermutation reducedPerm.symm final

/-- Normalize every unrestricted prefix multiplicity to zero, one, or two
while retaining the literal final letter. -/
theorem derivesNormalizePrefix :
    forall (stem : List Nat) (final : Nat),
      Derives basis
        (wordOfPrefixFinal stem final)
        (wordOfPrefixFinal (prefixCapTwo stem) final)
  | [], final => Derives.refl _
  | letter :: suffix, final => by
      have suffixNormal := derivesNormalizePrefix suffix final
      have prefixed :
          Derives basis
            (wordOfPrefixFinal (letter :: suffix) final)
            (wordOfPrefixFinal
              (letter :: prefixCapTwo suffix) final) := by
        simpa [wordOfPrefixFinal] using
          Derives.prepend (Word.singleton letter) suffixNormal
      by_cases countSmall :
          (prefixCapTwo suffix).count letter < 2
      · have reduced :
            prefixCapTwo (letter :: suffix) =
              letter :: prefixCapTwo suffix := by
          simp [prefixCapTwo, countSmall]
        rw [reduced]
        exact prefixed
      · have countLe :
            (prefixCapTwo suffix).count letter <= 2 :=
          prefixCapTwo_count_le_two letter suffix
        have countEq :
            (prefixCapTwo suffix).count letter = 2 := by
          omega
        have reduced :
            prefixCapTwo (letter :: suffix) =
              prefixCapTwo suffix := by
          simp [prefixCapTwo, countSmall]
        rw [reduced]
        exact prefixed.trans <|
          derivesDeleteThirdPrefixCopy
            final letter (prefixCapTwo suffix) countEq
termination_by
  stem _ => stem.length

/-- Every word derives to its two-capped prefix form. -/
theorem derivesNormal (word : Word Nat) :
    let split := splitPrefixFinal word
    Derives basis word
      (wordOfPrefixFinal (prefixCapTwo split.1) split.2) := by
  dsimp
  have reconstruct := wordOfPrefixFinal_split word
  have normal := derivesNormalizePrefix
    (splitPrefixFinal word).1 (splitPrefixFinal word).2
  rw [reconstruct] at normal
  exact normal

private theorem perm_four_to_end
    (a b c d : Nat) (remainder : List Nat) :
    (a :: b :: c :: d :: remainder).Perm
      (remainder ++ [a, b, c, d]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

private theorem derivesDoubledFinalSwitchWithPrefix :
    forall (remainder : List Nat) (oldFinal newFinal : Nat),
      Derives basis
        (wordOfPrefixFinal
          (remainder ++ [oldFinal, oldFinal, newFinal, newFinal])
          oldFinal)
        (wordOfPrefixFinal
          (remainder ++ [oldFinal, oldFinal, newFinal, newFinal])
          newFinal)
  | [], oldFinal, newFinal => by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesDoubledFinalSwitch
          (Word.singleton oldFinal) (Word.singleton newFinal)
  | head :: tail, oldFinal, newFinal => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton head)
          (derivesDoubledFinalSwitchWithPrefix
            tail oldFinal newFinal)

/-- If two distinct candidate final letters both occur twice in the prefix,
the fifth law switches the literal final letter without changing the prefix. -/
theorem derivesDoubledFinalChoice
    (stem : List Nat) (oldFinal newFinal : Nat)
    (oldCount : stem.count oldFinal = 2)
    (newCount : stem.count newFinal = 2) :
    Derives basis
      (wordOfPrefixFinal stem oldFinal)
      (wordOfPrefixFinal stem newFinal) := by
  by_cases equal : oldFinal = newFinal
  · subst newFinal
    exact Derives.refl _
  · let afterOld := (stem.erase oldFinal).erase oldFinal
    let remainder := (afterOld.erase newFinal).erase newFinal
    have oldFront :
        stem.Perm (oldFinal :: oldFinal :: afterOld) := by
      simpa [afterOld] using
        perm_two_copies_front oldFinal stem oldCount
    have newAfterOld : afterOld.count newFinal = 2 := by
      rw [show afterOld =
        (stem.erase oldFinal).erase oldFinal by rfl,
        List.count_erase_of_ne (Ne.symm equal),
        List.count_erase_of_ne (Ne.symm equal), newCount]
    have newFront :
        afterOld.Perm (newFinal :: newFinal :: remainder) := by
      simpa [remainder] using
        perm_two_copies_front newFinal afterOld newAfterOld
    have arrangeFront :
        stem.Perm
          (oldFinal :: oldFinal :: newFinal :: newFinal :: remainder) :=
      oldFront.trans <|
        List.Perm.cons oldFinal <|
          List.Perm.cons oldFinal newFront
    have arrange :
        stem.Perm
          (remainder ++ [oldFinal, oldFinal, newFinal, newFinal]) :=
      arrangeFront.trans <|
        perm_four_to_end oldFinal oldFinal newFinal newFinal remainder
    exact
      (derivesPrefixPermutation arrange oldFinal).trans <|
        (derivesDoubledFinalSwitchWithPrefix
          remainder oldFinal newFinal).trans <|
            derivesPrefixPermutation arrange.symm newFinal

/-- Equal marker states with opposite final flags force both prefix counts to
the saturated value two. -/
theorem markerStateFrom_false_true_forces_two
    (leftCount rightCount : Nat)
    (same : markerStateFrom leftCount false =
      markerStateFrom rightCount true) :
    And (min leftCount 2 = 2) (min rightCount 2 = 2) := by
  cases leftCount with
  | zero =>
      cases rightCount with
      | zero => simp [markerStateFrom] at same
      | succ rightCount =>
          cases rightCount with
          | zero => simp [markerStateFrom] at same
          | succ rightCount => simp [markerStateFrom] at same
  | succ leftCount =>
      cases leftCount with
      | zero =>
          cases rightCount with
          | zero => simp [markerStateFrom] at same
          | succ rightCount =>
              cases rightCount with
              | zero => simp [markerStateFrom] at same
              | succ rightCount => simp [markerStateFrom] at same
      | succ leftCount =>
          cases rightCount with
          | zero => simp [markerStateFrom] at same
          | succ rightCount =>
              cases rightCount with
              | zero => simp [markerStateFrom] at same
              | succ rightCount => simp

/-- Symmetric form of `markerStateFrom_false_true_forces_two`. -/
theorem markerStateFrom_true_false_forces_two
    (leftCount rightCount : Nat)
    (same : markerStateFrom leftCount true =
      markerStateFrom rightCount false) :
    And (min leftCount 2 = 2) (min rightCount 2 = 2) := by
  have reversed := markerStateFrom_false_true_forces_two
    rightCount leftCount same.symm
  exact ⟨reversed.2, reversed.1⟩

/-- Equal marker vectors are constructively complete for the five displayed
laws. The proof caps both prefixes at two, identifies their multiplicity
vectors, and uses the fifth law exactly when the final choice is hidden. -/
theorem derivesOfSameMarkerSignature
    (left right : Word Nat)
    (same : SameMarkerSignature left right) :
    Derives basis left right := by
  let leftSplit := splitPrefixFinal left
  let rightSplit := splitPrefixFinal right
  let leftPrefix := prefixCapTwo leftSplit.1
  let rightPrefix := prefixCapTwo rightSplit.1
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = left :=
    wordOfPrefixFinal_split left
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = right :=
    wordOfPrefixFinal_split right
  have leftNormal :
      Derives basis left
        (wordOfPrefixFinal leftPrefix leftSplit.2) := by
    have normal := derivesNormalizePrefix leftSplit.1 leftSplit.2
    rw [leftReconstruct] at normal
    exact normal
  have rightNormal :
      Derives basis right
        (wordOfPrefixFinal rightPrefix rightSplit.2) := by
    have normal := derivesNormalizePrefix rightSplit.1 rightSplit.2
    rw [rightReconstruct] at normal
    exact normal
  have splitStates : forall tested,
      splitMarkerState leftSplit.1 leftSplit.2 tested =
        splitMarkerState rightSplit.1 rightSplit.2 tested := by
    intro tested
    have stateEq := same tested
    rw [← leftReconstruct, ← rightReconstruct,
      markerState_wordOfPrefixFinal,
      markerState_wordOfPrefixFinal] at stateEq
    exact stateEq
  have cappedCounts : forall tested,
      min (leftSplit.1.count tested) 2 =
        min (rightSplit.1.count tested) 2 := by
    intro tested
    have stateEq := congrArg prefixMultiplicityOfState
      (splitStates tested)
    simpa [splitMarkerState] using stateEq
  have prefixPermutation : leftPrefix.Perm rightPrefix := by
    rw [List.perm_iff_count]
    intro tested
    simpa [leftPrefix, rightPrefix, count_prefixCapTwo] using
      cappedCounts tested
  by_cases finalsEqual : leftSplit.2 = rightSplit.2
  · rw [← finalsEqual] at rightNormal
    exact leftNormal.trans <|
      (derivesPrefixPermutation
        prefixPermutation leftSplit.2).trans rightNormal.symm
  · have oldState :
        markerStateFrom (leftSplit.1.count leftSplit.2) true =
          markerStateFrom (rightSplit.1.count leftSplit.2) false := by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr (Ne.symm finalsEqual)] using
        splitStates leftSplit.2
    have newState :
        markerStateFrom (leftSplit.1.count rightSplit.2) false =
          markerStateFrom (rightSplit.1.count rightSplit.2) true := by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr finalsEqual] using
        splitStates rightSplit.2
    have oldTwo := markerStateFrom_true_false_forces_two
      (leftSplit.1.count leftSplit.2)
      (rightSplit.1.count leftSplit.2) oldState
    have newTwo := markerStateFrom_false_true_forces_two
      (leftSplit.1.count rightSplit.2)
      (rightSplit.1.count rightSplit.2) newState
    have oldCount : leftPrefix.count leftSplit.2 = 2 := by
      simpa [leftPrefix, count_prefixCapTwo] using oldTwo.1
    have newCount : leftPrefix.count rightSplit.2 = 2 := by
      simpa [leftPrefix, count_prefixCapTwo] using newTwo.1
    have switch := derivesDoubledFinalChoice
      leftPrefix leftSplit.2 rightSplit.2 oldCount newCount
    exact leftNormal.trans <| switch.trans <|
      (derivesPrefixPermutation
        prefixPermutation rightSplit.2).trans rightNormal.symm

end SemigroupBasis.CoRoots.S5_207
