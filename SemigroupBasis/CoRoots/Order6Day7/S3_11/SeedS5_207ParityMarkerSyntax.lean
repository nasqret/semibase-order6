import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank009
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009
import SemigroupBasis.CoRoots.S5_207Family
import SemigroupBasis.CoRoots.Order6FactorPairS2S5356Normal

/-!
# Exact D009 frozen-law parity-marker calculus

The existing complete five-law S5_207 basis changes occurrence parity and is
NOT transported.  All derivations below use the literal frozen eight-law
presentation.  Only the presentation-independent list arithmetic of the
existing threshold/parity reducer is reused.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6FactorPairS2S5356

private abbrev targetBasis : List (Identity Nat) := Rank009.basis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Direct substitution in the literal square-free frozen prefix swap. -/
theorem derivesPrefixSwap
    (first second suffix : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ suffix)
      ((second ++ first) ++ suffix) := by
  have primitive :
      Derives targetBasis (word 0 [1, 2]) (word 1 [0, 2]) :=
    Derives.fromBasis (e := Rank009.law03)
      (show Rank009.law03 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree first second suffix)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Delete exactly TWO prefix occurrences; no parity-changing cap is used. -/
theorem derivesFourPrefixToTwo
    (letter suffix : Word Nat) :
    Derives targetBasis
      ((((letter ++ letter) ++ letter) ++ letter) ++ suffix)
      ((letter ++ letter) ++ suffix) := by
  have primitive :
      Derives targetBasis (word 0 [0, 0, 0, 1]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Rank009.law01)
      (show Rank009.law01 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree letter suffix suffix)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Every prefix permutation is valid while its literal final stays fixed. -/
theorem derivesPrefixPermutation
    {left right : List Nat}
    (permutation : left.Perm right) (final : Nat) :
    Derives targetBasis
      (wordOfPrefixFinal left final)
      (wordOfPrefixFinal right final) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons head _ induction =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton head) induction
  | swap left right suffix =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesPrefixSwap
          (Word.singleton right) (Word.singleton left)
          (wordOfPrefixFinal suffix final)
  | trans _ _ first second => exact first.trans second

private theorem derivesContractLeadingFour
    (letter final : Nat) (remainder : List Nat) :
    Derives targetBasis
      (wordOfPrefixFinal
        (letter :: letter :: letter :: letter :: remainder) final)
      (wordOfPrefixFinal (letter :: letter :: remainder) final) := by
  simpa [wordOfPrefixFinal, Word.append_assoc] using
    derivesFourPrefixToTwo
      (Word.singleton letter) (wordOfPrefixFinal remainder final)

private theorem derivesDeleteFourthPrefixCopy
    (final letter : Nat) (reduced : List Nat)
    (countEqual : reduced.count letter = 3) :
    Derives targetBasis
      (wordOfPrefixFinal (letter :: reduced) final)
      (wordOfPrefixFinal (reduced.erase letter) final) := by
  let remainder := ((reduced.erase letter).erase letter).erase letter
  have firstErase : (reduced.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEqual]
  have secondErase : ((reduced.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, firstErase]
  have thirdErase : remainder.count letter = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondErase]
  have sourcePermutation :
      (letter :: reduced).Perm
        (letter :: letter :: letter :: letter :: remainder) := by
    rw [List.perm_iff_count]
    intro tested
    by_cases equal : tested = letter
    · subst tested
      simp [countEqual, thirdErase]
    · simp [remainder, equal, Ne.symm equal]
  have targetPermutation :
      (reduced.erase letter).Perm
        (letter :: letter :: remainder) := by
    rw [List.perm_iff_count]
    intro tested
    by_cases equal : tested = letter
    · subst tested
      simp [firstErase, thirdErase]
    · simp [remainder, equal, Ne.symm equal]
  exact (derivesPrefixPermutation sourcePermutation final).trans <|
    (derivesContractLeadingFour letter final remainder).trans <|
      derivesPrefixPermutation targetPermutation.symm final

/-- Normalize prefix counts to 0, 1, 2, or 3 without changing parity. -/
theorem derivesNormalizePrefix :
    ∀ (stem : List Nat) (final : Nat),
      Derives targetBasis
        (wordOfPrefixFinal stem final)
        (wordOfPrefixFinal (thresholdParityReduce stem) final)
  | [], final => Derives.refl _
  | letter :: suffix, final => by
      have suffixNormal := derivesNormalizePrefix suffix final
      have prefixed :
          Derives targetBasis
            (wordOfPrefixFinal (letter :: suffix) final)
            (wordOfPrefixFinal
              (letter :: thresholdParityReduce suffix) final) := by
        simpa [wordOfPrefixFinal] using
          Derives.prepend (Word.singleton letter) suffixNormal
      by_cases countSmall :
          (thresholdParityReduce suffix).count letter < 3
      · have reduced :
            thresholdParityReduce (letter :: suffix) =
              letter :: thresholdParityReduce suffix := by
          simp [thresholdParityReduce, countSmall]
        rw [reduced]
        exact prefixed
      · have countBound :=
          thresholdParityReduce_count_le_three letter suffix
        have countEqual :
            (thresholdParityReduce suffix).count letter = 3 := by
          omega
        have reduced :
            thresholdParityReduce (letter :: suffix) =
              (thresholdParityReduce suffix).erase letter := by
          simp [thresholdParityReduce, countSmall]
        rw [reduced]
        exact prefixed.trans <|
          derivesDeleteFourthPrefixCopy
            final letter (thresholdParityReduce suffix) countEqual
termination_by stem _ => stem.length

/-- Frozen `aaabbba = aabbb`: old/new prefix multiplicities 3,3. -/
theorem derivesFinalBridge33 (oldFinal newFinal : Nat) :
    Derives targetBasis
      (wordOfPrefixFinal
        [oldFinal, oldFinal, oldFinal,
          newFinal, newFinal, newFinal] oldFinal)
      (wordOfPrefixFinal
        [oldFinal, oldFinal, newFinal, newFinal] newFinal) := by
  have primitive :
      Derives targetBasis
        (word 0 [0, 0, 1, 1, 1, 0]) (word 0 [0, 1, 1, 1]) :=
    Derives.fromBasis (e := Rank009.law04)
      (show Rank009.law04 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree (Word.singleton oldFinal)
      (Word.singleton newFinal) (Word.singleton newFinal))
  simpa [word, instantiateThree, wordOfPrefixFinal, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Frozen `aabbba = aaabbb`: old/new prefix multiplicities 2,3. -/
theorem derivesFinalBridge23 (oldFinal newFinal : Nat) :
    Derives targetBasis
      (wordOfPrefixFinal
        [oldFinal, oldFinal, newFinal, newFinal, newFinal] oldFinal)
      (wordOfPrefixFinal
        [oldFinal, oldFinal, oldFinal, newFinal, newFinal] newFinal) := by
  have primitive :
      Derives targetBasis
        (word 0 [0, 1, 1, 1, 0]) (word 0 [0, 0, 1, 1, 1]) :=
    Derives.fromBasis (e := Rank009.law05)
      (show Rank009.law05 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree (Word.singleton oldFinal)
      (Word.singleton newFinal) (Word.singleton newFinal))
  simpa [word, instantiateThree, wordOfPrefixFinal, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Frozen `aabba = aaabbbb`: old/new prefix multiplicities 2,2. -/
theorem derivesFinalBridge22 (oldFinal newFinal : Nat) :
    Derives targetBasis
      (wordOfPrefixFinal
        [oldFinal, oldFinal, newFinal, newFinal] oldFinal)
      (wordOfPrefixFinal
        [oldFinal, oldFinal, oldFinal,
          newFinal, newFinal, newFinal] newFinal) := by
  have primitive :
      Derives targetBasis
        (word 0 [0, 1, 1, 0]) (word 0 [0, 0, 1, 1, 1, 1]) :=
    Derives.fromBasis (e := Rank009.law06)
      (show Rank009.law06 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree (Word.singleton oldFinal)
      (Word.singleton newFinal) (Word.singleton newFinal))
  simpa [word, instantiateThree, wordOfPrefixFinal, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Frozen `aaabba = aabbbb`: old/new prefix multiplicities 3,2. -/
theorem derivesFinalBridge32 (oldFinal newFinal : Nat) :
    Derives targetBasis
      (wordOfPrefixFinal
        [oldFinal, oldFinal, oldFinal, newFinal, newFinal] oldFinal)
      (wordOfPrefixFinal
        [oldFinal, oldFinal, newFinal, newFinal, newFinal] newFinal) := by
  have primitive :
      Derives targetBasis
        (word 0 [0, 0, 1, 1, 0]) (word 0 [0, 1, 1, 1, 1]) :=
    Derives.fromBasis (e := Rank009.law07)
      (show Rank009.law07 ∈ targetBasis by decide)
  have substituted := Derives.subst primitive
    (instantiateThree (Word.singleton oldFinal)
      (Word.singleton newFinal) (Word.singleton newFinal))
  simpa [word, instantiateThree, wordOfPrefixFinal, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private def eraseAtMostThree (letters : List Nat) (marker : Nat) : List Nat :=
  ((letters.erase marker).erase marker).erase marker

/-- Remove every copy of two markers from a 3-bounded normalized prefix. -/
def markerRemainder (letters : List Nat) (first second : Nat) : List Nat :=
  eraseAtMostThree (eraseAtMostThree letters first) second

private theorem markerRemainder_count_first
    (letters : List Nat) (first second : Nat)
    (different : first ≠ second)
    (countBound : letters.count first ≤ 3) :
    (markerRemainder letters first second).count first = 0 := by
  simp only [markerRemainder, eraseAtMostThree]
  rw [List.count_erase_of_ne different,
    List.count_erase_of_ne different,
    List.count_erase_of_ne different,
    List.count_erase_self, List.count_erase_self,
    List.count_erase_self]
  omega

private theorem markerRemainder_count_second
    (letters : List Nat) (first second : Nat)
    (different : first ≠ second)
    (countBound : letters.count second ≤ 3) :
    (markerRemainder letters first second).count second = 0 := by
  simp only [markerRemainder, eraseAtMostThree]
  rw [List.count_erase_self, List.count_erase_self,
    List.count_erase_self,
    List.count_erase_of_ne (Ne.symm different),
    List.count_erase_of_ne (Ne.symm different),
    List.count_erase_of_ne (Ne.symm different)]
  omega

private theorem markerRemainder_count_other
    (letters : List Nat) (first second tested : Nat)
    (notFirst : tested ≠ first) (notSecond : tested ≠ second) :
    (markerRemainder letters first second).count tested =
      letters.count tested := by
  simp [markerRemainder, eraseAtMostThree, notFirst, notSecond]

/-- Extract every marker copy while preserving the exact unmarked multiset. -/
theorem arrangeMarkers
    (letters : List Nat) (first second : Nat)
    (different : first ≠ second)
    (firstBound : letters.count first ≤ 3)
    (secondBound : letters.count second ≤ 3) :
    letters.Perm
      (markerRemainder letters first second ++
        List.replicate (letters.count first) first ++
        List.replicate (letters.count second) second) := by
  rw [List.perm_iff_count]
  intro tested
  by_cases firstEqual : tested = first
  · subst tested
    have remainder := markerRemainder_count_first
      letters first second different firstBound
    simp [List.count_append, List.count_replicate, remainder]
    intro equal
    exact False.elim (different equal.symm)
  · by_cases secondEqual : tested = second
    · subst tested
      have remainder := markerRemainder_count_second
        letters first second different secondBound
      simp [List.count_append, List.count_replicate, remainder]
      intro equal
      exact False.elim (different equal)
    · have remainder := markerRemainder_count_other
        letters first second tested firstEqual secondEqual
      simp [List.count_append, List.count_replicate, remainder]
      constructor
      · intro equal
        exact False.elim (firstEqual equal.symm)
      · intro equal
        exact False.elim (secondEqual equal.symm)

private theorem derivesBridgeWithPrefix
    {source target : List Nat} {oldFinal newFinal : Nat}
    (bridge :
      Derives targetBasis
        (wordOfPrefixFinal source oldFinal)
        (wordOfPrefixFinal target newFinal)) :
    ∀ remainder : List Nat,
      Derives targetBasis
        (wordOfPrefixFinal (remainder ++ source) oldFinal)
        (wordOfPrefixFinal (remainder ++ target) newFinal)
  | [] => by simpa using bridge
  | head :: tail => by
      simpa [wordOfPrefixFinal, List.append_assoc] using
        Derives.prepend (Word.singleton head)
          (derivesBridgeWithPrefix bridge tail)
termination_by remainder => remainder.length

/-- A saturated final can be switched in all four exact parity configurations. -/
theorem derivesSaturatedFinalChoice
    (stem : List Nat) (oldFinal newFinal : Nat)
    (different : oldFinal ≠ newFinal)
    (oldLower : 2 ≤ stem.count oldFinal)
    (oldUpper : stem.count oldFinal ≤ 3)
    (newLower : 2 ≤ stem.count newFinal)
    (newUpper : stem.count newFinal ≤ 3) :
    ∃ switched : List Nat,
      Derives targetBasis
        (wordOfPrefixFinal stem oldFinal)
        (wordOfPrefixFinal switched newFinal) := by
  let remainder := markerRemainder stem oldFinal newFinal
  have arranged := arrangeMarkers
    stem oldFinal newFinal different oldUpper newUpper
  have oldCases :
      stem.count oldFinal = 2 ∨ stem.count oldFinal = 3 := by
    omega
  have newCases :
      stem.count newFinal = 2 ∨ stem.count newFinal = 3 := by
    omega
  rcases oldCases with oldTwo | oldThree
  · rcases newCases with newTwo | newThree
    · have permutation :
          stem.Perm
            (remainder ++
              [oldFinal, oldFinal, newFinal, newFinal]) := by
        simpa [remainder, oldTwo, newTwo] using arranged
      refine ⟨remainder ++
        [oldFinal, oldFinal, oldFinal,
          newFinal, newFinal, newFinal], ?_⟩
      exact (derivesPrefixPermutation permutation oldFinal).trans <|
        derivesBridgeWithPrefix
          (derivesFinalBridge22 oldFinal newFinal) remainder
    · have permutation :
          stem.Perm
            (remainder ++
              [oldFinal, oldFinal, newFinal, newFinal, newFinal]) := by
        simpa [remainder, oldTwo, newThree] using arranged
      refine ⟨remainder ++
        [oldFinal, oldFinal, oldFinal, newFinal, newFinal], ?_⟩
      exact (derivesPrefixPermutation permutation oldFinal).trans <|
        derivesBridgeWithPrefix
          (derivesFinalBridge23 oldFinal newFinal) remainder
  · rcases newCases with newTwo | newThree
    · have permutation :
          stem.Perm
            (remainder ++
              [oldFinal, oldFinal, oldFinal, newFinal, newFinal]) := by
        simpa [remainder, oldThree, newTwo] using arranged
      refine ⟨remainder ++
        [oldFinal, oldFinal, newFinal, newFinal, newFinal], ?_⟩
      exact (derivesPrefixPermutation permutation oldFinal).trans <|
        derivesBridgeWithPrefix
          (derivesFinalBridge32 oldFinal newFinal) remainder
    · have permutation :
          stem.Perm
            (remainder ++
              [oldFinal, oldFinal, oldFinal,
                newFinal, newFinal, newFinal]) := by
        simpa [remainder, oldThree, newThree] using arranged
      refine ⟨remainder ++
        [oldFinal, oldFinal, newFinal, newFinal], ?_⟩
      exact (derivesPrefixPermutation permutation oldFinal).trans <|
        derivesBridgeWithPrefix
          (derivesFinalBridge33 oldFinal newFinal) remainder

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207
