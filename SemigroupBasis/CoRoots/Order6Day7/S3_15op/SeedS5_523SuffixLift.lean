import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank100
import SemigroupBasis.CoRoots.S5_523Normalization
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Exact five-law suffix lift for the frozen rank-100 intersection

The complete `S5_523` calculus has five displayed laws. Every law lifts through
an unchanged nonempty final context using only the seven immutable rank-100
laws; the gather law requires the explicit head-contraction/repeated-deletion
diamond. A three-step terminal-duplication chain removes the temporary final
context from both long endpoints. The independently certified lower signature
separates literal words from the long stratum.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_523

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank100.basis

private abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_523.basis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Frozen law 00 expands an arbitrary nonempty triple block. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ first)
      (((first ++ first) ++ first) ++ first) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [0, 0])
        (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := Rank100.law00)
      (show Rank100.law00 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Frozen law 01 removes the third initial block before a suffix. -/
theorem derivesPrefixCap (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ first) ++ second)
      ((first ++ first) ++ second) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [0, 0, 1])
        (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := Rank100.law01)
      (show Rank100.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Frozen law 02 changes an initial duplicate into an alternating pair. -/
theorem derivesAlternation (first second : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ second)
      (((first ++ second) ++ first) ++ second) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [0, 1])
        (Word.mk 0 [1, 0, 1]) :=
    Derives.fromBasis (e := Rank100.law02)
      (show Rank100.law02 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Frozen law 03 transfers a duplicated block to its neighbor. -/
theorem derivesTransfer (first second : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ second)
      ((first ++ second) ++ second) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [0, 1])
        (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := Rank100.law03)
      (show Rank100.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Frozen law 05 contracts an initial duplicate before two nonempty blocks. -/
theorem derivesHeadContraction
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [0, 1, 2])
        (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank100.law05)
      (show Rank100.law05 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Frozen law 06 deletes an interior repetition of the initial block. -/
theorem derivesRepeatedDeletion
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ first) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives targetBasis (Word.mk 0 [1, 0, 2])
        (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank100.law06)
      (show Rank100.law06 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Three explicit displayed steps duplicate the final block of a long word. -/
theorem derivesFinalDuplication
    (first second final : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ final)
      (((first ++ second) ++ final) ++ final) := by
  have expand := (derivesHeadContraction first second final).symm
  have alternate :=
    Derives.appendRight (derivesAlternation first second) final
  have transfer :
      Derives targetBasis
        ((((first ++ second) ++ first) ++ second) ++ final)
        (((first ++ second) ++ final) ++ final) := by
    simpa [Word.append_assoc] using
      derivesTransfer (first ++ second) final
  exact expand.trans (alternate.trans transfer)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay every certified lower derivation before one unchanged final block. -/
theorem liftLowerWithSuffix
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives targetBasis
      (left.bind substitution ++ suffix)
      (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_523.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 0]).bind substitution ++ suffix)
            ((Word.mk 0 [0, 0, 0]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesPowerExpansion (substitution 0)) suffix
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 1]).bind substitution ++ suffix)
            ((Word.mk 0 [1, 0]).bind substitution ++ suffix)
        have contraction :=
          derivesHeadContraction
            (substitution 0) (substitution 1) suffix
        have deletion :=
          derivesRepeatedDeletion
            (substitution 0) (substitution 1) suffix
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          contraction.trans deletion.symm
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 1]).bind substitution ++ suffix)
            ((Word.mk 0 [1, 1]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesTransfer (substitution 0) (substitution 1)) suffix
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 1]).bind substitution ++ suffix)
            ((Word.mk 0 [0, 0, 1]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesPrefixCap (substitution 0) (substitution 1)).symm
            suffix
      · change
          Derives targetBasis
            ((Word.mk 0 [1, 2]).bind substitution ++ suffix)
            ((Word.mk 0 [0, 1, 2]).bind substitution ++ suffix)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesHeadContraction
              (substitution 0) (substitution 1) (substitution 2)).symm
            suffix
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction suffix substitution).symm
  | trans _ _ first second =>
      exact
        (first suffix substitution).trans (second suffix substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction suffix substitution)
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (final.bind substitution ++ suffix) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction suffix
          (fun letter => (next letter).bind substitution)

/-- Any word of length at least three can duplicate its exact final letter. -/
theorem derivesWordFinalDuplication
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives targetBasis word (word ++ Word.singleton word.final) := by
  generalize splitEquation : splitPrefixFinal word = split
  obtain ⟨stem, final⟩ := split
  have rebuilt : wordOfPrefixFinal stem final = word := by
    simpa only [splitEquation] using wordOfPrefixFinal_split word
  have lists : stem ++ [final] = word.toList := by
    simpa only [toList_wordOfPrefixFinal] using
      congrArg Word.toList rebuilt
  have lengths : (stem ++ [final]).length = word.toList.length :=
    congrArg List.length lists
  cases stem with
  | nil =>
      simp at lengths
      omega
  | cons first prefixTail =>
      cases prefixTail with
      | nil =>
          simp at lengths
          omega
      | cons second rest =>
          let middle : Word Nat := ⟨second, rest⟩
          have shape :
              word =
                ((Word.singleton first ++ middle) ++
                  Word.singleton final) := by
            apply Word.toList_injective
            change word.toList = (first :: second :: rest) ++ [final]
            exact lists.symm
          rw [shape]
          simpa only [Word.final_append] using
            derivesFinalDuplication
              (Word.singleton first) middle (Word.singleton final)

/-- The certified long first-occurrence signature never shortens below three. -/
theorem longSignatureLength
    (first second third : Nat) (rest : List Nat) :
    3 ≤
      (SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
        (first :: second :: third :: rest)).length := by
  cases occurrence :
      SemigroupBasis.Examples.firstOccurrenceSequence
        (first :: second :: third :: rest) with
  | nil =>
      simp [SemigroupBasis.Examples.firstOccurrenceSequence] at occurrence
  | cons initial further =>
      cases further with
      | nil =>
          simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
            occurrence]
      | cons next remaining =>
          cases remaining with
          | nil =>
              simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
                occurrence]
          | cons last tail =>
              simp [SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList,
                occurrence]

/-- Equality of certified lower signatures gives literal or long endpoints. -/
theorem signatureShortOrLong
    (left right : Word Nat)
    (same :
      SemigroupBasis.CoRoots.S5_523.SameLongFirstOccurrenceSignature
        left right) :
    left = right ∨
      (3 ≤ left.toList.length ∧ 3 ≤ right.toList.length) := by
  change
    SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
        left.toList =
      SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
        right.toList at same
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | mk rightHead rightTail =>
              cases rightTail with
              | nil =>
                  left
                  apply Word.toList_injective
                  change [leftHead] = [rightHead]
                  change [leftHead] = [rightHead] at same
                  exact same
              | cons rightSecond rightRest =>
                  cases rightRest with
                  | nil =>
                      have lengths := congrArg List.length same
                      change 1 = 2 at lengths
                      omega
                  | cons rightThird rightMore =>
                      change
                        [leftHead] =
                          SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
                              (rightHead :: rightSecond ::
                                rightThird :: rightMore) at same
                      have lengths := congrArg List.length same
                      have long :=
                        longSignatureLength
                          rightHead rightSecond rightThird rightMore
                      simp only [List.length_cons, List.length_nil] at lengths
                      omega
      | cons leftSecond leftRest =>
          cases leftRest with
          | nil =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil =>
                      have lengths := congrArg List.length same
                      change 2 = 1 at lengths
                      omega
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          left
                          apply Word.toList_injective
                          change
                            [leftHead, leftSecond] =
                              [rightHead, rightSecond]
                          change
                            [leftHead, leftSecond] =
                              [rightHead, rightSecond] at same
                          exact same
                      | cons rightThird rightMore =>
                          change
                            [leftHead, leftSecond] =
                              SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
                                  (rightHead :: rightSecond ::
                                    rightThird :: rightMore) at same
                          have lengths := congrArg List.length same
                          have long :=
                            longSignatureLength
                              rightHead rightSecond rightThird rightMore
                          simp only [List.length_cons, List.length_nil] at lengths
                          omega
          | cons leftThird leftMore =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil =>
                      change
                        SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
                              (leftHead :: leftSecond ::
                                leftThird :: leftMore) =
                          [rightHead] at same
                      have lengths := congrArg List.length same
                      have long :=
                        longSignatureLength
                          leftHead leftSecond leftThird leftMore
                      simp only [List.length_cons, List.length_nil] at lengths
                      omega
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          change
                            SemigroupBasis.CoRoots.S5_523.longFirstOccurrenceNormalList
                                  (leftHead :: leftSecond ::
                                    leftThird :: leftMore) =
                              [rightHead, rightSecond] at same
                          have lengths := congrArg List.length same
                          have long :=
                            longSignatureLength
                              leftHead leftSecond leftThird leftMore
                          simp only [List.length_cons, List.length_nil] at lengths
                          omega
                      | cons rightThird rightMore =>
                          right
                          constructor <;> simp [Word.toList]

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_523
