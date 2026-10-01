import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank103
import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.FinalMarkerThree

/-!
# Exact cap-three final-relative calculus for frozen rank 103

Both independently complete `S5_530` laws lift through an arbitrary unchanged
nonempty final context using the immutable three-law rank-103 envelope.
The fourth-to-third law, anchored fourth-occurrence contraction, and guarded
gather law additionally duplicate a final letter precisely when its word has
at least three occurrences. This threshold is sharp: a twice-occurring final
cannot be duplicated because the complete lower factor detects capped counts.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank103.basis

private abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_530.s5_530Basis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Frozen law 00 contracts a fourth copy of any nonempty block. -/
theorem derivesPowerContraction (first : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ first) ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := Rank103.law00)
      (show Rank103.law00 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 contracts the anchored fourth occurrence of a block. -/
theorem derivesAnchoredPowerContraction
    (first middle : Word Nat) :
    Derives targetBasis
      ((((first ++ first) ++ first) ++ middle) ++ first)
      (((first ++ first) ++ middle) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1, 0]) (Word.mk 0 [0, 1, 0]) :=
    Derives.fromBasis (e := Rank103.law01)
      (show Rank103.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 02 gathers a repeated first block before a nonempty suffix. -/
theorem derivesGatherUnderSuffix
    (first middle suffix : Word Nat) :
    Derives targetBasis
      (((first ++ middle) ++ first) ++ suffix)
      (((first ++ first) ++ middle) ++ suffix) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 0, 2]) (Word.mk 0 [0, 1, 2]) :=
    Derives.fromBasis (e := Rank103.law02)
      (show Rank103.law02 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first middle suffix)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- An initial double and a later occurrence create exactly one final copy. -/
theorem derivesDoubleFinalDuplication
    (first middle : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ middle) ++ first)
      ((((first ++ first) ++ middle) ++ first) ++ first) := by
  have expand :=
    (derivesAnchoredPowerContraction first middle).symm
  have gather :
      Derives targetBasis
        ((((first ++ first) ++ middle) ++ first) ++ first)
        ((((first ++ first) ++ first) ++ middle) ++ first) := by
    simpa [Word.append_assoc] using
      derivesGatherUnderSuffix first (first ++ middle) first
  exact expand.trans gather.symm

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

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Lift every unrestricted two-law lower derivation through a final guard. -/
theorem liftLowerUnderGuard
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives targetBasis
      (left.bind substitution ++ guard)
      (right.bind substitution ++ guard) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_530.s5_530Basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 0]).bind substitution ++ guard)
            ((Word.mk 0 [0, 0, 0]).bind substitution ++ guard)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesPowerContraction (substitution 0)).symm guard
      · change
          Derives targetBasis
            ((Word.mk 0 [0, 1]).bind substitution ++ guard)
            ((Word.mk 0 [1, 0]).bind substitution ++ guard)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          (derivesGatherUnderSuffix
            (substitution 0) (substitution 1) guard).symm
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction guard substitution).symm
  | trans _ _ first second =>
      exact
        (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction guard substitution)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind substitution ++ guard) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard
          (fun letter => (next letter).bind substitution)

/-- Identity-substitution specialization of the complete relative lift. -/
theorem liftLowerUnderGuardIdentity
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) :
    Derives targetBasis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using
    liftLowerUnderGuard derivation guard Word.singleton

private theorem listPowerExpansion (letter : Nat) :
    ListDerives [letter, letter, letter]
      [letter, letter, letter, letter] := by
  simpa [Word.toList, Word.singleton, Word.append] using
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesPowerContraction (Word.singleton letter)).symm

private theorem listDoubleGapFinalDuplication
    (letter gapFirst : Nat) (gapRest : List Nat) :
    ListDerives
      ([letter, letter] ++ (gapFirst :: gapRest) ++ [letter])
      ([letter, letter] ++ (gapFirst :: gapRest) ++ [letter, letter]) := by
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.toList, Word.singleton, Word.append,
    List.append_assoc] using
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesDoubleFinalDuplication
        (Word.singleton letter)
        (SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest))

private theorem listGatherGapBeforeFinal
    (letter gapFirst : Nat) (gapRest after : List Nat) :
    ListDerives
      ([letter] ++ (gapFirst :: gapRest) ++ [letter] ++ after ++ [letter])
      ([letter, letter] ++ (gapFirst :: gapRest) ++ after ++ [letter]) := by
  have gathered :=
    derivesGatherUnderSuffix
      (Word.singleton letter)
      (SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest)
      (wordOfPrefixFinal after letter)
  have listed :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord gathered
  simp only [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal] at listed
  simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.toList,
    List.append_assoc] using listed

/-- Two earlier occurrences are exactly what enables terminal duplication. -/
theorem listDuplicateFinalOfTwoEarlier
    (stem : List Nat) (final : Nat)
    (two : 2 ≤ stem.count final) :
    ListDerives (stem ++ [final]) (stem ++ [final, final]) := by
  induction stem with
  | nil =>
      simp at two
  | cons first rest induction =>
      by_cases same : first = final
      · subst first
        have positive : 0 < rest.count final := by
          simp only [List.count_cons_self] at two
          omega
        have seen : final ∈ rest :=
          List.count_pos_iff.mp positive
        obtain ⟨gap, after, shape⟩ := List.mem_iff_append.mp seen
        cases gap with
        | nil =>
            cases after with
            | nil =>
                simpa [shape] using listPowerExpansion final
            | cons next tail =>
                simpa [shape, List.append_assoc] using
                  listDoubleGapFinalDuplication final next tail
        | cons gapFirst gapRest =>
            have gather :=
              listGatherGapBeforeFinal final gapFirst gapRest after
            have duplicate :=
              listDoubleGapFinalDuplication
                final gapFirst (gapRest ++ after)
            have ungather :=
              listGatherGapBeforeFinal
                final gapFirst gapRest (after ++ [final])
            have duplicateAligned :
                ListDerives
                  ([final, final] ++ (gapFirst :: gapRest) ++
                    after ++ [final])
                  ([final, final] ++ (gapFirst :: gapRest) ++
                    after ++ [final, final]) := by
              simpa [List.append_assoc] using duplicate
            have ungatherAligned :
                ListDerives
                  ([final, final] ++ (gapFirst :: gapRest) ++
                    after ++ [final, final])
                  ([final] ++ (gapFirst :: gapRest) ++
                    [final] ++ after ++ [final, final]) := by
              simpa [List.append_assoc] using ungather.symm
            simpa [shape, List.append_assoc] using
              gather.trans (duplicateAligned.trans ungatherAligned)
      · have restTwo : 2 ≤ rest.count final := by
          simpa [same] using two
        have derived := induction restTwo
        simpa [List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
            [first] derived

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons first rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

/-- The exact split stores the genuine final variable. -/
theorem split_final_eq (word : Word Nat) :
    (splitPrefixFinal word).2 = word.final := by
  have reconstructed :=
    congrArg Word.final (wordOfPrefixFinal_split word)
  rw [final_wordOfPrefixFinal] at reconstructed
  exact reconstructed

/-- Exact list reconstruction for the unrestricted prefix/final split. -/
theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList =
      (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed :=
    congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

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

/-- Duplicate the exact final variable only in the certified cap-three case. -/
theorem derivesDuplicateFinalOfThree
    (word : Word Nat)
    (three : 3 ≤ word.toList.count word.final) :
    Derives targetBasis word
      (word ++ Word.singleton word.final) := by
  have splitCount :
      word.toList.count word.final =
        (splitPrefixFinal word).1.count word.final + 1 := by
    rw [toList_eq_splitPrefixFinal, split_final_eq,
      List.count_append]
    simp
  have stemTwo :
      2 ≤ (splitPrefixFinal word).1.count word.final := by
    omega
  have listed :=
    listDuplicateFinalOfTwoEarlier
      (splitPrefixFinal word).1 word.final stemTwo
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_singleton,
    toList_eq_splitPrefixFinal, split_final_eq]
  simpa [List.append_assoc] using listed

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_530
