import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank089
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_240
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_303Completeness

/-!
# An unrestricted first-order / literal-final seed for rank 089

The independently certified left-regular-band factor fixes the COMPLETE
first-occurrence order.  The independently complete `S5_303` factor fixes
singletons, the literal final letter, and the ordered terminal pair exactly
when that final letter is globally unique.

The exact frozen ten-law presentation replays both complete left-regular-band
laws behind two final guards.  A repeated final letter can always be duplicated
at the actual endpoint.  Consequently repeated-final words normalize behind
the resulting literal double guard, while unique-final words retain their
genuine, independently detected penultimate/final pair.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 7000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank089.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The frozen square expansion `xx = xxx`. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 01 contracts a repeated nonempty block before a real suffix. -/
theorem derivesPrefixContraction (first guard : Word Nat) :
    Derives basis ((first ++ first) ++ guard) (first ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first guard guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 02 duplicates a genuinely returned terminal block. -/
theorem derivesReturnedFinalDuplication (first between : Word Nat) :
    Derives basis
      ((first ++ between) ++ first)
      (((first ++ between) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first between between)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law 05 deletes a returned first block before a repeated guard. -/
theorem derivesReturnedGuardContraction
    (first second guard : Word Nat) :
    Derives basis
      ((((first ++ second) ++ first) ++ guard) ++ guard)
      (((first ++ second) ++ guard) ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 2]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- LRB regularity has the exact protected replay
`xyzw → xyzzw → xyxzzw → xyxzw`; a single guard is false. -/
theorem derivesLrbRegularUnderFinalPair
    (first second guard₁ guard₂ : Word Nat) :
    Derives basis
      (((first ++ second) ++ guard₁) ++ guard₂)
      ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
  have firstStep :
      Derives basis
        (((first ++ second) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ guard₁) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ second)
        (derivesPrefixContraction guard₁ guard₂).symm
  have secondStep :
      Derives basis
        ((((first ++ second) ++ guard₁) ++ guard₁) ++ guard₂)
        (((((first ++ second) ++ first) ++ guard₁) ++ guard₁) ++ guard₂) := by
    exact Derives.appendRight
      (derivesReturnedGuardContraction first second guard₁).symm guard₂
  have thirdStep :
      Derives basis
        (((((first ++ second) ++ first) ++ guard₁) ++ guard₁) ++ guard₂)
        ((((first ++ second) ++ first) ++ guard₁) ++ guard₂) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((first ++ second) ++ first)
        (derivesPrefixContraction guard₁ guard₂)
  exact firstStep.trans (secondStep.trans thirdStep)

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
  simp

/-- The COMPLETE two-law LRB calculus lifts behind two nonempty final guards,
through every substitution and both context constructors. -/
theorem liftLeftRegularBandUnderFinalPair
    {left right : Word Nat}
    (derivation : Derives leftRegularBandThreeBasis left right)
    (guard₁ guard₂ : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((left.bind substitution ++ guard₁) ++ guard₂)
      ((right.bind substitution ++ guard₁) ++ guard₂) := by
  induction derivation generalizing guard₁ guard₂ substitution with
  | fromBasis member =>
      simp only [leftRegularBandThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change Derives basis
          (((Word.singleton 0).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          (derivesPrefixContraction
            (substitution 0) (guard₁ ++ guard₂)).symm
      · change Derives basis
          (((Word.mk 0 [1]).bind substitution ++ guard₁) ++ guard₂)
          (((Word.mk 0 [1, 0]).bind substitution ++ guard₁) ++ guard₂)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesLrbRegularUnderFinalPair
            (substitution 0) (substitution 1) guard₁ guard₂
  | refl => exact Derives.refl _
  | symm _ hypothesis =>
      exact (hypothesis guard₁ guard₂ substitution).symm
  | trans _ _ first second =>
      exact (first guard₁ guard₂ substitution).trans
        (second guard₁ guard₂ substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (front.bind substitution)
          (hypothesis guard₁ guard₂ substitution)
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis (suffix.bind substitution) (guard₁ ++ guard₂)
          substitution
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard₁ guard₂
          (fun letter => (first letter).bind substitution)

/-- Equal COMPLETE first-occurrence sequences derive behind the unchanged
genuine final pair. -/
theorem derivesSameFirstOrderUnderFinalPair
    (left right guard₁ guard₂ : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList) :
    Derives basis
      ((left ++ guard₁) ++ guard₂)
      ((right ++ guard₁) ++ guard₂) := by
  simpa only [bind_singleton] using
    liftLeftRegularBandUnderFinalPair
      (SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.lrbDerives_of_sameFirstOccurrences
        left right order)
      guard₁ guard₂ Word.singleton

/-- Explicit terminal-pair rendering recovers its exact decomposition. -/
theorem terminalSplit_wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) :
    terminalSplit
        (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
          stem penultimate final) =
      .pair stem penultimate final := by
  simpa [SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
    TerminalSplit.renderWord] using
    terminalSplit_renderWord_inverse
      (.pair stem penultimate final)

/-- Normalize an arbitrary prefix by its FULL first-occurrence order while
retaining both independently relevant terminal variables. -/
theorem derivesStemFirstOccurrenceNormal
    (stem : List Nat) (penultimate final : Nat) :
    Derives basis
      (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
        stem penultimate final)
      (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
        (firstOccurrenceSequence stem) penultimate final) := by
  cases stem with
  | nil =>
      exact Derives.refl _
  | cons first rest =>
      let initialWord : Word Nat := ⟨first, rest⟩
      let normalWord : Word Nat :=
        ⟨first,
          (firstOccurrenceSequence rest).filter
            (fun letter => decide (letter ≠ first))⟩
      have lower :
          Derives leftRegularBandThreeBasis
            initialWord normalWord := by
        simpa [initialWord, normalWord, Word.toList,
          firstOccurrenceSequence] using
          lrbDerivesNormal initialWord
      have sourceShape :
          SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            (first :: rest) penultimate final =
            ((initialWord ++ Word.singleton penultimate) ++
              Word.singleton final) := by
        apply Word.toList_injective
        rw [SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair,
          Word.toList_append, Word.toList_append]
        simp [initialWord, Word.toList, List.append_assoc]
      have targetShape :
          SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            (firstOccurrenceSequence (first :: rest))
            penultimate final =
            ((normalWord ++ Word.singleton penultimate) ++
              Word.singleton final) := by
        apply Word.toList_injective
        rw [SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair,
          Word.toList_append, Word.toList_append]
        simp [normalWord, firstOccurrenceSequence,
          Word.toList, List.append_assoc]
      rw [sourceShape, targetShape]
      simpa only [bind_singleton] using
        liftLeftRegularBandUnderFinalPair lower
          (Word.singleton penultimate)
          (Word.singleton final) Word.singleton

/-- Every globally repeated final variable can be duplicated at the actual
endpoint; the first earlier occurrence uses law 02, and a terminal square
uses law 00. -/
theorem derivesAppendRepeatedFinal :
    ∀ (stem : List Nat) (penultimate final : Nat),
      (final = penultimate ∨ final ∈ stem) →
        Derives basis
          (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            stem penultimate final)
          (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            (stem ++ [penultimate]) final final)
  | [], penultimate, final, repeated => by
      have equal : final = penultimate := by
        simpa using repeated
      subst final
      simpa [SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, Word.append, Word.singleton,
        Word.append_assoc] using
        derivesPowerExpansion (Word.singleton penultimate)
  | first :: rest, penultimate, final, repeated => by
      by_cases firstFinal : first = final
      · subst first
        let between : Word Nat :=
          wordOfPrefixFinal rest penultimate
        have duplication :=
          derivesReturnedFinalDuplication
            (Word.singleton final) between
        have sourceShape :
            SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
                (final :: rest) penultimate final =
              ((Word.singleton final ++ between) ++
                Word.singleton final) := by
          apply Word.toList_injective
          rw [SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair,
            Word.toList_append, Word.toList_append,
            toList_wordOfPrefixFinal]
          simp [Word.toList, List.append_assoc]
        have targetShape :
            SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
                ((final :: rest) ++ [penultimate]) final final =
              (((Word.singleton final ++ between) ++
                Word.singleton final) ++ Word.singleton final) := by
          apply Word.toList_injective
          rw [SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair,
            Word.toList_append, Word.toList_append, Word.toList_append,
            toList_wordOfPrefixFinal]
          simp [Word.toList, List.append_assoc]
        rw [sourceShape, targetShape]
        exact duplication
      · have remaining : final = penultimate ∨ final ∈ rest := by
          rcases repeated with equal | member
          · exact Or.inl equal
          · have cases := (List.mem_cons.mp member)
            exact Or.inr (cases.resolve_left (Ne.symm firstFinal))
        have induction :=
          derivesAppendRepeatedFinal rest penultimate final remaining
        simpa [SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
          wordOfPrefixFinal, Word.append, Word.singleton,
          Word.append_assoc, List.append_assoc] using
          Derives.prepend (Word.singleton first) induction

/-- Duplicate the penultimate marker immediately before its unchanged genuine
final guard.  Every prefix is retained literally. -/
theorem derivesDuplicatePenultimateWithStem :
    ∀ (stem : List Nat) (penultimate final : Nat),
      Derives basis
        (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
          stem penultimate final)
        (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
          (stem ++ [penultimate]) penultimate final)
  | [], penultimate, final => by
      simpa [SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, Word.append, Word.singleton,
        Word.append_assoc] using
        (derivesPrefixContraction
          (Word.singleton penultimate) (Word.singleton final)).symm
  | first :: rest, penultimate, final => by
      simpa [SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair,
        wordOfPrefixFinal, Word.append, Word.singleton,
        Word.append_assoc, List.append_assoc] using
        Derives.prepend (Word.singleton first)
          (derivesDuplicatePenultimateWithStem rest penultimate final)

/-- Canonical representatives retain full first-occurrence order and the
literal final variable.  A unique final preserves its independently detected
penultimate marker; a repeated final provides two actual terminal guards. -/
noncomputable def canonicalList (word : Word Nat) : List Nat := by
  classical
  let order := firstOccurrenceSequence word.toList
  exact
    match terminalSplit word with
    | .singleton _ => order
    | .pair _ penultimate final =>
        if SemigroupBasis.CoRoots.S5_303.UniqueFinalPair
            word penultimate final then
          order.dropLast ++ [penultimate, final]
        else
          order ++ [final, final]

/-- The canonical list depends only on the independent FULL first-order
signature and the independently complete `S5_303` endpoint signature. -/
theorem canonicalList_eq_of_invariants
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature
        left right) :
    canonicalList left = canonicalList right := by
  classical
  cases leftSplit : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          simpa [canonicalList, leftSplit, rightSplit] using order
      | pair rightStem rightPenultimate rightFinal =>
          have singleton : IsSingletonWord left := by
            simp [IsSingletonWord, leftSplit]
          have impossible := signature.singleton.mp singleton
          simp [IsSingletonWord, rightSplit] at impossible
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplit : terminalSplit right with
      | singleton rightFinal =>
          have singleton : IsSingletonWord right := by
            simp [IsSingletonWord, rightSplit]
          have impossible := signature.singleton.mpr singleton
          simp [IsSingletonWord, leftSplit] at impossible
      | pair rightStem rightPenultimate rightFinal =>
          have rightFinalProperty :
              SemigroupBasis.CoRoots.S5_303.FinalLetter
                right leftFinal :=
            (signature.finalLetter leftFinal).mp <| by
              simp [SemigroupBasis.CoRoots.S5_303.FinalLetter,
                leftSplit]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter,
              rightSplit] using rightFinalProperty
          subst rightFinal
          by_cases leftUnique :
              SemigroupBasis.CoRoots.S5_303.UniqueFinalPair
                left leftPenultimate leftFinal
          · have rightUnique :=
              (signature.uniqueFinalPair
                leftPenultimate leftFinal).mp leftUnique
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  leftFinal = leftFinal ∧
                    leftFinal ≠ rightPenultimate ∧
                      leftFinal ∉ rightStem := by
              simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                rightSplit] using rightUnique
            have penultimates := rightParts.1
            subst rightPenultimate
            simp [canonicalList, leftSplit, rightSplit,
              leftUnique, rightUnique, order]
          · have rightNotUnique :
                ¬ SemigroupBasis.CoRoots.S5_303.UniqueFinalPair
                  right rightPenultimate leftFinal := by
              intro rightUnique
              have leftSpecific :=
                (signature.uniqueFinalPair
                  rightPenultimate leftFinal).mpr rightUnique
              have leftParts :
                  leftPenultimate = rightPenultimate ∧
                    leftFinal = leftFinal ∧
                      leftFinal ≠ leftPenultimate ∧
                        leftFinal ∉ leftStem := by
                simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
                  leftSplit] using leftSpecific
              have actual :
                  SemigroupBasis.CoRoots.S5_303.UniqueFinalPair
                    left leftPenultimate leftFinal := by
                simpa [leftParts.1] using leftSpecific
              exact leftUnique actual
            simp [canonicalList, leftSplit, rightSplit,
              leftUnique, rightNotUnique, order]

/-- Concrete decidable rendering for an explicit actual final pair. -/
theorem canonicalList_terminalPair
    (stem : List Nat) (penultimate final : Nat) :
    canonicalList
        (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
          stem penultimate final) =
      let order := firstOccurrenceSequence (stem ++ [penultimate, final])
      if final ≠ penultimate ∧ final ∉ stem then
        order.dropLast ++ [penultimate, final]
      else
        order ++ [final, final] := by
  classical
  simp [canonicalList, terminalSplit_wordOfTerminalPair,
    SemigroupBasis.CoRoots.S5_303.UniqueFinalPair,
    SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair]

/-- Every word reaches the canonical list.  Globally repeated finals acquire
their literal double guard, while globally unique finals preserve the exact
independently certified terminal pair. -/
theorem derivesToCanonical
    (word : Word Nat) :
    ∃ normal : Word Nat,
      normal.toList = canonicalList word ∧
        Derives basis word normal := by
  classical
  cases split : terminalSplit word with
  | singleton final =>
      have rendered := terminalSplit_renderWord word
      rw [split] at rendered
      have shape : word = Word.singleton final := by
        simpa [TerminalSplit.renderWord] using rendered.symm
      rw [shape]
      refine ⟨Word.singleton final, ?_, Derives.refl _⟩
      have singletonSplit :
          terminalSplit (Word.singleton final) = .singleton final := by
        rfl
      simp [canonicalList, singletonSplit,
        Word.toList, firstOccurrenceSequence]
  | pair stem penultimate final =>
      have rendered := terminalSplit_renderWord word
      rw [split] at rendered
      have shape :
          word = SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            stem penultimate final := by
        simpa [TerminalSplit.renderWord,
          SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair] using
          rendered.symm
      rw [shape]
      by_cases repeated : final = penultimate ∨ final ∈ stem
      · have finalPresent : final ∈ stem ++ [penultimate] := by
          rcases repeated with equal | present
          · simp [equal]
          · simp [present]
        have fullOrder :
            firstOccurrenceSequence
                (stem ++ [penultimate, final]) =
              firstOccurrenceSequence (stem ++ [penultimate]) := by
          rw [show stem ++ [penultimate, final] =
            (stem ++ [penultimate]) ++ [final] by
              simp [List.append_assoc]]
          rw [SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.firstOccurrenceSequence_append_final,
            if_pos finalPresent]
        have notUnique :
            ¬ (final ≠ penultimate ∧ final ∉ stem) := by
          intro unique
          rcases repeated with equal | present
          · exact unique.1 equal
          · exact unique.2 present
        have canonical :
            canonicalList
                (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
                  stem penultimate final) =
              firstOccurrenceSequence (stem ++ [penultimate]) ++
                [final, final] := by
          rw [canonicalList_terminalPair, if_neg notUnique, fullOrder]
        refine ⟨SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
          (firstOccurrenceSequence (stem ++ [penultimate]))
            final final, ?_, ?_⟩
        · rw [canonical,
            SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair]
        · exact
            (derivesAppendRepeatedFinal
              stem penultimate final repeated).trans <|
              derivesStemFirstOccurrenceNormal
                (stem ++ [penultimate]) final final
      · have unique : final ≠ penultimate ∧ final ∉ stem := by
          exact not_or.mp repeated
        have normalized :=
          derivesStemFirstOccurrenceNormal stem penultimate final
        by_cases penultimatePresent : penultimate ∈ stem
        · have fullOrder :
              firstOccurrenceSequence
                  (stem ++ [penultimate, final]) =
                firstOccurrenceSequence stem ++ [final] := by
            rw [show stem ++ [penultimate, final] =
              (stem ++ [penultimate]) ++ [final] by
                simp [List.append_assoc]]
            rw [SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.firstOccurrenceSequence_append_final,
              if_neg (by simp [unique.1, unique.2]),
              SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.firstOccurrenceSequence_append_final,
              if_pos penultimatePresent]
          have canonical :
              canonicalList
                  (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
                    stem penultimate final) =
                firstOccurrenceSequence stem ++
                  [penultimate, final] := by
            rw [canonicalList_terminalPair, if_pos unique, fullOrder]
            simp
          refine ⟨SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            (firstOccurrenceSequence stem) penultimate final, ?_,
              normalized⟩
          rw [canonical,
            SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair]
        · have fullOrder :
              firstOccurrenceSequence
                  (stem ++ [penultimate, final]) =
                (firstOccurrenceSequence stem ++ [penultimate]) ++
                  [final] := by
            rw [show stem ++ [penultimate, final] =
              (stem ++ [penultimate]) ++ [final] by
                simp [List.append_assoc]]
            rw [SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.firstOccurrenceSequence_append_final,
              if_neg (by simp [unique.1, unique.2]),
              SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.firstOccurrenceSequence_append_final,
              if_neg penultimatePresent]
          have canonical :
              canonicalList
                  (SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
                    stem penultimate final) =
                (firstOccurrenceSequence stem ++ [penultimate]) ++
                  [penultimate, final] := by
            rw [canonicalList_terminalPair, if_pos unique, fullOrder]
            simp
          refine ⟨SemigroupBasis.CoRoots.S5_303.wordOfTerminalPair
            (firstOccurrenceSequence stem ++ [penultimate])
              penultimate final, ?_, ?_⟩
          · rw [canonical,
              SemigroupBasis.CoRoots.S5_303.toList_wordOfTerminalPair]
          · exact normalized.trans <|
              derivesDuplicatePenultimateWithStem
                (firstOccurrenceSequence stem) penultimate final

/-- Exact unrestricted completeness from the independent FULL left order
and the independently complete `S5_303` endpoint signature. -/
theorem derives_of_signatures
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (signature :
      SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature
        left right) :
    Derives basis left right := by
  obtain ⟨leftNormal, leftList, leftDerivation⟩ :=
    derivesToCanonical left
  obtain ⟨rightNormal, rightList, rightDerivation⟩ :=
    derivesToCanonical right
  have sameCanonical :=
    canonicalList_eq_of_invariants left right order signature
  have normalEqual : leftNormal = rightNormal := by
    apply Word.toList_injective
    exact leftList.trans (sameCanonical.trans rightList.symm)
  exact leftDerivation.trans <| by
    rw [normalEqual]
    exact rightDerivation.symm

/-- The actual independently certified factors discharge every premise of
the unrestricted canonical completeness proof. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have order :=
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
      identity leftValid
  have actualRight :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup := by
    simpa [rightTable] using rightValid
  have signature :=
    SemigroupBasis.CoRoots.S5_303.valid_signature
      identity actualRight
  exact derives_of_signatures identity.lhs identity.rhs order signature

/-- Exact frozen ten-law intersection, assembled only after unrestricted
factor completeness is genuinely proved. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Reusable certified rank-089 family seed; no premise remains conditional. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The staged rank-089 representative is proved unconditionally. -/
theorem s6_7216_representative_basis :
    BasisFor S6_7216.table.semigroup basis :=
  S6_7216.representative_basis_of_normalizer normalizer

/-- Its opposite orientation retains the exact reversed frozen presentation. -/
theorem s6_7216_opposite_basis :
    BasisFor S6_7216.table.semigroup.opposite (reversedBasis basis) :=
  S6_7216.opposite_basis_of_normalizer normalizer

/-- Reviewed shared transport retains explicit displayed-law derivations and
independent unrestricted validity implications for both target factors. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank089.Seed
