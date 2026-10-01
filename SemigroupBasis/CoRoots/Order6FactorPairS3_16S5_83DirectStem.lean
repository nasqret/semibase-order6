import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_83Invariant
import SemigroupBasis.Examples.LeftRegularBandThree

/-!
# Protected stem normalization for the direct `S3_16` / `S5_83` family

The left-regular-band normalizer cannot be transported globally: its laws are
not identities of `S5_83`.  They do become derivable when two nonempty blocks
remain on the right.  This module proves that contextual fact directly and
uses it to retain the first occurrence of each stem letter before a fixed
terminal pair.

It also closes the two nonsingleton terminal strata.  If the penultimate letter
already occurs in the normalized stem `F`, then

`F p t = F F t`.

The final letter remains globally unique, so this representative is determined
by the first-occurrence sequence and the `S5_83` terminal suffix signature.
When the final letter is repeated, the terminal suffix is empty.  A second
block argument sends every `F p t` in that stratum to the square of its
first-occurrence sequence.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct

open SemigroupBasis
open SemigroupBasis.Examples

abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private theorem derivesDeleteOneBeforePair
    (letter : Nat) (middle suffix : List Nat)
    (penultimate final : Nat) :
    ListDerives
      ([letter] ++ middle ++ [letter] ++ suffix ++ [penultimate, final])
      ([letter] ++ middle ++ suffix ++ [penultimate, final]) := by
  cases middle with
  | nil =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesProtectedDeletion
            (Word.singleton letter)
            (wordOfPrefixFinal suffix penultimate)
            (Word.singleton final)
      simpa [wordOfPrefixFinal, toList_wordOfPrefixFinal,
        Word.singleton, Word.append,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        List.append_assoc] using core
  | cons middleHead middleTail =>
      have core :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesRegularContractionBeforeTwo
            (Word.singleton letter)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons
              middleHead middleTail)
            (wordOfPrefixFinal suffix penultimate)
            (Word.singleton final)
      simpa [wordOfPrefixFinal, toList_wordOfPrefixFinal,
        Word.singleton, Word.append,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        List.append_assoc] using core

/-- Delete every later occurrence of `letter` in `rest`, while retaining the
intervening letters and a fixed terminal pair. -/
private theorem derivesDeleteAfterBeforePair :
    forall (letter : Nat) (middle rest : List Nat)
      (penultimate final : Nat),
      ListDerives
        ([letter] ++ middle ++ rest ++ [penultimate, final])
        ([letter] ++ middle ++
          rest.filter (fun other => decide (other ≠ letter)) ++
          [penultimate, final])
  | letter, middle, [], penultimate, final => by
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          ([letter] ++ middle ++ [penultimate, final]))
  | letter, middle, other :: rest, penultimate, final => by
      by_cases equal : other = letter
      · subst other
        have first :=
          derivesDeleteOneBeforePair
            letter middle rest penultimate final
        have remaining :=
          derivesDeleteAfterBeforePair
            letter middle rest penultimate final
        simpa [List.append_assoc] using first.trans remaining
      · have remaining :=
          derivesDeleteAfterBeforePair
            letter (middle ++ [other]) rest penultimate final
        simpa [equal, List.append_assoc] using remaining
termination_by
  _ _ rest _ _ => rest.length

/-- Normalize a stem to its first-occurrence sequence without changing either
of the two protected terminal letters. -/
theorem listDerivesStemNormal :
    forall (stem : List Nat) (penultimate final : Nat),
      ListDerives
        (stem ++ [penultimate, final])
        (firstOccurrenceSequence stem ++ [penultimate, final])
  | [], penultimate, final => by
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | letter :: rest, penultimate, final => by
      have tailNormal :=
        listDerivesStemNormal rest penultimate final
      have prefixed := tailNormal.prepend [letter]
      have deleteLater :=
        derivesDeleteAfterBeforePair
          letter [] (firstOccurrenceSequence rest)
          penultimate final
      simpa [firstOccurrenceSequence, List.append_assoc] using
        prefixed.trans deleteLater
termination_by
  stem _ _ => stem.length

private theorem derivesOfListDerivesToList
    {left right : Word Nat}
    (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

/-- Word-level protected stem normal form. -/
theorem derivesStemNormal
    (stem : List Nat) (penultimate final : Nat) :
    Derives basis
      (SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
        stem penultimate final)
      (SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
        (firstOccurrenceSequence stem) penultimate final) := by
  have lists := listDerivesStemNormal stem penultimate final
  apply derivesOfListDerivesToList
  simpa [SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair,
    toList_wordOfPrefixFinal, List.append_assoc] using lists

/-! ## Unique-final canonicalization -/

/-- When `penultimate` already occurs in a stem `F`, duplicate `F` before a
globally unique final letter.  No nodup hypothesis is needed for the rewrite;
the normalizer supplies it when this lemma is used canonically. -/
theorem listDerivesUniqueFinalCanonical
    (stem : List Nat) (penultimate final : Nat)
    (member : penultimate ∈ stem) :
    ListDerives
      (stem ++ [penultimate, final])
      (stem ++ stem ++ [final]) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  cases after with
  | nil =>
      cases before with
      | nil =>
          simpa [shape] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
              (basis := basis) [penultimate, penultimate, final])
      | cons beforeHead beforeTail =>
          let beforeWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              beforeHead beforeTail
          have expand :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesSquareExpansion (Word.singleton penultimate)).context
                (beforeHead :: beforeTail) [final]
          have duplicateBefore :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              (derivesTerminalTransfer
                beforeWord (Word.singleton penultimate)).symm).append
                  [penultimate, final]
          have expanded :
              ListDerives
                ((beforeHead :: beforeTail) ++
                  [penultimate, penultimate, final])
                ((beforeHead :: beforeTail) ++ [penultimate, penultimate,
                  penultimate, final]) := by
            simpa [beforeWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, List.append_assoc] using expand
          have duplicated :
              ListDerives
                ((beforeHead :: beforeTail) ++ [penultimate, penultimate,
                  penultimate, final])
                ((beforeHead :: beforeTail) ++ [penultimate] ++
                  (beforeHead :: beforeTail) ++ [penultimate, final]) := by
            simpa [beforeWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, List.append_assoc] using
                duplicateBefore
          simpa [shape,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, List.append_assoc] using
              expanded.trans duplicated
  | cons afterHead afterTail =>
      let afterWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          afterHead afterTail
      let beforeWithMarker := wordOfPrefixFinal before penultimate
      have transfer :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesTerminalTransfer
            (Word.singleton penultimate) afterWord).context
              before [final]
      have expand :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesSquareExpansion afterWord).context
            (before ++ [penultimate]) [final]
      have duplicateBefore :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (derivesTerminalTransfer beforeWithMarker afterWord).symm).append
            (afterHead :: afterTail ++ [final])
      have transferred :
          ListDerives
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              [penultimate, final])
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              (afterHead :: afterTail) ++ [final]) := by
        simpa [afterWord,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.append, List.append_assoc] using transfer
      have expanded :
          ListDerives
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              (afterHead :: afterTail) ++ [final])
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              (afterHead :: afterTail) ++ (afterHead :: afterTail) ++
              [final]) := by
        simpa [afterWord,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.append, List.append_assoc] using expand
      have duplicated :
          ListDerives
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              (afterHead :: afterTail) ++ (afterHead :: afterTail) ++
              [final])
            (before ++ [penultimate] ++ (afterHead :: afterTail) ++
              before ++ [penultimate] ++ (afterHead :: afterTail) ++
              [final]) := by
        simpa [afterWord, beforeWithMarker, wordOfPrefixFinal,
          toList_wordOfPrefixFinal,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.append, List.append_assoc] using
            duplicateBefore
      simpa [shape, afterWord, beforeWithMarker, wordOfPrefixFinal,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          transferred.trans <| expanded.trans duplicated

/-- Word-level unique-final canonicalization. -/
theorem derivesUniqueFinalCanonical
    (stem : List Nat) (penultimate final : Nat)
    (member : penultimate ∈ stem) :
    Derives basis
      (SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
        stem penultimate final)
      (wordOfPrefixFinal (stem ++ stem) final) := by
  have lists :=
    listDerivesUniqueFinalCanonical stem penultimate final member
  apply derivesOfListDerivesToList
  simpa [SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair,
    toList_wordOfPrefixFinal, List.append_assoc] using lists

/-! ## Repeated-final canonicalization -/

/-- Delete a supported final letter after two copies of a stem.  Splitting the
stem around that letter leaves four block configurations; each is a direct
instance of terminal transfer, final expansion, or power expansion. -/
private theorem listDerivesDeleteFinalFromStemSquare
    (stem : List Nat) (final : Nat) (member : final ∈ stem) :
    ListDerives
      (stem ++ stem ++ [final])
      (stem ++ stem) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  cases before with
  | nil =>
      cases after with
      | nil =>
          have contracted :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesSquareExpansion (Word.singleton final)).symm
          simpa [shape, Word.singleton, Word.append,
            List.append_assoc] using contracted
      | cons afterHead afterTail =>
          let afterWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              afterHead afterTail
          let afterWithFinal :=
            wordOfPrefixFinal (afterHead :: afterTail) final
          have first :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              (derivesTerminalTransfer
                (Word.singleton final) afterWithFinal).symm
          have second :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              (derivesTerminalTransfer
                afterWord (Word.singleton final)).symm).prepend [final]
          have firstStep :
              ListDerives
                ([final] ++ (afterHead :: afterTail) ++ [final] ++
                  (afterHead :: afterTail) ++ [final])
                ([final] ++ (afterHead :: afterTail) ++ [final, final]) := by
            simpa [afterWithFinal, toList_wordOfPrefixFinal,
              Word.singleton, Word.append, List.append_assoc] using first
          have secondStep :
              ListDerives
                ([final] ++ (afterHead :: afterTail) ++ [final, final])
                ([final] ++ (afterHead :: afterTail) ++ [final] ++
                  (afterHead :: afterTail)) := by
            simpa [afterWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, List.append_assoc] using second
          simpa [shape,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, List.append_assoc] using
              firstStep.trans secondStep
  | cons beforeHead beforeTail =>
      cases after with
      | nil =>
          let beforeWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              beforeHead beforeTail
          let stemWord :=
            wordOfPrefixFinal (beforeHead :: beforeTail) final
          have first :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesTerminalTransfer
                (Word.singleton final) stemWord).prepend
                  (beforeHead :: beforeTail)
          have second :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesSquareExpansion stemWord).symm
          have firstStep :
              ListDerives
                ((beforeHead :: beforeTail) ++ [final] ++
                  (beforeHead :: beforeTail) ++ [final, final])
                (((beforeHead :: beforeTail) ++ [final]) ++
                  ((beforeHead :: beforeTail) ++ [final]) ++
                  ((beforeHead :: beforeTail) ++ [final])) := by
            simpa [stemWord, toList_wordOfPrefixFinal,
              Word.singleton, Word.append, List.append_assoc] using first
          have secondStep :
              ListDerives
                (((beforeHead :: beforeTail) ++ [final]) ++
                  ((beforeHead :: beforeTail) ++ [final]) ++
                  ((beforeHead :: beforeTail) ++ [final]))
                (((beforeHead :: beforeTail) ++ [final]) ++
                  ((beforeHead :: beforeTail) ++ [final])) := by
            simpa [stemWord, toList_wordOfPrefixFinal,
              Word.singleton, Word.append, List.append_assoc] using second
          simpa [shape, beforeWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, List.append_assoc] using
              firstStep.trans secondStep
      | cons afterHead afterTail =>
          let beforeWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              beforeHead beforeTail
          let afterWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              afterHead afterTail
          have first :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesTerminalTransfer
                (Word.singleton final) afterWord).prepend
                  ((beforeHead :: beforeTail) ++ [final] ++
                    (afterHead :: afterTail) ++
                    (beforeHead :: beforeTail))
          have second :=
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              (derivesFinalExpansion
                afterWord beforeWord (Word.singleton final)).symm).prepend
                  ((beforeHead :: beforeTail) ++ [final])
          have firstStep :
              ListDerives
                ((beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++ [final])
                ((beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (afterHead :: afterTail)) := by
            simpa [afterWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, List.append_assoc] using first
          have secondStep :
              ListDerives
                ((beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (afterHead :: afterTail))
                ((beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail) ++
                  (beforeHead :: beforeTail) ++ [final] ++
                  (afterHead :: afterTail)) := by
            simpa [beforeWord, afterWord,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, List.append_assoc] using second
          simpa [shape, beforeWord, afterWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, List.append_assoc] using
              firstStep.trans secondStep

/-- If a fresh penultimate letter is itself the repeated final letter, first
expand its terminal square and then reverse terminal transfer. -/
private theorem listDerivesFreshPenultimateRepeated
    (stem : List Nat) (penultimate : Nat) :
    ListDerives
      (stem ++ [penultimate, penultimate])
      ((stem ++ [penultimate]) ++ (stem ++ [penultimate])) := by
  cases stem with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head tail =>
      let stemWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail
      have expand :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          derivesSquareExpansion (Word.singleton penultimate)).prepend
            (head :: tail)
      have duplicate :=
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
          (derivesTerminalTransfer
            stemWord (Word.singleton penultimate)).symm).append
              [penultimate]
      have expandStep :
          ListDerives
            ((head :: tail) ++ [penultimate, penultimate])
            ((head :: tail) ++
              [penultimate, penultimate, penultimate]) := by
        simpa [Word.singleton, Word.append,
          List.append_assoc] using expand
      have duplicateStep :
          ListDerives
            ((head :: tail) ++
              [penultimate, penultimate, penultimate])
            (((head :: tail) ++ [penultimate]) ++
              ((head :: tail) ++ [penultimate])) := by
        simpa [stemWord,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.append, List.append_assoc] using duplicate
      simpa [stemWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
          expandStep.trans duplicateStep

/-- If the final letter already occurs in the stem while the penultimate is
fresh, expose the old final occurrence, triple the intervening nonempty block,
and reverse terminal transfer. -/
private theorem listDerivesFreshPenultimateOldFinal
    (stem : List Nat) (penultimate final : Nat)
    (member : final ∈ stem) :
    ListDerives
      (stem ++ [penultimate, final])
      ((stem ++ [penultimate]) ++ (stem ++ [penultimate])) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  let middleWord := wordOfPrefixFinal after penultimate
  let leftWord := wordOfPrefixFinal before final
  let middle := after ++ [penultimate]
  let left := before ++ [final]
  have transfer :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesTerminalTransfer
        (Word.singleton final) middleWord).prepend before
  have expand :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      derivesSquareExpansion middleWord).prepend (before ++ [final])
  have duplicate :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
      (derivesTerminalTransfer leftWord middleWord).symm).append
        (after ++ [penultimate])
  have transferStep :
      ListDerives
        (left ++ middle ++ [final])
        (left ++ middle ++ middle) := by
    simpa [left, middle, middleWord, toList_wordOfPrefixFinal,
      Word.singleton, Word.append, List.append_assoc] using transfer
  have expandStep :
      ListDerives
        (left ++ middle ++ middle)
        (left ++ middle ++ middle ++ middle) := by
    simpa [left, middle, middleWord, toList_wordOfPrefixFinal,
      Word.singleton, Word.append, List.append_assoc] using expand
  have duplicateStep :
      ListDerives
        (left ++ middle ++ middle ++ middle)
        ((left ++ middle) ++ (left ++ middle)) := by
    simpa [left, middle, middleWord, leftWord,
      toList_wordOfPrefixFinal, Word.singleton, Word.append,
      List.append_assoc] using duplicate
  simpa [shape, middle, left, middleWord, leftWord,
    toList_wordOfPrefixFinal,
    Word.singleton, Word.append, List.append_assoc] using
      transferStep.trans <| expandStep.trans duplicateStep

/-- Canonicalize the repeated-final stratum.  If the penultimate already
occurs in `stem`, the first-occurrence block is `stem`; otherwise it is
`stem ++ [penultimate]`.  The final result is two copies of that block. -/
theorem listDerivesRepeatedFinalCanonical
    (stem : List Nat) (penultimate final : Nat)
    (repeated : final = penultimate ∨ final ∈ stem) :
    ListDerives
      (stem ++ [penultimate, final])
      (if penultimate ∈ stem then
        stem ++ stem
      else
        (stem ++ [penultimate]) ++ (stem ++ [penultimate])) := by
  by_cases penultimateMember : penultimate ∈ stem
  · have finalMember : final ∈ stem := by
      rcases repeated with equal | member
      · simpa [equal] using penultimateMember
      · exact member
    have duplicate :=
      listDerivesUniqueFinalCanonical
        stem penultimate final penultimateMember
    have deleteFinal :=
      listDerivesDeleteFinalFromStemSquare stem final finalMember
    simpa [penultimateMember] using duplicate.trans deleteFinal
  · simp only [penultimateMember, if_false]
    rcases repeated with equal | finalMember
    · subst final
      exact listDerivesFreshPenultimateRepeated stem penultimate
    · exact
        listDerivesFreshPenultimateOldFinal
          stem penultimate final finalMember

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct
