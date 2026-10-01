import SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035GuardedReplay

/-!
# Rank035: unrestricted repeated-final pair insertion

The lower M18 pair bank may cross any word only in its own calculus.
The joint calculus first creates its own repeated-final square, replays the
lower derivation behind that nonempty guard, commutes two genuine squares,
and removes the original guard. No unguarded lower rewrite is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035TailInsertion

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035Shape
open SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035GuardedReplay

private abbrev ListDerives := SemigroupBasis.CoRoots.S5_107.ListDerives basis

private theorem derives_of_listDerives_toList
    {sigma : List (Identity Nat)} (left right : Word Nat)
    (derivation : SemigroupBasis.CoRoots.S5_107.ListDerives sigma left.toList right.toList) :
    Derives sigma left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

theorem toList_eq_splitPrefixFinal (word : Word Nat) :
    word.toList = (splitPrefixFinal word).1 ++ [(splitPrefixFinal word).2] := by
  have reconstructed := congrArg Word.toList (wordOfPrefixFinal_split word)
  rw [toList_wordOfPrefixFinal] at reconstructed
  exact reconstructed.symm

theorem listDerivesFinalSelfPair (stem : List Nat) (final : Nat) (seen : final ∈ stem) :
    ListDerives (stem ++ [final]) (stem ++ [final, final, final]) := by
  obtain ⟨before, gap, shape⟩ := List.mem_iff_append.mp seen
  cases gap with
  | nil =>
      have expanded := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesPower (Word.singleton final))
      simpa [shape, Word.toList_append, Word.toList_singleton, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before expanded
  | cons gapFirst gapRest =>
      let gapWord := SemigroupBasis.CoRoots.S5_107.listWordOfCons gapFirst gapRest
      have expanded := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
        (derivesFinalSelfPair (Word.singleton final) gapWord)
      simpa [shape, gapWord, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.toList, Word.toList_append, Word.toList_singleton, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend before expanded

theorem derivesDuplicateRepeatedFinalPair (word : Word Nat)
    (seen : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1) :
    Derives basis word
      ((word ++ Word.singleton (splitPrefixFinal word).2) ++ Word.singleton (splitPrefixFinal word).2) := by
  apply derives_of_listDerives_toList
  rw [Word.toList_append, Word.toList_append, Word.toList_singleton, toList_eq_splitPrefixFinal]
  simpa [List.append_assoc] using
    listDerivesFinalSelfPair (splitPrefixFinal word).1 (splitPrefixFinal word).2 seen

private theorem two_occurrence_split (selected : Nat) :
    ∀ letters : List Nat, 2 ≤ letters.count selected →
      ∃ before gap after,
        letters = before ++ selected :: (gap ++ selected :: after)
  | [], repeated => by simp at repeated
  | first :: rest, repeated => by
      by_cases same : first = selected
      · subst first
        have positive : 0 < rest.count selected := by
          have counts : (selected :: rest).count selected = rest.count selected + 1 := by simp
          rw [counts] at repeated
          omega
        obtain ⟨gap, after, shape⟩ :=
          List.mem_iff_append.mp (List.count_pos_iff.mp positive)
        exact ⟨[], gap, after, by simp [shape]⟩
      · have restRepeated : 2 ≤ rest.count selected := by
          simpa [List.count_cons, same, Ne.symm same] using repeated
        obtain ⟨before, gap, after, shape⟩ := two_occurrence_split selected rest restRepeated
        exact ⟨first :: before, gap, after, by simp [shape]⟩

/-- This conversion is only from the sound joint system into the complete lower one. -/
theorem listDerivesToLower {left right : List Nat} (derivation : ListDerives left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives lowerBasis left right := by
  cases derivation with
  | empty => exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | @words leftHead rightHead leftTail rightTail derivation =>
      let identity : Identity Nat :=
        ⟨SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftTail,
         SemigroupBasis.CoRoots.S5_107.listWordOfCons rightHead rightTail⟩
      have valid : identity.SatisfiedBy rightTable.semigroup := derivation.sound modelsRight
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.words
        (SemigroupBasis.CoRoots.S5_254.basisFor.2 identity valid)

/-- Append a pair of any repeated letter in the independent M18 calculus. -/
theorem lowerListDerivesAppendSeenPair (letters : List Nat) (selected : Nat)
    (repeated : 2 ≤ letters.count selected) :
    SemigroupBasis.CoRoots.S5_107.ListDerives lowerBasis letters (letters ++ [selected, selected]) := by
  obtain ⟨before, gap, after, shape⟩ := two_occurrence_split selected letters repeated
  have core := listDerivesToLower
    (listDerivesFinalSelfPair (selected :: gap) selected (by simp))
  have expanded := SemigroupBasis.CoRoots.S5_107.ListDerives.context before after core
  have across := SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
    (before ++ selected :: (gap ++ [selected]))
    (SemigroupBasis.CoRoots.S5_254.listDerivesPairAcross selected after)
  have first : SemigroupBasis.CoRoots.S5_107.ListDerives lowerBasis letters
      ((before ++ selected :: (gap ++ [selected])) ++ [selected, selected] ++ after) := by
    simpa [shape, List.append_assoc] using expanded
  have second : SemigroupBasis.CoRoots.S5_107.ListDerives lowerBasis
      ((before ++ selected :: (gap ++ [selected])) ++ [selected, selected] ++ after)
      (letters ++ [selected, selected]) := by
    simpa [shape, List.append_assoc] using across
  exact first.trans second

theorem lowerDerivesAppendSeenPair (word : Word Nat) (selected : Nat)
    (repeated : 2 ≤ word.toList.count selected) :
    Derives lowerBasis word ((word ++ Word.singleton selected) ++ Word.singleton selected) := by
  apply derives_of_listDerives_toList
  simpa [Word.toList_append, Word.toList_singleton, List.append_assoc] using
    lowerListDerivesAppendSeenPair word.toList selected repeated

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Unrestricted pair insertion in the repeated-final stratum of the joint theory. -/
theorem derivesAppendSeenPair (word : Word Nat) (selected : Nat)
    (finalRepeated : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1)
    (selectedRepeated : 2 ≤ word.toList.count selected) :
    Derives basis word ((word ++ Word.singleton selected) ++ Word.singleton selected) := by
  let anchor := Word.singleton (splitPrefixFinal word).2
  let chosen := Word.singleton selected
  have self : Derives basis word (word ++ (anchor ++ anchor)) := by
    simpa [anchor, Word.append_assoc] using derivesDuplicateRepeatedFinalPair word finalRepeated
  have lower : Derives lowerBasis word (word ++ (chosen ++ chosen)) := by
    simpa [chosen, Word.append_assoc] using lowerDerivesAppendSeenPair word selected selectedRepeated
  have lifted : Derives basis (word ++ (anchor ++ anchor))
      ((word ++ (chosen ++ chosen)) ++ (anchor ++ anchor)) := by
    simpa only [bind_singleton] using
      liftLowerWithSuffix lower (anchor ++ anchor) Word.singleton
  have commute : Derives basis ((word ++ (chosen ++ chosen)) ++ (anchor ++ anchor))
      ((word ++ (anchor ++ anchor)) ++ (chosen ++ chosen)) := by
    simpa only [Word.append_assoc] using Derives.prepend word (derivesSquaresCommute chosen anchor)
  have remove : Derives basis ((word ++ (anchor ++ anchor)) ++ (chosen ++ chosen))
      (word ++ (chosen ++ chosen)) := Derives.appendRight self.symm (chosen ++ chosen)
  simpa [chosen, Word.append_assoc] using self.trans (lifted.trans (commute.trans remove))

end SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank035TailInsertion
