import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenSwaps

/-! A seen letter's pair can cross a letter having a future witness.
The latter may be a first introduction. Neither empty substitutions nor
an unrestricted permutation principle are used. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395MixedPairs

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesMixedShort : Derives basis law04.lhs law04.rhs :=
  Derives.fromBasis (by decide)

theorem derivesMixedAfter : Derives basis law10.lhs law10.rhs :=
  Derives.fromBasis (by decide)

theorem movePairWithAdjacentPast (letter crossed : Nat) (after : List Nat) :
    LD ([letter,letter,letter,crossed] ++ after ++ [crossed])
      ([letter,crossed,letter,letter] ++ after ++ [crossed]) := by
  cases after with
  | nil =>
      have proof := S5_107.ListDerives.ofWord (derivesMixedShort.subst
        (threeWords (Word.singleton letter) (Word.singleton crossed) (Word.singleton letter)))
      simp only [Word.toList_bind] at proof
      simpa [law04, threeWords, Word.toList, Word.singleton] using proof
  | cons head tail =>
      have proof := S5_107.ListDerives.ofWord (derivesMixedAfter.subst
        (threeWords (Word.singleton letter) (Word.singleton crossed)
          (S5_107.listWordOfCons head tail)))
      simp only [Word.toList_bind] at proof
      simpa [law10, threeWords, Word.toList, Word.singleton,
        S5_107.listWordOfCons, List.append_assoc] using proof

/-- Both gaps are arbitrary, including empty. The pair retains a past
witness and the crossed letter retains a future witness. -/
theorem movePairBetweenMixedWitnesses (letter crossed : Nat) (before after : List Nat) :
    LD ([letter] ++ before ++ [letter,letter,crossed] ++ after ++ [crossed])
      ([letter] ++ before ++ [crossed,letter,letter] ++ after ++ [crossed]) := by
  have first : LD ([letter] ++ before ++ [letter,letter,crossed] ++ after ++ [crossed])
      ([letter] ++ before ++ [letter,letter,letter,letter,crossed] ++ after ++ [crossed]) := by
    simpa [List.append_assoc] using
      (insertPairBetween letter [] []).context ([letter] ++ before) ([crossed] ++ after ++ [crossed])
  have second : LD ([letter] ++ before ++ [letter,letter,letter,letter,crossed] ++ after ++ [crossed])
      ([letter] ++ before ++ [letter,letter,crossed,letter,letter] ++ after ++ [crossed]) := by
    simpa [List.append_assoc] using
      (movePairWithAdjacentPast letter crossed after).context ([letter] ++ before ++ [letter]) []
  have third : LD ([letter] ++ before ++ [letter,letter,crossed,letter,letter] ++ after ++ [crossed])
      ([letter] ++ before ++ [crossed,letter,letter] ++ after ++ [crossed]) := by
    simpa [List.append_assoc] using
      ((insertPairBetween letter before [crossed]).context [] ([letter] ++ after ++ [crossed])).symm
  exact first.trans (second.trans third)

theorem movePairPastFuture (prefixWords suffix : List Nat) (letter crossed : Nat)
    (seen : letter ∈ prefixWords) (future : crossed ∈ suffix) :
    LD (prefixWords ++ [letter,letter,crossed] ++ suffix)
      (prefixWords ++ [crossed,letter,letter] ++ suffix) := by
  obtain ⟨before, between, pastShape⟩ := List.append_of_mem seen
  obtain ⟨after, rest, futureShape⟩ := List.append_of_mem future
  rw [pastShape, futureShape]
  simpa [List.append_assoc] using
    (movePairBetweenMixedWitnesses letter crossed between after).context before rest

theorem movePairPastSeen (prefixWords suffix : List Nat) (letter crossed : Nat)
    (seen : letter ∈ prefixWords) (crossedSeen : crossed ∈ prefixWords) :
    LD (prefixWords ++ [letter,letter,crossed] ++ suffix)
      (prefixWords ++ [crossed,letter,letter] ++ suffix) := by
  have first : LD (prefixWords ++ [letter,letter,crossed] ++ suffix)
      (prefixWords ++ [letter,crossed,letter] ++ suffix) := by
    simpa [List.append_assoc] using swapSeen (prefixWords ++ [letter]) suffix letter crossed
      (List.mem_append_left _ seen) (List.mem_append_left _ crossedSeen)
  have second : LD (prefixWords ++ [letter,crossed,letter] ++ suffix)
      (prefixWords ++ [crossed,letter,letter] ++ suffix) := by
    simpa [List.append_assoc] using swapSeen prefixWords ([letter] ++ suffix) letter crossed seen crossedSeen
  exact first.trans second

/-- This is the guarded crossing rule, not an unrestricted swap. -/
theorem movePairPastWitnessed (prefixWords suffix : List Nat) (letter crossed : Nat)
    (seen : letter ∈ prefixWords) (witness : crossed ∈ prefixWords ∨ crossed ∈ suffix) :
    LD (prefixWords ++ [letter,letter,crossed] ++ suffix)
      (prefixWords ++ [crossed,letter,letter] ++ suffix) := by
  rcases witness with past | future
  · exact movePairPastSeen prefixWords suffix letter crossed seen past
  · exact movePairPastFuture prefixWords suffix letter crossed seen future

theorem mixedPairWord (letter crossed : Nat) (before after : List Nat) :
    Derives basis
      ⟨letter, before ++ [letter,letter,crossed] ++ after ++ [crossed]⟩
      ⟨letter, before ++ [crossed,letter,letter] ++ after ++ [crossed]⟩ := by
  exact (show LD
    (letter :: (before ++ [letter,letter,crossed] ++ after ++ [crossed]))
    (letter :: (before ++ [crossed,letter,letter] ++ after ++ [crossed])) from
      by simpa using movePairBetweenMixedWitnesses letter crossed before after).toWord

theorem mixedPairPreservesSignature (letter crossed : Nat) (before after : List Nat) :
    Msg0457S11395Observations.SameSignature
      ⟨letter, before ++ [letter,letter,crossed] ++ after ++ [crossed]⟩
      ⟨letter, before ++ [crossed,letter,letter] ++ after ++ [crossed]⟩ :=
  Msg0457S11395Signature.derives_preserve_signature (mixedPairWord letter crossed before after)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395MixedPairs
