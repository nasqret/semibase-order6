import SemigroupBasis.CoRoots.S5_345Normalization
import SemigroupBasis.CoRoots.S5_863

namespace SemigroupBasis.CoRoots.S5_863

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

private theorem listDerivesLeftEndpointContraction
    (pre suffix : List Nat) (x middleHead : Nat)
    (middleTail : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x] ++ (middleHead :: middleTail) ++ [x] ++ suffix)
      (pre ++ [x] ++ (middleHead :: middleTail) ++ [x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      (derivesLeftEndpointExpansion
        (Word.singleton x)
        (S5_107.listWordOfCons middleHead middleTail)).symm
  simpa [S5_107.listWordOfCons, List.append_assoc] using
    core.context pre suffix

/-- Contextual three-to-two contraction for a singleton letter. -/
theorem listDerivesPowerContract
    (pre suffix : List Nat) (x : Nat) :
    S5_107.ListDerives basis
      (pre ++ [x, x, x] ++ suffix)
      (pre ++ [x, x] ++ suffix) := by
  have core :=
    S5_107.ListDerives.ofWord <|
      derivesPowerContraction (Word.singleton x)
  simpa [List.append_assoc] using core.context pre suffix

/-- Gather two occurrences of `x` at the front of a segment whenever a
nonempty suffix follows the second occurrence. Empty middle context is the
reflexive case. -/
theorem listDerivesGatherNonfinal
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    S5_107.ListDerives basis
      (pre ++ [x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := basis) (pre ++ [x, x] ++ after ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨afterHead, afterTail, rfl⟩ :=
        List.exists_cons_of_ne_nil afterNonempty
      have core :=
        S5_107.ListDerives.ofWord <|
          (derivesDoubledInitialMove
            (Word.singleton x)
            (S5_107.listWordOfCons middleHead middleTail)
            (S5_107.listWordOfCons afterHead afterTail)).symm
      simpa [S5_107.listWordOfCons, List.append_assoc] using
        core.context pre suffix

/-- Delete a later copy of `x` once a leading square has been gathered. -/
theorem listDerivesAbsorbAfterSquare
    (pre suffix : List Nat) (x : Nat)
    (middle after : List Nat) (afterNonempty : after ≠ []) :
    S5_107.ListDerives basis
      (pre ++ [x, x] ++ middle ++ [x] ++ after ++ suffix)
      (pre ++ [x, x] ++ middle ++ after ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesPowerContract pre (after ++ suffix) x
  | cons middleHead middleTail =>
      have first :=
        listDerivesLeftEndpointContraction
          pre (after ++ suffix) x middleHead middleTail
      have second :=
        listDerivesGatherNonfinal
          pre suffix x (middleHead :: middleTail) after afterNonempty
      have firstStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix)
            (pre ++ [x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix) := by
        simpa [List.append_assoc] using first
      have secondStep :
          S5_107.ListDerives basis
            (pre ++ [x] ++
              (middleHead :: middleTail) ++ [x] ++ after ++ suffix)
            (pre ++ [x, x] ++
              (middleHead :: middleTail) ++ after ++ suffix) := by
        simpa [List.append_assoc] using second
      exact firstStep.trans secondStep

/-- Delete one interior occurrence between equal endpoint copies. -/
theorem listDerivesDeleteInteriorFinal
    (pre suffix : List Nat) (x : Nat)
    (left right : List Nat) :
    S5_107.ListDerives basis
      (pre ++ [x] ++ left ++ [x] ++ right ++ [x] ++ suffix)
      (pre ++ [x] ++ left ++ right ++ [x] ++ suffix) := by
  have gathered :=
    listDerivesGatherNonfinal
      pre suffix x left (right ++ [x]) (by simp)
  have gatheredStep :
      S5_107.ListDerives basis
        (pre ++ [x] ++ left ++ [x] ++ right ++ [x] ++ suffix)
        (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix) := by
    simpa [List.append_assoc] using gathered
  cases middleShape : left ++ right with
  | nil =>
      have finish := listDerivesPowerContract pre suffix x
      have finishStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix)
            (pre ++ [x] ++ (left ++ right) ++ [x] ++ suffix) := by
        rw [middleShape]
        simpa [List.append_assoc] using finish
      exact gatheredStep.trans <| by
        simpa [List.append_assoc] using finishStep
  | cons middleHead middleTail =>
      have finish :=
        listDerivesLeftEndpointContraction
          pre suffix x middleHead middleTail
      have finishStep :
          S5_107.ListDerives basis
            (pre ++ [x, x] ++ (left ++ right) ++ [x] ++ suffix)
            (pre ++ [x] ++ (left ++ right) ++ [x] ++ suffix) := by
        rw [middleShape]
        simpa [List.append_assoc] using finish
      exact gatheredStep.trans <| by
        simpa [List.append_assoc] using finishStep

/-- Remove every selected occurrence after a leading square. The final
nonempty suffix is retained verbatim. -/
theorem listDerivesAbsorbAllAfterSquare
    (x : Nat) :
    ∀ (pre rest suffix : List Nat), suffix ≠ [] →
      S5_107.ListDerives basis
        ([x, x] ++ pre ++ rest ++ suffix)
        ([x, x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ suffix)
  | pre, [], suffix, _ =>
      S5_107.ListDerives.refl _
  | pre, letter :: rest, suffix, suffixNonempty => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesAbsorbAfterSquare
            [] [] x pre (rest ++ suffix)
            (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare x pre rest suffix suffixNonempty
        have firstStep :
            S5_107.ListDerives basis
              ([x, x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have remaining :=
          listDerivesAbsorbAllAfterSquare
            x (pre ++ [letter]) rest suffix suffixNonempty
        simpa [equal, List.append_assoc] using remaining

/-- Gather the first selected occurrence into a leading square and remove all
remaining selected occurrences before a fixed nonempty suffix. -/
theorem listDerivesGatherAndDelete
    (x : Nat) :
    ∀ (pre rest suffix : List Nat), suffix ≠ [] → x ∈ rest →
      S5_107.ListDerives basis
        ([x] ++ pre ++ rest ++ suffix)
        ([x, x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ suffix)
  | _, [], _, _, member => by
      simp at member
  | pre, letter :: rest, suffix, suffixNonempty, member => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesGatherNonfinal
            [] [] x pre (rest ++ suffix)
            (by simp [suffixNonempty])
        have remaining :=
          listDerivesAbsorbAllAfterSquare
            x pre rest suffix suffixNonempty
        have firstStep :
            S5_107.ListDerives basis
              ([x] ++ pre ++ [x] ++ rest ++ suffix)
              ([x, x] ++ pre ++ rest ++ suffix) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have restMember : x ∈ rest := by
          simpa [equal, Ne.symm equal] using member
        have remaining :=
          listDerivesGatherAndDelete
            x (pre ++ [letter]) rest suffix
            suffixNonempty restMember
        simpa [equal, List.append_assoc] using remaining

/-- Delete every selected interior occurrence between equal endpoint copies. -/
theorem listDerivesDeleteInteriorCopies
    (x : Nat) :
    ∀ (pre rest : List Nat),
      S5_107.ListDerives basis
        ([x] ++ pre ++ rest ++ [x])
        ([x] ++ pre ++
          rest.filter (fun letter => decide (letter ≠ x)) ++ [x])
  | pre, [] =>
      S5_107.ListDerives.refl _
  | pre, letter :: rest => by
      by_cases equal : letter = x
      · subst letter
        have first :=
          listDerivesDeleteInteriorFinal [] [] x pre rest
        have remaining :=
          listDerivesDeleteInteriorCopies x pre rest
        have firstStep :
            S5_107.ListDerives basis
              ([x] ++ pre ++ [x] ++ rest ++ [x])
              ([x] ++ pre ++ rest ++ [x]) := by
          simpa [List.append_assoc] using first
        simpa [List.append_assoc] using firstStep.trans remaining
      · have remaining :=
          listDerivesDeleteInteriorCopies
            x (pre ++ [letter]) rest
        simpa [equal, List.append_assoc] using remaining

/-- Retaining only the first prefix occurrence of the final letter is a
derivable operation. -/
theorem listDerivesRetainFirstBeforeFinal
    (final : Nat) :
    ∀ letters : List Nat,
      S5_107.ListDerives basis
        (letters ++ [final])
        (S5_345.retainFirst final letters ++ [final])
  | [] =>
      S5_107.ListDerives.refl _
  | letter :: rest => by
      by_cases equal : letter = final
      · subst letter
        simpa [S5_345.retainFirst, List.append_assoc] using
          listDerivesDeleteInteriorCopies final [] rest
      · have remaining :=
          listDerivesRetainFirstBeforeFinal final rest
        simpa [S5_345.retainFirst, equal, List.append_assoc] using
          remaining.prepend [letter]

/-- Normalize a prefix to first-occurrence single/double blocks while keeping
a fixed final letter available as the nonempty right context. -/
theorem listDerivesDoubleCanonicalBeforeFinal
    (final : Nat) :
    ∀ letters : List Nat,
      S5_107.ListDerives basis
        (letters ++ [final])
        (S5_345.doubleCanonicalList letters ++ [final])
  | [] =>
      S5_107.ListDerives.refl _
  | letter :: rest => by
      let reduced := S5_345.doubleCanonicalList rest
      have first :=
        (listDerivesDoubleCanonicalBeforeFinal final rest).prepend [letter]
      by_cases member : letter ∈ reduced
      · have gathered :=
          listDerivesGatherAndDelete
            letter [] reduced [final] (by simp) member
        exact first.trans <| by
          simpa [S5_345.doubleCanonicalList, reduced, member,
            List.append_assoc] using gathered
      · simpa [S5_345.doubleCanonicalList, reduced, member,
          List.append_assoc] using first

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

/-- Every list derives directly to the `S5_863` core normal form. -/
theorem listDerivesCoreCanonical :
    ∀ letters : List Nat,
      S5_107.ListDerives basis letters
        (S5_345.coreCanonicalList letters)
  | [] =>
      S5_107.ListDerives.empty
  | head :: tail => by
      let letters := head :: tail
      let final := tail.getLastD head
      let beforeFinal := letters.dropLast
      have retained :=
        listDerivesRetainFirstBeforeFinal final beforeFinal
      have doubled :=
        listDerivesDoubleCanonicalBeforeFinal
          final (S5_345.retainFirst final beforeFinal)
      have normalized := retained.trans doubled
      have reconstruction :
          beforeFinal ++ [final] = letters := by
        simpa [beforeFinal, final, letters] using
          dropLast_append_final head tail
      rw [reconstruction] at normalized
      simpa [S5_345.coreCanonicalList, letters, final, beforeFinal] using
        normalized

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- The word represented by the basis-independent `S5_345` core canonical
list. -/
def coreCanonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head
    (S5_345.coreCanonicalList word.toList)

/-- Every word derives directly to the `S5_863` core normal form. -/
theorem derivesCoreCanonical (word : Word Nat) :
    Derives basis word (coreCanonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesCoreCanonical (Word.mk head tail).toList
      obtain
          ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            coreCanonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        unfold coreCanonicalWord
        rw [targetListEq]
        rfl
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

end SemigroupBasis.CoRoots.S5_863
