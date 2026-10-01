import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay

/-! Explicit protected-initial-marker moves. Every old-letter collapse and
square-to-final step is lower-calculus work replayed after a nonempty guard. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03MarkerMoves

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay

abbrev basis := Section03Replay.basis

theorem getLastD_append_word (before : List Nat) (word : Word Nat) (fallback : Nat) :
    (before ++ word.toList).getLastD fallback = word.final := by
  induction before generalizing fallback with
  | nil =>
      cases word with
      | mk head tail =>
          change (head :: tail).getLastD fallback = tail.getLastD head
          simp only [List.getLastD_cons]
  | cons letter rest ih =>
      simpa only [List.cons_append, List.getLastD_cons] using ih letter

theorem duplicateRepeatedFinal (pre : List Nat) (letter : Nat) (member : letter ∈ pre) :
    D (pre ++ [letter]) ((pre ++ [letter]) ++ [letter]) := by
  obtain ⟨before, middle, rfl⟩ := List.mem_iff_append.mp member
  cases middle with
  | nil =>
      simpa [Word.toList, Word.singleton, Word.append, List.append_assoc] using
        (ListDerives.ofWord (rawPower (Word.singleton letter))).prepend before
  | cons next rest =>
      simpa [Word.toList, Word.singleton, Word.append, List.append_assoc] using
        (ListDerives.ofWord (rawReturnDuplicate (Word.singleton letter) (Word.mk next rest))).prepend before

/-- Move the protected head between two occupied phases. The common middle
has two visible head returns; the second displayed edge removes the first. -/
theorem relocateMarker (head : Nat) (front back : Word Nat) :
    D (head :: (front.toList ++ head :: (back.toList ++ [back.final])))
      (head :: (front.toList ++ [front.final] ++ back.toList ++ [head])) := by
  have finalEq : (front.toList ++ head :: back.toList).getLastD head = back.final := by
    simpa [List.append_assoc] using getLastD_append_word (front.toList ++ [head]) back head
  have first : D (head :: (front.toList ++ head :: (back.toList ++ [head])))
      (head :: (front.toList ++ head :: (back.toList ++ [back.final]))) := by
    have step := appendOldTail head head (front.toList ++ head :: back.toList) (by simp)
    rw [finalEq] at step
    simpa only [List.cons_append, List.append_assoc] using step
  have second : D (head :: (front.toList ++ head :: (back.toList ++ [head])))
      (head :: (front.toList ++ front.toList ++ back.toList ++ [head])) := by
    simpa [Word.toList_append, Word.toList_singleton, List.append_assoc] using
      ListDerives.ofWord (rawMarkerTransfer (Word.singleton head) front back)
  have third : D (head :: (front.toList ++ front.toList ++ back.toList ++ [head]))
      (head :: (front.toList ++ [front.final] ++ back.toList ++ [head])) := by
    simpa [Word.toList_append, Word.toList_singleton, List.append_assoc] using
      (replayLowerList (ListDerives.ofWord (derivesSquareToFinal front))
        (Word.singleton head)).append (back.toList ++ [head])
  exact first.symm.trans (second.trans third)

/-- At a final occupied phase, a newly returned head replaces the redundant
phase-label copy. Both word blocks remain nonempty in the displayed step. -/
theorem markerAtFinalDouble (head : Nat) (front : Word Nat) :
    D (head :: (front.toList ++ [front.final, head])) (head :: (front.toList ++ [head])) := by
  have first : D (head :: (front.toList ++ [head]))
      (head :: (front.toList ++ front.toList ++ [head])) := by
    simpa [Word.toList_append, Word.toList_singleton, List.append_assoc] using
      ListDerives.ofWord (rawReturnMiddleDuplicate (Word.singleton head) front)
  have second : D (head :: (front.toList ++ front.toList ++ [head]))
      (head :: (front.toList ++ [front.final, head])) := by
    simpa [Word.toList_append, Word.toList_singleton, List.append_assoc] using
      (replayLowerList (ListDerives.ofWord (derivesSquareToFinal front))
        (Word.singleton head)).append [head]
  exact (first.trans second).symm

/-- Ordinary phase rendering needs only the displayed power contraction to
record one more old letter at its final phase. -/
theorem markPlainLast (fallback : Nat) :
    ∀ phases : List Phase, phases ≠ [] →
      D (renderPhases phases ++ [(renderPhases phases).getLastD fallback])
        (renderPhases (markLastDoubled phases))
  | [], nonempty => False.elim (nonempty rfl)
  | phase :: rest, _ => by
      cases rest with
      | nil =>
          rcases phase with ⟨label, doubled⟩
          cases doubled with
          | false =>
              simpa [renderPhases, renderPhase, markLastDoubled] using
                (ListDerives.refl (basis := basis) [label, label])
          | true =>
              simpa [renderPhases, renderPhase, markLastDoubled,
                Word.toList_append, Word.toList_singleton] using
                ListDerives.ofWord (rawPower (Word.singleton label)).symm
      | cons next tail =>
          have induction := markPlainLast ((renderPhase phase).getLastD fallback)
            (next :: tail) (by simp)
          cases phase.doubled <;> cases next.doubled <;>
            simpa [renderPhases, renderPhase, markLastDoubled, List.append_assoc] using
              induction.prepend (renderPhase phase)

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03MarkerMoves
