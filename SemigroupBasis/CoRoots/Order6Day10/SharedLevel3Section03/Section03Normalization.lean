import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseStep

/-! Full unbounded scan induction. The canonical list depends only on the
actual lower phase profile, the actual head, and whether that head repeats. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Normalization

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.S5_831
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseData
open SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseStep

abbrev basis := Section03Replay.basis

def repeatScan (head : Nat) (repeated : Bool) : List Nat → Bool
  | [] => repeated
  | letter :: rest => repeatScan head (nextRepeated head repeated letter) rest

theorem repeatScan_eq (head : Nat) (repeated : Bool) (letters : List Nat) :
    repeatScan head repeated letters = (repeated || decide (head ∈ letters)) := by
  induction letters generalizing repeated with
  | nil => simp [repeatScan]
  | cons letter rest ih =>
      rw [repeatScan, ih]
      by_cases same : letter = head
      · subst letter
        simp [nextRepeated]
      · simp [nextRepeated, same, Ne.symm same]

theorem derivesScan (head : Nat) (phases : List Phase) (repeated : Bool)
    (ok : StateOK head phases repeated) :
    ∀ letters : List Nat,
      D (renderState head phases repeated ++ letters)
        (renderState head (scanPhases phases letters) (repeatScan head repeated letters))
  | [] => by simpa [scanPhases, repeatScan] using (ListDerives.refl (basis := basis) (renderState head phases repeated))
  | letter :: rest => by
      have first := (stateStep ok letter).append rest
      have second := derivesScan head (phaseStep phases letter) (nextRepeated head repeated letter)
        (stateOK_step ok letter) rest
      simpa [scanPhases, repeatScan, List.append_assoc] using first.trans second

def canonicalList (word : Word Nat) : List Nat :=
  renderState word.head (phaseProfile word) (decide (word.head ∈ word.tail))

theorem derivesCanonical (word : Word Nat) : D word.toList (canonicalList word) := by
  cases word with
  | mk head tail =>
      have normalized := derivesScan head [⟨head, false⟩] false (initialStateOK head) tail
      simpa [canonicalList, renderState, renderPhases, renderPhase, phaseProfile,
        phaseProfileList, Word.toList, repeatScan_eq] using normalized

theorem canonical_eq_of_data {left right : Word Nat}
    (heads : left.head = right.head)
    (phases : phaseProfile left = phaseProfile right)
    (repeated : decide (left.head ∈ left.tail) = decide (right.head ∈ right.tail)) :
    canonicalList left = canonicalList right := by
  unfold canonicalList
  rw [heads] at repeated ⊢
  rw [phases, repeated]

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Normalization
