import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395EvenInsertion

/-! A run whose letter already appeared reduces to one or two copies,
not to parity zero: its final occurrence must remain available. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PositiveRuns

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395EvenInsertion

def positiveCopies (copies : Nat) : Nat := Msg0446TailBudget.cap 1 copies

theorem positiveCopies_eq_iff (left right : Nat) :
    positiveCopies left = positiveCopies right ↔
      min left 1 = min right 1 ∧ left % 2 = right % 2 :=
  Msg0446TailBudget.cap_eq_iff 1 left right

theorem positiveCopies_zero : positiveCopies 0 = 0 := rfl

theorem positiveCopies_of_pos (copies : Nat) (positive : 0 < copies) :
    positiveCopies copies = (copies - 1) % 2 + 1 := by
  have above : ¬ copies < 1 := by omega
  simp [positiveCopies, Msg0446TailBudget.cap, above, Nat.add_comm]

theorem positiveCopies_le_two (copies : Nat) : positiveCopies copies ≤ 2 := by
  by_cases zero : copies = 0
  · simp [zero, positiveCopies_zero]
  · rw [positiveCopies_of_pos copies (by omega)]
    omega

theorem positiveCopies_positive_iff (copies : Nat) : 0 < positiveCopies copies ↔ 0 < copies := by
  by_cases zero : copies = 0
  · simp [zero, positiveCopies_zero]
  · rw [positiveCopies_of_pos copies (by omega)]
    omega

theorem positiveCopies_parity (copies : Nat) : positiveCopies copies % 2 = copies % 2 := by
  have parts := (Msg0446TailBudget.cap_eq_iff 1 (positiveCopies copies) copies).1
    (show Msg0446TailBudget.cap 1 (positiveCopies copies) = Msg0446TailBudget.cap 1 copies from by
      by_cases zero : copies = 0
      · simp [zero, positiveCopies_zero, Msg0446TailBudget.cap]
      · rw [positiveCopies_of_pos copies (by omega)]
        have bound : (copies - 1) % 2 < 2 := Nat.mod_lt _ (by decide)
        unfold Msg0446TailBudget.cap
        split <;> split <;> omega)
  exact parts.2

theorem normalizePositiveRun (letter : Nat) (before : List Nat) (copies : Nat)
    (positive : 0 < copies) :
    LD ([letter] ++ before ++ List.replicate copies letter)
      ([letter] ++ before ++ List.replicate (positiveCopies copies) letter) := by
  have split : copies - 1 + 1 = copies := by omega
  have source : List.replicate copies letter = List.replicate (copies-1) letter ++ [letter] := by
    rw [← split, replicateAdd]
    simp
  have target : List.replicate (positiveCopies copies) letter =
      List.replicate ((copies-1)%2) letter ++ [letter] := by
    rw [positiveCopies_of_pos copies positive, replicateAdd]
    simp
  rw [source, target]
  simpa [List.append_assoc] using normalizeAnchoredRun letter before [] (copies-1)

/-- Zero-length runs stay empty; positive runs retain their last occurrence. -/
theorem normalizeSeenRun (prefixWords suffix : List Nat) (letter copies : Nat)
    (seen : letter ∈ prefixWords) :
    LD (prefixWords ++ List.replicate copies letter ++ suffix)
      (prefixWords ++ List.replicate (positiveCopies copies) letter ++ suffix) := by
  by_cases zero : copies = 0
  · subst copies
    simp only [positiveCopies_zero, List.replicate_zero, List.append_nil]
    exact S5_107.ListDerives.refl _
  obtain ⟨before, after, shape⟩ := List.append_of_mem seen
  rw [shape]
  simpa [List.append_assoc] using
    (normalizePositiveRun letter after copies (by omega)).context before suffix

theorem compareSeenRuns (prefixWords suffix : List Nat) (letter left right : Nat)
    (seen : letter ∈ prefixWords)
    (support : min left 1 = min right 1) (parity : left % 2 = right % 2) :
    LD (prefixWords ++ List.replicate left letter ++ suffix)
      (prefixWords ++ List.replicate right letter ++ suffix) := by
  have same := (positiveCopies_eq_iff left right).2 ⟨support,parity⟩
  have first := normalizeSeenRun prefixWords suffix letter left seen
  have second := normalizeSeenRun prefixWords suffix letter right seen
  rw [same] at first
  exact first.trans second.symm

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395PositiveRuns
