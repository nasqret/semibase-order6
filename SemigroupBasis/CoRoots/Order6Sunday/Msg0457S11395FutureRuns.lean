import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SeenGap

/-! Suffix-aware run allocation: a retained future witness permits parity
zero; without it the final positive run retains one or two copies. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureRuns

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395PositiveRuns

def futureCopies (suffix : List Nat) (letter copies : Nat) : Nat :=
  if letter ∈ suffix then copies % 2 else positiveCopies copies

theorem futureCopies_zero (suffix : List Nat) (letter : Nat) : futureCopies suffix letter 0 = 0 := by
  simp [futureCopies, positiveCopies_zero]

theorem futureCopies_parity (suffix : List Nat) (letter copies : Nat) :
    futureCopies suffix letter copies % 2 = copies % 2 := by
  by_cases future : letter ∈ suffix
  · simp [futureCopies, future]
  · simp [futureCopies, future, positiveCopies_parity]

theorem positiveCopies_le_self (copies : Nat) : positiveCopies copies ≤ copies := by
  by_cases zero : copies = 0
  · simp [zero, positiveCopies_zero]
  · rw [positiveCopies_of_pos copies (by omega)]
    have bound := Nat.mod_le (copies - 1) 2
    omega

theorem futureCopies_le_self (suffix : List Nat) (letter copies : Nat) :
    futureCopies suffix letter copies ≤ copies := by
  by_cases future : letter ∈ suffix
  · simpa [futureCopies, future] using Nat.mod_le copies 2
  · simpa [futureCopies, future] using positiveCopies_le_self copies

theorem futureCopies_le_two (suffix : List Nat) (letter copies : Nat) :
    futureCopies suffix letter copies ≤ 2 := by
  by_cases future : letter ∈ suffix
  · simp only [futureCopies, if_pos future]
    have bound := Nat.mod_lt copies (show 0 < 2 by decide)
    omega
  · simpa [futureCopies, future] using positiveCopies_le_two copies

theorem minOne_eq_of_positive_iff (left right : Nat) (same : 0 < left ↔ 0 < right) :
    min left 1 = min right 1 := by
  by_cases positive : 0 < left
  · have other := same.mp positive
    omega
  · have other : ¬ 0 < right := fun h => positive (same.mpr h)
    omega

theorem futureCopies_idempotent (suffix : List Nat) (letter copies : Nat) :
    futureCopies suffix letter (futureCopies suffix letter copies) = futureCopies suffix letter copies := by
  by_cases future : letter ∈ suffix
  · simp [futureCopies, future]
  · simp only [futureCopies, if_neg future]
    exact (positiveCopies_eq_iff _ _).2
      ⟨minOne_eq_of_positive_iff _ _ (positiveCopies_positive_iff copies), positiveCopies_parity copies⟩

theorem futureCopies_support (suffix : List Nat) (letter copies : Nat) :
    (0 < futureCopies suffix letter copies ∨ letter ∈ suffix) ↔
      (0 < copies ∨ letter ∈ suffix) := by
  by_cases future : letter ∈ suffix
  · simp [future]
  · simp [futureCopies, future, positiveCopies_positive_iff]

theorem futureCopies_eq_of_observations (suffix : List Nat) (letter left right : Nat)
    (support : (0 < left ∨ letter ∈ suffix) ↔ (0 < right ∨ letter ∈ suffix))
    (parity : left % 2 = right % 2) : futureCopies suffix letter left = futureCopies suffix letter right := by
  by_cases future : letter ∈ suffix
  · simpa [futureCopies, future] using parity
  · simp only [futureCopies, if_neg future]
    apply (positiveCopies_eq_iff _ _).2
    exact ⟨minOne_eq_of_positive_iff _ _ (by simpa [future] using support), parity⟩

/-- The selected future witness is in suffix; extra may contain arbitrary
additional letters. The right-hand count depends only on suffix. -/
theorem normalizeFutureRun (prefixWords extra suffix : List Nat) (letter copies : Nat)
    (seen : letter ∈ prefixWords) :
    LD (prefixWords ++ List.replicate copies letter ++ extra ++ suffix)
      (prefixWords ++ List.replicate (futureCopies suffix letter copies) letter ++ extra ++ suffix) := by
  by_cases future : letter ∈ suffix
  · simp only [futureCopies, if_pos future]
    obtain ⟨before, between, pastShape⟩ := List.append_of_mem seen
    obtain ⟨after, rest, futureShape⟩ := List.append_of_mem future
    rw [pastShape, futureShape]
    simpa [List.append_assoc] using
      (normalizeAnchoredRun letter between (extra ++ after) copies).context before rest
  · simp only [futureCopies, if_neg future]
    simpa [List.append_assoc] using normalizeSeenRun prefixWords (extra ++ suffix) letter copies seen

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395FutureRuns
