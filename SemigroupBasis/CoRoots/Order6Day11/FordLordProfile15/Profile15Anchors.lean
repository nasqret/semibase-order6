import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Key

/-! The exact two-anchor local renderer from msg0447/0448: one retained last
copy, one retained first copy, and the least parity budget beside the first.
This is a single-letter step, not the global canonical reach theorem. -/

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis
open Moves

namespace Anchors

def erase (letter : Nat) (middle : List Nat) : List Nat :=
  middle.filter (fun tested => decide (tested ≠ letter))

def normal (letter : Nat) (middle : List Nat) : List Nat :=
  List.replicate (1 + tailBudget22 (middle.count letter + 2)) letter ++
    erase letter middle ++ [letter]

theorem doubleFinalToFirst (letter : Nat) (middle : List Nat) :
    L ([letter] ++ middle ++ [letter,letter]) ([letter,letter] ++ middle ++ [letter]) := by
  cases middle with
  | nil => exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons head tail =>
      simpa [Word.toList_append, Word.toList, Word.singleton, List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (rawLaw15 (Word.singleton letter) (Word.mk head tail)).symm

theorem derivesNormal (letter : Nat) (middle : List Nat) :
    L ([letter] ++ middle ++ [letter]) (normal letter middle) := by
  have gathered := gatherAndCap letter middle
  have bound : tailBudget22 (middle.count letter + 2) < 2 := Nat.mod_lt _ (by decide)
  by_cases zero : tailBudget22 (middle.count letter + 2) = 0
  · simpa [normal, erase, zero] using gathered
  · have one : tailBudget22 (middle.count letter + 2) = 1 := by omega
    have first : L ([letter] ++ middle ++ [letter])
        ([letter] ++ erase letter middle ++ [letter,letter]) := by
      simpa [erase, one] using gathered
    simpa [normal, one] using first.trans (doubleFinalToFirst letter (erase letter middle))

theorem sameKey (letter : Nat) (middle : List Nat) :
    KeyTheory.SameKey ([letter] ++ middle ++ [letter]) (normal letter middle) :=
  KeyTheory.listDerives_sameKey (derivesNormal letter middle)

theorem normal_ne_nil (letter : Nat) (middle : List Nat) : normal letter middle ≠ [] := by
  simp [normal]

theorem count_erase (letter : Nat) (middle : List Nat) : (erase letter middle).count letter = 0 := by
  apply List.count_eq_zero.mpr
  simp [erase]

theorem count_normal (letter : Nat) (middle : List Nat) :
    (normal letter middle).count letter = 2 + tailBudget22 (middle.count letter + 2) := by
  simp [normal, List.count_replicate, count_erase] <;> omega

theorem count_normal_bounded (letter : Nat) (middle : List Nat) :
    2 ≤ (normal letter middle).count letter ∧ (normal letter middle).count letter ≤ 3 := by
  rw [count_normal]
  unfold tailBudget22
  omega

/-- For this selected letter, erased context and capped count determine the
literal local render. This is independent of the input's length. -/
theorem normal_eq (letter : Nat) (left right : List Nat)
    (sameErasure : erase letter left = erase letter right)
    (sameCount : cap22 (left.count letter + 2) = cap22 (right.count letter + 2)) :
    normal letter left = normal letter right := by
  have budget : tailBudget22 (left.count letter + 2) = tailBudget22 (right.count letter + 2) := by
    unfold cap22 at sameCount
    rw [if_neg (by omega), if_neg (by omega)] at sameCount
    unfold tailBudget22
    omega
  simp only [normal, budget, sameErasure]

end Anchors
end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15
