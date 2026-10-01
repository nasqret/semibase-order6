import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlyPower
import SemigroupBasis.Examples.LeftRegularBandThree

/-! The canonical first-occurrence block word and its exact capped key.
The length component is min(length,3), not raw length. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Examples

def remainder (letter : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun x => decide (x ≠ letter))

theorem remainder_length_lt (letter : Nat) (tail : List Nat) :
    (remainder letter tail).length < (letter :: tail).length := by
  have bound : (remainder letter tail).length ≤ tail.length := List.filter_sublist.length_le
  simp only [List.length_cons]
  omega

theorem remainder_count_ne (letter tested : Nat) (letters : List Nat) (ne : tested ≠ letter) :
    (remainder letter letters).count tested = letters.count tested :=
  List.count_filter (by simpa using ne)

theorem remainder_length_count (letter : Nat) (letters : List Nat) :
    (remainder letter letters).length + letters.count letter = letters.length := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      simp [remainder] at ih
      by_cases equal : head = letter
      · subst head
        simp [remainder] <;> omega
      · simp [remainder, equal, List.count_cons_of_ne equal] <;> omega

theorem order_cons (letter : Nat) (tail : List Nat) :
    firstOccurrenceSequence (letter :: tail) =
      letter :: firstOccurrenceSequence (remainder letter tail) := by
  simp only [remainder, firstOccurrenceSequence_filter, firstOccurrenceSequence]

theorem order_eq_nil_iff (letters : List Nat) :
    firstOccurrenceSequence letters = [] ↔ letters = [] := by
  cases letters <;> simp [firstOccurrenceSequence]

theorem render_congr (order : List Nat) (left right : Nat → Nat)
    (same : ∀ letter ∈ order, left letter = right letter) :
    order.flatMap (fun letter => List.replicate (left letter) letter) =
      order.flatMap (fun letter => List.replicate (right letter) letter) := by
  induction order with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons]
      rw [same head (by simp)]
      congr 1
      exact ih (fun letter member => same letter (by simp [member]))

def blocksTwo (letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).flatMap
    (fun letter => List.replicate (min (letters.count letter) 2) letter)

theorem blocksTwo_cons (letter : Nat) (tail : List Nat) :
    blocksTwo (letter :: tail) =
      List.replicate (min ((letter :: tail).count letter) 2) letter ++
        blocksTwo (remainder letter tail) := by
  unfold blocksTwo
  rw [order_cons, List.flatMap_cons]
  congr 1
  apply render_congr
  intro tested member
  have kept : tested ∈ tail ∧ tested ≠ letter := by
    simpa [remainder] using (mem_firstOccurrenceSequence_iff tested _).mp member
  rw [List.count_cons_of_ne (Ne.symm kept.2), remainder_count_ne letter tested tail kept.2]

theorem blocksTwo_eq {left right : List Nat}
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right)
    (counts : ∀ letter, min (left.count letter) 2 = min (right.count letter) 2) :
    blocksTwo left = blocksTwo right := by
  unfold blocksTwo
  rw [order]
  exact render_congr _ _ _ (fun letter _ => counts letter)

structure Signature (left right : List Nat) : Prop where
  order : firstOccurrenceSequence left = firstOccurrenceSequence right
  counts : ∀ letter, min (left.count letter) 2 = min (right.count letter) 2
  length : min left.length 3 = min right.length 3

def normalList (letters : List Nat) : List Nat :=
  match firstOccurrenceSequence letters with
  | [letter] => List.replicate (min letters.length 3) letter
  | _ => blocksTwo letters

theorem normalList_eq {left right : List Nat} (same : Signature left right) :
    normalList left = normalList right := by
  have blocks := blocksTwo_eq same.order same.counts
  simp only [normalList, same.order, same.length, blocks]

theorem normalList_unary (letter : Nat) (tail : List Nat)
    (empty : remainder letter tail = []) :
    normalList (letter :: tail) = List.replicate (min (letter :: tail).length 3) letter := by
  unfold normalList
  rw [order_cons, empty]
  rfl

theorem normalList_mixed (letter : Nat) (tail : List Nat)
    (nonempty : remainder letter tail ≠ []) :
    normalList (letter :: tail) = blocksTwo (letter :: tail) := by
  simp only [normalList, order_cons]
  cases shape : firstOccurrenceSequence (remainder letter tail) with
  | nil => exact False.elim (nonempty ((order_eq_nil_iff _).mp shape))
  | cons head rest => rfl

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly
