import SemigroupBasis.CoRoots.Order6SporadicSection22E5Derivations

/-! Doubling every nonsimple occurrence. The mask is fixed from the original
word, while the induction records the count invariant in the growing stem.
No cardinality bound on the alphabet or number of occurrences is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

def doubleSelected (simple : Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => if simple x then x :: doubleSelected simple xs
      else x :: x :: doubleSelected simple xs

theorem doubleSelected_append (simple : Nat → Bool) (xs ys : List Nat) :
    doubleSelected simple (xs ++ ys) = doubleSelected simple xs ++ doubleSelected simple ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases flag : simple x <;> simp [doubleSelected,flag,ih]

theorem doubleSelected_derives (simple : Nat → Bool) (stem suffix : List Nat)
    (nonsimple : ∀ x, simple x = false → (stem ++ suffix).count x ≠ 1) :
    ListDerives (stem ++ suffix) (stem ++ doubleSelected simple suffix) := by
  induction suffix generalizing stem with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      cases flag : simple x with
      | true =>
          have invariant : ∀ y, simple y = false → ((stem ++ [x]) ++ xs).count y ≠ 1 := by
            intro y mask
            simpa [List.append_assoc] using nonsimple y mask
          simpa [doubleSelected,flag,List.append_assoc] using ih (stem ++ [x]) invariant
      | false =>
          have notOne := nonsimple x flag
          have seen : x ∈ stem ∨ x ∈ xs := by
            by_cases prior : x ∈ stem
            · exact Or.inl prior
            · by_cases later : x ∈ xs
              · exact Or.inr later
              · have stemZero := List.count_eq_zero.mpr prior
                have tailZero := List.count_eq_zero.mpr later
                exact False.elim (notOne (by simp [List.count_append,stemZero,tailZero]))
          have invariant : ∀ y, simple y = false → ((stem ++ [x,x]) ++ xs).count y ≠ 1 := by
            intro y mask
            by_cases same : y = x
            · subst y
              simp only [List.count_append,List.count_cons_self,List.count_nil] 
              omega
            · simpa [List.count_append,List.count_cons_of_ne (Ne.symm same)] using nonsimple y mask
          have first := duplicateOccurrence stem x xs seen
          have second : ListDerives (stem ++ x :: x :: xs)
              (stem ++ x :: x :: doubleSelected simple xs) := by
            simpa [List.append_assoc] using ih (stem ++ [x,x]) invariant
          simpa [doubleSelected,flag] using first.trans second

def simpleMask (letters : List Nat) (x : Nat) : Bool := decide (letters.count x = 1)

theorem doubleNonsimple_derives (letters : List Nat) :
    ListDerives letters (doubleSelected (simpleMask letters) letters) := by
  have invariant : ∀ x, simpleMask letters x = false → ([] ++ letters).count x ≠ 1 := by
    intro x mask
    simpa [simpleMask] using mask
  simpa using doubleSelected_derives (simpleMask letters) [] letters invariant

theorem doubleSelected_mem (simple : Nat → Bool) (letters : List Nat) (x : Nat) :
    x ∈ doubleSelected simple letters ↔ x ∈ letters := by
  induction letters with
  | nil => simp [doubleSelected]
  | cons h t ih => cases flag : simple h <;> simp [doubleSelected,flag,ih]

#print axioms doubleSelected_derives
#print axioms doubleNonsimple_derives
#print axioms doubleSelected_mem

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
