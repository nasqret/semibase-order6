import SemigroupBasis.CoRoots.Order6SporadicSection18ActualEvaluation

/-! Actual C7 evaluation for the Lemma18.8 window separator. Paper labels
4,3,5,6 are Fin6 values3,2,4,5. Homogeneous window evaluations are nonzero;
a square block containing both colors4 and5 forces zero in every context.
Constructing the globally consistent marked window valuation remains separate. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual

private theorem mul44 : tableMul 4 4 = 4 := by decide
private theorem mul45 : tableMul 4 5 = 0 := by decide
private theorem mul54 : tableMul 5 4 = 0 := by decide
private theorem mul55 : tableMul 5 5 = 5 := by decide
private theorem mul53 : tableMul 5 3 = 3 := by decide
private theorem mul34 : tableMul 3 4 = 3 := by decide
private theorem mul32 : tableMul 3 2 = 1 := by decide
private theorem mul15 : tableMul 1 5 = 1 := by decide
private theorem mul42 : tableMul 4 2 = 2 := by decide
private theorem mul25 : tableMul 2 5 = 2 := by decide

theorem run_uniform (valuation : Nat → Fin 6) (acc value : Fin 6)
    (stable : tableMul acc value = acc) :
    ∀ letters : List Nat, (∀ x ∈ letters, valuation x = value) → run valuation acc letters = acc
  | [], _ => rfl
  | head :: tail, uniform => by
      rw [run_cons, uniform head (List.Mem.head tail), stable]
      exact run_uniform valuation acc value stable tail
        (fun x member => uniform x (List.Mem.tail head member))

private theorem tail_has_other (valuation : Nat → Fin 6) (head : Nat) (tail : List Nat)
    (first other : Fin 6) (different : first ≠ other) (headValue : valuation head = first)
    (present : ∃ x ∈ head :: tail, valuation x = other) : ∃ x ∈ tail, valuation x = other := by
  obtain ⟨x, member, value⟩ := present
  rcases List.mem_cons.mp member with equal | member
  · subst x
    exact False.elim (different (headValue.symm.trans value))
  · exact ⟨x, member, value⟩

theorem run_four_zero_of_five (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ x ∈ letters, valuation x = 4 ∨ valuation x = 5) →
      (∃ x ∈ letters, valuation x = 5) → run valuation 4 letters = 0
  | [], _, present => by
      obtain ⟨x, impossible, _⟩ := present
      cases impossible
  | head :: tail, colors, present => by
      rcases colors head (List.Mem.head tail) with four | five
      · rw [run_cons, four, mul44]
        exact run_four_zero_of_five valuation tail
          (fun x member => colors x (List.Mem.tail head member))
          (tail_has_other valuation head tail 4 5 (by decide) four present)
      · rw [run_cons, five, mul45, run_zero]

theorem run_five_zero_of_four (valuation : Nat → Fin 6) :
    ∀ letters : List Nat,
      (∀ x ∈ letters, valuation x = 4 ∨ valuation x = 5) →
      (∃ x ∈ letters, valuation x = 4) → run valuation 5 letters = 0
  | [], _, present => by
      obtain ⟨x, impossible, _⟩ := present
      cases impossible
  | head :: tail, colors, present => by
      rcases colors head (List.Mem.head tail) with four | five
      · rw [run_cons, four, mul54, run_zero]
      · rw [run_cons, five, mul55]
        exact run_five_zero_of_four valuation tail
          (fun x member => colors x (List.Mem.tail head member))
          (tail_has_other valuation head tail 5 4 (by decide) five present)

theorem mixed_colors_run_zero (valuation : Nat → Fin 6) (acc : Fin 6) (letters : List Nat)
    (colors : ∀ x ∈ letters, valuation x = 4 ∨ valuation x = 5)
    (four : ∃ x ∈ letters, valuation x = 4) (five : ∃ x ∈ letters, valuation x = 5) :
    run valuation acc letters = 0 := by
  cases letters with
  | nil =>
      obtain ⟨x, impossible, _⟩ := four
      cases impossible
  | cons head tail =>
      have tailColors := fun x member => colors x (List.Mem.tail head member)
      rcases colors head (List.Mem.head tail) with headFour | headFive
      · have tailZero := run_four_zero_of_five valuation tail tailColors
          (tail_has_other valuation head tail 4 5 (by decide) headFour five)
        rw [run_cons, headFour, run_mul, tailZero]
        exact (zero_absorbing acc).2
      · have tailZero := run_five_zero_of_four valuation tail tailColors
          (tail_has_other valuation head tail 5 4 (by decide) headFive four)
        rw [run_cons, headFive, run_mul, tailZero]
        exact (zero_absorbing acc).2

theorem mixed_square_context_zero (valuation : Nat → Fin 6) (acc : Fin 6)
    (before block after : List Nat)
    (colors : ∀ x ∈ block, valuation x = 4 ∨ valuation x = 5)
    (four : ∃ x ∈ block, valuation x = 4) (five : ∃ x ∈ block, valuation x = 5) :
    run valuation acc (before ++ squareList block ++ after) = 0 := by
  have squareColors : ∀ x ∈ squareList block, valuation x = 4 ∨ valuation x = 5 :=
    fun x member => colors x ((squareList_mem block x).mp member)
  have squareFour : ∃ x ∈ squareList block, valuation x = 4 := by
    obtain ⟨x, member, value⟩ := four
    exact ⟨x, (squareList_mem block x).mpr member, value⟩
  have squareFive : ∃ x ∈ squareList block, valuation x = 5 := by
    obtain ⟨x, member, value⟩ := five
    exact ⟨x, (squareList_mem block x).mpr member, value⟩
  rw [run_append, run_append,
    mixed_colors_run_zero valuation (run valuation acc before) (squareList block)
      squareColors squareFour squareFive, run_zero]

theorem window_middle_value (valuation : Nat → Fin 6) (before inside after : List Nat)
    (left right : Nat) (leftValue : valuation left = 3) (rightValue : valuation right = 2)
    (beforeFive : ∀ x ∈ before, valuation x = 5)
    (insideFour : ∀ x ∈ inside, valuation x = 4)
    (afterFive : ∀ x ∈ after, valuation x = 5) :
    run valuation 5 (before ++ (left :: (inside ++ (right :: after)))) = 1 := by
  rw [run_append, run_uniform valuation 5 5 mul55 before beforeFive,
    run_cons, leftValue, mul53, run_append,
    run_uniform valuation 3 4 mul34 inside insideFour,
    run_cons, rightValue, mul32, run_uniform valuation 1 5 mul15 after afterFive]

theorem window_initial_value (valuation : Nat → Fin 6) (inside after : List Nat)
    (right : Nat) (rightValue : valuation right = 2)
    (insideFour : ∀ x ∈ inside, valuation x = 4)
    (afterFive : ∀ x ∈ after, valuation x = 5) :
    run valuation 4 (inside ++ (right :: after)) = 2 := by
  rw [run_append, run_uniform valuation 4 4 mul44 inside insideFour,
    run_cons, rightValue, mul42, run_uniform valuation 2 5 mul25 after afterFive]

theorem window_final_value (valuation : Nat → Fin 6) (before inside : List Nat)
    (left : Nat) (leftValue : valuation left = 3)
    (beforeFive : ∀ x ∈ before, valuation x = 5)
    (insideFour : ∀ x ∈ inside, valuation x = 4) :
    run valuation 5 (before ++ (left :: inside)) = 3 := by
  rw [run_append, run_uniform valuation 5 5 mul55 before beforeFive,
    run_cons, leftValue, mul53, run_uniform valuation 3 4 mul34 inside insideFour]

/-- Once the marked window valuation is constructed and its source evaluation
is nonzero, actual C7 validity forbids both colors in one target square block. -/
theorem SameEval.excludes_mixed_square {left right : List Nat} (same : SameEval left right)
    (valuation : Nat → Fin 6) (acc : Fin 6) (nonzero : run valuation acc left ≠ 0)
    (before block after : List Nat) (shape : right = before ++ squareList block ++ after)
    (colors : ∀ x ∈ block, valuation x = 4 ∨ valuation x = 5)
    (four : ∃ x ∈ block, valuation x = 4) : ¬ ∃ x ∈ block, valuation x = 5 := by
  intro five
  have equal := same valuation acc
  rw [shape] at equal
  exact nonzero (equal.trans (mixed_square_context_zero valuation acc before block after colors four five))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_uniform
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_four_zero_of_five
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_five_zero_of_four
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.mixed_colors_run_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.mixed_square_context_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.window_middle_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.window_initial_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.window_final_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.SameEval.excludes_mixed_square

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
