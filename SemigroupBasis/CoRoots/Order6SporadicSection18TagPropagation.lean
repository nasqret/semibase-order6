import SemigroupBasis.CoRoots.Order6SporadicSection18TaggedCanonical

/-! Actual C7 semantics spreads a fresh square from one occurrence to all
occurrences of the same block. A nonempty square block has value0,4or5;
the fresh square either leaves that value unchanged or annihilates it. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

theorem squareList_shift (block : List Nat) :
    squareList (block.map Nat.succ) = (squareList block).map Nat.succ := by
  induction block with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, squareList_cons, List.map_append, ih, List.map_nil]

def singleTaggedWord (marked : List Nat) (before : List Slot) (slot : Slot) (after : List Slot) : List Nat :=
  (render before).map Nat.succ ++ slot.gap.map Nat.succ ++
    squareList (tagBlock marked slot.block) ++ (render after).map Nat.succ

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
open Canonical

def SquareColor (value : Fin 6) : Prop := value = 0 ∨ value = 4 ∨ value = 5

private theorem assoc_eval (a b c : Fin 6) :
    tableMul (tableMul a b) c = tableMul a (tableMul b c) := table.assoc a b c

private theorem square_color (value : Fin 6) : SquareColor (tableMul value value) := by
  have checked : ∀ value : Fin 6, SquareColor (tableMul value value) := by unfold SquareColor; decide
  exact checked value

private theorem square_step_color (acc value : Fin 6) (color : SquareColor acc) :
    SquareColor (tableMul (tableMul acc value) value) := by
  have checked : ∀ a v : Fin 6, SquareColor a → SquareColor (tableMul (tableMul a v) v) := by
    unfold SquareColor
    decide
  exact checked acc value color

private theorem run_square_color (valuation : Nat → Fin 6) (block : List Nat) (acc : Fin 6)
    (color : SquareColor acc) : SquareColor (run valuation acc (squareList block)) := by
  induction block generalizing acc with
  | nil => exact color
  | cons head tail ih =>
      rw [squareList_cons, run_append]
      exact ih _ (square_step_color acc (valuation head) color)

def squareValue (valuation : Nat → Fin 6) : List Nat → Fin 6
  | [] => 0
  | head :: tail => run valuation (tableMul (valuation head) (valuation head)) (squareList tail)

theorem squareValue_color (valuation : Nat → Fin 6) (block : List Nat) :
    SquareColor (squareValue valuation block) := by
  cases block with
  | nil => exact Or.inl rfl
  | cons head tail => exact run_square_color valuation tail _ (square_color (valuation head))

theorem run_square_value (valuation : Nat → Fin 6) (block : List Nat)
    (nonempty : block ≠ []) (acc : Fin 6) :
    run valuation acc (squareList block) = tableMul acc (squareValue valuation block) := by
  cases block with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      simp only [squareList_cons, run_append, run_cons, run_nil, squareValue]
      rw [assoc_eval acc (valuation head) (valuation head)]
      exact run_mul valuation (squareList tail) acc (tableMul (valuation head) (valuation head))

private theorem shift_nonempty {block : List Nat} (nonempty : block ≠ []) : block.map Nat.succ ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [List.length_map, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

theorem run_tagged_marked_square (valuation : Nat → Fin 6) (marked : List Nat)
    (nonempty : marked ≠ []) (acc : Fin 6) :
    run valuation acc (squareList (tagBlock marked marked)) =
      tableMul acc (tableMul (tableMul (valuation 0) (valuation 0))
        (squareValue valuation (marked.map Nat.succ))) := by
  rw [tagBlock, if_pos rfl, squareList_cons, run_append]
  simp only [run_cons, run_nil]
  rw [run_square_value valuation (marked.map Nat.succ) (shift_nonempty nonempty)]
  rw [assoc_eval acc (valuation 0) (valuation 0),
    assoc_eval acc (tableMul (valuation 0) (valuation 0))]

theorem run_tagged_square_stable (valuation : Nat → Fin 6) (marked : List Nat)
    (nonempty : marked ≠ [])
    (stable : tableMul (tableMul (valuation 0) (valuation 0)) (squareValue valuation (marked.map Nat.succ)) =
      squareValue valuation (marked.map Nat.succ)) (block : List Nat) (acc : Fin 6) :
    run valuation acc (squareList (tagBlock marked block)) =
      run valuation acc (squareList (block.map Nat.succ)) := by
  by_cases equal : block = marked
  · subst block
    rw [run_tagged_marked_square valuation marked nonempty acc, stable,
      run_square_value valuation (marked.map Nat.succ) (shift_nonempty nonempty)]
  · simp only [tagBlock, if_neg equal]

private theorem run_tagged_square_zero (valuation : Nat → Fin 6) (marked : List Nat)
    (nonempty : marked ≠ [])
    (killed : tableMul (tableMul (valuation 0) (valuation 0)) (squareValue valuation (marked.map Nat.succ)) = 0)
    (acc : Fin 6) : run valuation acc (squareList (tagBlock marked marked)) = 0 := by
  rw [run_tagged_marked_square valuation marked nonempty acc, killed]
  exact (zero_absorbing acc).2

theorem run_tag_chain_stable (valuation : Nat → Fin 6) (marked : List Nat)
    (nonempty : marked ≠ [])
    (stable : tableMul (tableMul (valuation 0) (valuation 0)) (squareValue valuation (marked.map Nat.succ)) =
      squareValue valuation (marked.map Nat.succ)) (chain : List Slot) (acc : Fin 6) :
    run valuation acc (render (chain.map (tagSlot marked))) =
      run valuation acc ((render chain).map Nat.succ) := by
  induction chain generalizing acc with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, render, tagSlot, List.map_append, run_append, ← squareList_shift]
      rw [run_tagged_square_stable valuation marked nonempty stable]
      exact ih _

/-- This holds for any chain with the selected nonempty block at the given
position. It uses actual finite-table algebra, not an assumed identity transfer. -/
theorem tag_all_sameEval_single (marked : List Nat) (nonempty : marked ≠ [])
    (before : List Slot) (slot : Slot) (after : List Slot) (selected : slot.block = marked) :
    SameEval (render ((before ++ slot :: after).map (tagSlot marked)))
      (singleTaggedWord marked before slot after) := by
  intro valuation acc
  have cut : ∀ z e : Fin 6, SquareColor e → tableMul (tableMul z z) e = 0 ∨ tableMul (tableMul z z) e = e := by
    unfold SquareColor
    decide
  rcases cut (valuation 0) (squareValue valuation (marked.map Nat.succ))
    (squareValue_color valuation (marked.map Nat.succ)) with killed | stable
  · have kill : ∀ a, run valuation a (squareList (tagBlock marked slot.block)) = 0 := by
      intro a
      rw [selected]
      exact run_tagged_square_zero valuation marked nonempty killed a
    simp only [List.map_append, List.map_cons, render_append, render, tagSlot,
      singleTaggedWord, run_append, kill, run_zero]
  · rw [run_tag_chain_stable valuation marked nonempty stable]
    simp only [render_append, render, List.map_append, singleTaggedWord, run_append, ← squareList_shift]
    rw [run_tagged_square_stable valuation marked nonempty stable]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.squareList_shift
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.squareValue_color
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_square_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_tagged_marked_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_tagged_square_stable
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_tag_chain_stable
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.tag_all_sameEval_single

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
