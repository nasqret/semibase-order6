import SemigroupBasis.CoRoots.Order6SporadicSection18OrientedWindows
import SemigroupBasis.CoRoots.Order6SporadicSection18SimpleRunPermutation

/-! Select simple boundary markers by position in the SAME canonical witness.
The three records retain the actual slot and word decompositions; no separate
region valuation or assumed boundary-gap existence is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

theorem CanonicalWitness.noninitial_gap_nonempty {whole alphabet : List Nat}
    {first : Slot} {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before : List Slot) (slot : Slot) (after : List Slot)
    (shape : first :: rest = before ++ slot :: after) (nonempty : before ≠ []) :
    slot.gap ≠ [] := by
  obtain ⟨_, _, _, _, _, later, _, _, _⟩ := witness
  cases before with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      have boundary : first :: rest = head :: (tail ++ slot :: after) := shape
      have restShape := (List.cons.inj boundary).2
      apply later slot
      rw [restShape]
      simp

theorem CanonicalWitness.gap_simple {whole alphabet : List Nat}
    {first : Slot} {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (slot : Slot) (member : slot ∈ first :: rest) (x : Nat) (present : x ∈ slot.gap) :
    whole.count x = 1 := by
  obtain ⟨_, _, _, _, _, _, simple, _, _⟩ := witness
  exact simple slot member x present

theorem simple_marker_clear (whole before after : List Nat) (x : Nat)
    (shape : whole = before ++ x :: after) (simple : whole.count x = 1) :
    x ∉ before ++ after := by
  rw [shape] at simple
  simp only [List.count_append, List.count_cons_self] at simple
  apply List.count_eq_zero.mp
  rw [List.count_append]
  omega

theorem simple_markers_clear (whole before inside after : List Nat) (x y : Nat)
    (shape : whole = before ++ x :: (inside ++ y :: after))
    (leftSimple : whole.count x = 1) (rightSimple : whole.count y = 1) :
    x ≠ y ∧ Actual.PairClear x y (before ++ inside ++ after) := by
  have different : x ≠ y := by
    intro equal
    subst y
    rw [shape] at leftSimple
    simp only [List.count_append, List.count_cons_self] at leftSimple
    omega
  have leftClear := simple_marker_clear whole before (inside ++ y :: after) x shape leftSimple
  have rightShape : whole = (before ++ x :: inside) ++ y :: after := by
    simpa only [List.append_assoc, List.cons_append] using shape
  have rightClear := simple_marker_clear whole (before ++ x :: inside) after y rightShape rightSimple
  refine ⟨different, ?_, ?_⟩
  · intro member
    apply leftClear
    simpa only [List.mem_append, List.mem_cons] using
      (show x ∈ before ∨ x ∈ inside ∨ x = y ∨ x ∈ after from by
        rcases List.mem_append.mp member with member | member
        · rcases List.mem_append.mp member with member | member
          · exact Or.inl member
          · exact Or.inr (Or.inl member)
        · exact Or.inr (Or.inr (Or.inr member)))
  · intro member
    apply rightClear
    simp only [List.mem_append, List.mem_cons] at member ⊢
    rcases member with (member | member) | member
    · exact Or.inl (Or.inl member)
    · exact Or.inl (Or.inr (Or.inr member))
    · exact Or.inr member

structure MiddleBoundary (whole : List Nat) (before window after : List Slot) where
  head : Slot
  tail : List Slot
  next : Slot
  remaining : List Slot
  left : Nat
  right : Nat
  leftTail : List Nat
  rightHead : List Nat
  beforeNonempty : before ≠ []
  windowShape : window = head :: tail
  afterShape : after = next :: remaining
  leftGap : head.gap = left :: leftTail
  rightGap : next.gap = rightHead ++ [right]
  leftSimple : whole.count left = 1
  rightSimple : whole.count right = 1
  different : left ≠ right
  wordShape : whole = render before ++ left ::
    ((leftTail ++ squareList head.block ++ render tail ++ rightHead) ++
      right :: (squareList next.block ++ render remaining))
  clear : Actual.PairClear left right
    (render before ++ (leftTail ++ squareList head.block ++ render tail ++ rightHead) ++
      (squareList next.block ++ render remaining))

structure InitialBoundary (whole : List Nat) (before window after : List Slot) where
  head : Slot
  tail : List Slot
  next : Slot
  remaining : List Slot
  right : Nat
  rightHead : List Nat
  beforeEmpty : before = []
  windowShape : window = head :: tail
  afterShape : after = next :: remaining
  firstGap : head.gap = []
  rightGap : next.gap = rightHead ++ [right]
  rightSimple : whole.count right = 1
  wordShape : whole = (squareList head.block ++ render tail ++ rightHead) ++
    right :: (squareList next.block ++ render remaining)
  clear : right ∉ (squareList head.block ++ render tail ++ rightHead) ++
    (squareList next.block ++ render remaining)

structure FinalBoundary (whole : List Nat) (before window after : List Slot) where
  head : Slot
  tail : List Slot
  left : Nat
  leftTail : List Nat
  beforeNonempty : before ≠ []
  windowShape : window = head :: tail
  afterEmpty : after = []
  leftGap : head.gap = left :: leftTail
  leftSimple : whole.count left = 1
  wordShape : whole = render before ++ left :: (leftTail ++ squareList head.block ++ render tail)
  clear : left ∉ render before ++ (leftTail ++ squareList head.block ++ render tail)

theorem CanonicalWitness.middle_boundary {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before : List Slot) (head : Slot) (tail : List Slot) (next : Slot) (remaining : List Slot)
    (shape : first :: rest = before ++ (head :: tail) ++ (next :: remaining))
    (beforeNonempty : before ≠ []) :
    Nonempty (MiddleBoundary whole before (head :: tail) (next :: remaining)) := by
  have leftNonempty := witness.noninitial_gap_nonempty before head
    (tail ++ next :: remaining) (by simpa only [List.append_assoc, List.cons_append] using shape)
    beforeNonempty
  have rightNonempty := witness.noninitial_gap_nonempty (before ++ head :: tail) next remaining
    shape (by simp)
  obtain ⟨left, leftTail, leftGap⟩ := List.exists_cons_of_ne_nil leftNonempty
  have reverseNonempty : next.gap.reverse ≠ [] := by simpa using rightNonempty
  obtain ⟨right, reversed, reverseShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  have rightGap : next.gap = reversed.reverse ++ [right] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse reverseShape
  have leftSimple : whole.count left = 1 := witness.gap_simple head
    (by rw [shape]; simp) left (by rw [leftGap]; simp)
  have rightSimple : whole.count right = 1 := witness.gap_simple next
    (by rw [shape]; simp) right (by rw [rightGap]; simp)
  have rendered := witness.2.2.2.2.2.2.2.2
  have wordShape : whole = render before ++ left ::
      ((leftTail ++ squareList head.block ++ render tail ++ reversed.reverse) ++
        right :: (squareList next.block ++ render remaining)) := by
    rw [shape, render_append, render_append] at rendered
    simpa only [render, leftGap, rightGap, List.append_assoc, List.cons_append,
      List.nil_append] using rendered.symm
  have properties := simple_markers_clear whole (render before)
    (leftTail ++ squareList head.block ++ render tail ++ reversed.reverse)
    (squareList next.block ++ render remaining) left right wordShape leftSimple rightSimple
  exact ⟨⟨head, tail, next, remaining, left, right, leftTail, reversed.reverse, beforeNonempty,
    rfl, rfl, leftGap, rightGap, leftSimple, rightSimple, properties.1, wordShape, properties.2⟩⟩

theorem CanonicalWitness.initial_boundary {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (head : Slot) (tail : List Slot) (next : Slot) (remaining : List Slot)
    (shape : first :: rest = (head :: tail) ++ (next :: remaining)) :
    Nonempty (InitialBoundary whole [] (head :: tail) (next :: remaining)) := by
  have headEqual : first = head := (List.cons.inj shape).1
  have firstGap : head.gap = [] := by
    rw [← headEqual]
    exact witness.2.2.2.2.1
  have rightNonempty := witness.noninitial_gap_nonempty (head :: tail) next remaining shape (by simp)
  have reverseNonempty : next.gap.reverse ≠ [] := by simpa using rightNonempty
  obtain ⟨right, reversed, reverseShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  have rightGap : next.gap = reversed.reverse ++ [right] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse reverseShape
  have rightSimple : whole.count right = 1 := witness.gap_simple next
    (by rw [shape]; simp) right (by rw [rightGap]; simp)
  have rendered := witness.2.2.2.2.2.2.2.2
  have wordShape : whole = (squareList head.block ++ render tail ++ reversed.reverse) ++
      right :: (squareList next.block ++ render remaining) := by
    rw [shape, render_append] at rendered
    simpa only [render, firstGap, rightGap, List.append_assoc, List.cons_append,
      List.nil_append] using rendered.symm
  have clear := simple_marker_clear whole (squareList head.block ++ render tail ++ reversed.reverse)
    (squareList next.block ++ render remaining) right wordShape rightSimple
  exact ⟨⟨head, tail, next, remaining, right, reversed.reverse, rfl, rfl, rfl,
    firstGap, rightGap, rightSimple, wordShape, clear⟩⟩

theorem CanonicalWitness.final_boundary {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before : List Slot) (head : Slot) (tail : List Slot)
    (shape : first :: rest = before ++ (head :: tail)) (beforeNonempty : before ≠ []) :
    Nonempty (FinalBoundary whole before (head :: tail) []) := by
  have leftNonempty := witness.noninitial_gap_nonempty before head tail shape beforeNonempty
  obtain ⟨left, leftTail, leftGap⟩ := List.exists_cons_of_ne_nil leftNonempty
  have leftSimple : whole.count left = 1 := witness.gap_simple head
    (by rw [shape]; simp) left (by rw [leftGap]; simp)
  have rendered := witness.2.2.2.2.2.2.2.2
  have wordShape : whole = render before ++ left :: (leftTail ++ squareList head.block ++ render tail) := by
    rw [shape, render_append] at rendered
    simpa only [render, leftGap, List.append_assoc, List.cons_append] using rendered.symm
  have clear := simple_marker_clear whole (render before)
    (leftTail ++ squareList head.block ++ render tail) left wordShape leftSimple
  exact ⟨⟨head, tail, left, leftTail, beforeNonempty, rfl, rfl, leftGap,
    leftSimple, wordShape, clear⟩⟩

/-- An oriented window has at least one actual boundary, hence exactly one of
the three marker shapes applies. All records use the original canonical word. -/
theorem CanonicalWitness.boundary_markers {whole alphabet : List Nat} {first : Slot}
    {rest : List Slot} (witness : CanonicalWitness whole alphabet first rest)
    (before window after : List Slot) (shape : first :: rest = before ++ window ++ after)
    (windowNonempty : window ≠ []) (outside : before ≠ [] ∨ after ≠ []) :
    Nonempty (MiddleBoundary whole before window after) ∨
      Nonempty (InitialBoundary whole before window after) ∨
      Nonempty (FinalBoundary whole before window after) := by
  obtain ⟨head, tail, windowShape⟩ := List.exists_cons_of_ne_nil windowNonempty
  subst window
  cases after with
  | nil =>
      have beforeNonempty : before ≠ [] := by simpa using outside
      exact Or.inr (Or.inr (witness.final_boundary before head tail
        (by simpa only [List.append_nil] using shape) beforeNonempty))
  | cons next remaining =>
      by_cases beforeEmpty : before = []
      · subst before
        exact Or.inr (Or.inl (witness.initial_boundary head tail next remaining
          (by simpa only [List.nil_append] using shape)))
      · exact Or.inl (witness.middle_boundary before head tail next remaining shape beforeEmpty)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.noninitial_gap_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.gap_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.simple_marker_clear
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.simple_markers_clear
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.middle_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.initial_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.final_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.CanonicalWitness.boundary_markers

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
