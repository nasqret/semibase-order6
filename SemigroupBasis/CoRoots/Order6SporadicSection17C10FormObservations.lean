import SemigroupBasis.CoRoots.Order6SporadicSection17C10FormSyntax

/-! Contents and empty-body observations in retained whole-word contexts.
Only actual-table probes are used; a common prefix is never cancelled. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis Semantics

theorem PrefixContext.previous_noSquare {p : Nat} {stem : List Nat} {form : SquareForm}
    (context : PrefixContext (some p) stem form) : p ∉ squareList form.initial := by
  obtain ⟨before,shape,noBefore,noForm⟩ := context.previousBoundary
  intro member
  exact noForm (List.mem_append.mpr (Or.inl member))

theorem PrefixContext.previous_noTail {p : Nat} {stem initial : List Nat}
    {separator : Nat} {body : List Nat} {rest : Slots}
    (context : PrefixContext (some p) stem ⟨initial,(separator,body) :: rest⟩) :
    p ∉ renderForm ⟨body,rest⟩ := by
  obtain ⟨before,shape,noBefore,noForm⟩ := context.previousBoundary
  intro member
  have later : p ∈ renderSlots ((separator,body) :: rest) := List.mem_cons_of_mem separator member
  exact noForm (List.mem_append.mpr (Or.inr later))

theorem context_support (which : Bool) (previous : Option Nat) (stem : List Nat)
    (left right : SquareForm) (leftContext : PrefixContext previous stem left)
    (rightContext : PrefixContext previous stem right)
    (same : SameEval which (stem ++ renderForm left) (stem ++ renderForm right)) :
    ∀ x, x ∈ renderForm left ↔ x ∈ renderForm right := by
  cases previous with
  | none =>
      have empty : stem = [] := leftContext.previousBoundary
      intro x
      simpa [empty] using same.mem x
  | some p =>
      obtain ⟨before,shape,noBefore,noLeft⟩ := leftContext.previousBoundary
      obtain ⟨otherBefore,otherShape,noOther,noRight⟩ := rightContext.previousBoundary
      have splitSame : SameEval which (before ++ p :: renderForm left) (before ++ p :: renderForm right) := by
        simpa [shape,List.append_assoc] using same
      exact sameEval_afterMem which p before (renderForm left) before (renderForm right)
        splitSame noBefore noLeft noBefore noRight

theorem empty_bodies_at_terminal (which : Bool) (previous : Option Nat) (stem left right : List Nat)
    (leftContext : PrefixContext previous stem ⟨left,[]⟩)
    (rightContext : PrefixContext previous stem ⟨right,[]⟩)
    (same : SameEval which (stem ++ renderForm ⟨left,[]⟩) (stem ++ renderForm ⟨right,[]⟩)) :
    left = [] ↔ right = [] := by
  have observed : (stem ++ squareList left).getLast? = (stem ++ squareList right).getLast? := by
    simpa [renderForm,renderSlots] using same.last
  cases previous with
  | none =>
      have empty : stem = [] := leftContext.previousBoundary
      have lastEqual : (squareList left).getLast? = (squareList right).getLast? := by
        simpa [empty] using observed
      rw [← squareList_empty left,← squareList_empty right,
        ← List.getLast?_eq_none_iff (xs := squareList left),
        ← List.getLast?_eq_none_iff (xs := squareList right),lastEqual]
  | some p =>
      obtain ⟨before,shape,noBefore,noLeft⟩ := leftContext.previousBoundary
      have leftTest : (stem ++ squareList left).getLast? = some p ↔ left = [] := by
        rw [shape]
        exact (last_boundary before p (squareList left) leftContext.previous_noSquare).trans (squareList_empty left)
      have rightTest : (stem ++ squareList right).getLast? = some p ↔ right = [] := by
        rw [shape]
        exact (last_boundary before p (squareList right) rightContext.previous_noSquare).trans (squareList_empty right)
      rw [← leftTest,← rightTest,observed]

theorem empty_bodies_at_next (which : Bool) (previous : Option Nat) (stem leftInitial rightInitial : List Nat)
    (separator : Nat) (leftBody rightBody : List Nat) (leftRest rightRest : Slots)
    (leftGood : WellFormed ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
    (rightGood : WellFormed ⟨rightInitial,(separator,rightBody) :: rightRest⟩)
    (leftContext : PrefixContext previous stem ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
    (rightContext : PrefixContext previous stem ⟨rightInitial,(separator,rightBody) :: rightRest⟩)
    (same : SameEval which (stem ++ renderForm ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
      (stem ++ renderForm ⟨rightInitial,(separator,rightBody) :: rightRest⟩)) :
    leftInitial = [] ↔ rightInitial = [] := by
  have splitSame : SameEval which
      ((stem ++ squareList leftInitial) ++ separator :: renderForm ⟨leftBody,leftRest⟩)
      ((stem ++ squareList rightInitial) ++ separator :: renderForm ⟨rightBody,rightRest⟩) := by
    simpa [renderForm,renderSlots,List.append_assoc] using same
  have beforeL := leftContext.beforeAbsent leftGood
  have beforeR := rightContext.beforeAbsent rightGood
  have afterL := first_separator_noTail _ _ _ _ leftGood
  have afterR := first_separator_noTail _ _ _ _ rightGood
  cases previous with
  | none =>
      have empty : stem = [] := leftContext.previousBoundary
      have observed := sameEval_beforeEmpty which separator
        (stem ++ squareList leftInitial) (renderForm ⟨leftBody,leftRest⟩)
        (stem ++ squareList rightInitial) (renderForm ⟨rightBody,rightRest⟩)
        splitSame beforeL afterL beforeR afterR
      simpa [empty,squareList_empty] using observed
  | some p =>
      obtain ⟨before,shape,noBefore,noLeft⟩ := leftContext.previousBoundary
      have observed := sameEval_previous which separator p
        (stem ++ squareList leftInitial) (renderForm ⟨leftBody,leftRest⟩)
        (stem ++ squareList rightInitial) (renderForm ⟨rightBody,rightRest⟩)
        splitSame beforeL afterL beforeR afterR leftContext.previous_noTail rightContext.previous_noTail
      have leftTest : (stem ++ squareList leftInitial).getLast? = some p ↔ leftInitial = [] := by
        rw [shape]
        exact (last_boundary before p (squareList leftInitial) leftContext.previous_noSquare).trans
          (squareList_empty leftInitial)
      have rightTest : (stem ++ squareList rightInitial).getLast? = some p ↔ rightInitial = [] := by
        rw [shape]
        exact (last_boundary before p (squareList rightInitial) rightContext.previous_noSquare).trans
          (squareList_empty rightInitial)
      exact leftTest.symm.trans (observed.trans rightTest)

theorem context_initial_empty (which : Bool) (previous : Option Nat) (stem : List Nat) (left right : SquareForm)
    (leftGood : WellFormed left) (rightGood : WellFormed right)
    (leftContext : PrefixContext previous stem left) (rightContext : PrefixContext previous stem right)
    (separatorsEqual : separators left = separators right)
    (same : SameEval which (stem ++ renderForm left) (stem ++ renderForm right)) :
    left.initial = [] ↔ right.initial = [] := by
  rcases left with ⟨leftInitial,leftSlots⟩
  rcases right with ⟨rightInitial,rightSlots⟩
  cases leftSlots with
  | nil =>
      cases rightSlots with
      | nil => exact empty_bodies_at_terminal which previous stem leftInitial rightInitial leftContext rightContext same
      | cons slot rest => simp [separators] at separatorsEqual
  | cons slot rest =>
      cases rightSlots with
      | nil => simp [separators] at separatorsEqual
      | cons otherSlot otherRest =>
          rcases slot with ⟨separator,body⟩
          rcases otherSlot with ⟨otherSeparator,otherBody⟩
          have equal : separator = otherSeparator := (List.cons.inj separatorsEqual).1
          subst otherSeparator
          exact empty_bodies_at_next which previous stem leftInitial rightInitial separator body otherBody rest otherRest
            leftGood rightGood leftContext rightContext same

theorem context_initial_content (which : Bool) (previous : Option Nat) (stem : List Nat) (left right : SquareForm)
    (leftGood : WellFormed left) (rightGood : WellFormed right)
    (leftSaturated : Saturated left) (rightSaturated : Saturated right)
    (leftContext : PrefixContext previous stem left) (rightContext : PrefixContext previous stem right)
    (separatorsEqual : separators left = separators right)
    (same : SameEval which (stem ++ renderForm left) (stem ++ renderForm right))
    (leftNonempty : left.initial ≠ []) (rightNonempty : right.initial ≠ []) :
    ∀ x, x ∈ left.initial ↔ x ∈ right.initial := by
  have content := context_support which previous stem left right leftContext rightContext same
  intro x
  rw [saturated_initial_mem left leftGood leftSaturated leftNonempty,
    saturated_initial_mem right rightGood rightSaturated rightNonempty]
  exact and_congr (content x) (by rw [separatorsEqual])

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.context_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.empty_bodies_at_terminal
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.empty_bodies_at_next
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.context_initial_empty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.context_initial_content

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
