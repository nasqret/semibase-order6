import SemigroupBasis.CoRoots.Order6SporadicSection17C10FormObservations

/-! Read the last-letter alternative from the original full contexts, then
apply the already proved retained-suffix block calculus. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis Semantics

theorem lasts_at_next (which : Bool) (previous : Option Nat) (stem left right : List Nat) (x y separator : Nat)
    (leftBody rightBody : List Nat) (leftRest rightRest : Slots)
    (leftGood : WellFormed ⟨left ++ [x],(separator,leftBody) :: leftRest⟩)
    (rightGood : WellFormed ⟨right ++ [y],(separator,rightBody) :: rightRest⟩)
    (leftContext : PrefixContext previous stem ⟨left ++ [x],(separator,leftBody) :: leftRest⟩)
    (rightContext : PrefixContext previous stem ⟨right ++ [y],(separator,rightBody) :: rightRest⟩)
    (same : SameEval which (stem ++ renderForm ⟨left ++ [x],(separator,leftBody) :: leftRest⟩)
      (stem ++ renderForm ⟨right ++ [y],(separator,rightBody) :: rightRest⟩)) :
    x = y ∨ (x ∈ renderSlots ((separator,leftBody) :: leftRest) ∧
      y ∈ renderSlots ((separator,leftBody) :: leftRest)) := by
  by_cases equal : x = y
  · exact Or.inl equal
  have splitSame : SameEval which
      ((stem ++ squareList (left ++ [x])) ++ separator :: renderForm ⟨leftBody,leftRest⟩)
      ((stem ++ squareList (right ++ [y])) ++ separator :: renderForm ⟨rightBody,rightRest⟩) := by
    simpa [renderForm,renderSlots,List.append_assoc] using same
  have beforeL := leftContext.beforeAbsent leftGood
  have beforeR := rightContext.beforeAbsent rightGood
  have afterL := first_separator_noTail _ _ _ _ leftGood
  have afterR := first_separator_noTail _ _ _ _ rightGood
  have afterSupports := sameEval_afterMem which separator
    (stem ++ squareList (left ++ [x])) (renderForm ⟨leftBody,leftRest⟩)
    (stem ++ squareList (right ++ [y])) (renderForm ⟨rightBody,rightRest⟩)
    splitSame beforeL afterL beforeR afterR
  have leftLast : (stem ++ squareList (left ++ [x])).getLast? = some x := by
    simp [squareList_append,squareList_cons,squareList_nil]
  have rightLast : (stem ++ squareList (right ++ [y])).getLast? = some y := by
    simp [squareList_append,squareList_cons,squareList_nil]
  have xLater : x ∈ renderForm ⟨leftBody,leftRest⟩ := by
    by_cases found : x ∈ renderForm ⟨leftBody,leftRest⟩
    · exact found
    · have otherAbsent : x ∉ renderForm ⟨rightBody,rightRest⟩ :=
        fun member => found ((afterSupports x).mpr member)
      have observed := sameEval_previous which separator x
        (stem ++ squareList (left ++ [x])) (renderForm ⟨leftBody,leftRest⟩)
        (stem ++ squareList (right ++ [y])) (renderForm ⟨rightBody,rightRest⟩)
        splitSame beforeL afterL beforeR afterR found otherAbsent
      have backwards : y = x := Option.some.inj (rightLast.symm.trans (observed.mp leftLast))
      exact False.elim (equal backwards.symm)
  have yLaterRight : y ∈ renderForm ⟨rightBody,rightRest⟩ := by
    by_cases found : y ∈ renderForm ⟨rightBody,rightRest⟩
    · exact found
    · have otherAbsent : y ∉ renderForm ⟨leftBody,leftRest⟩ :=
        fun member => found ((afterSupports y).mp member)
      have observed := sameEval_previous which separator y
        (stem ++ squareList (left ++ [x])) (renderForm ⟨leftBody,leftRest⟩)
        (stem ++ squareList (right ++ [y])) (renderForm ⟨rightBody,rightRest⟩)
        splitSame beforeL afterL beforeR afterR otherAbsent found
      have forwards : x = y := Option.some.inj (leftLast.symm.trans (observed.mpr rightLast))
      exact False.elim (equal forwards)
  exact Or.inr ⟨List.mem_cons_of_mem separator xLater,
    List.mem_cons_of_mem separator ((afterSupports y).mpr yLaterRight)⟩

theorem context_initial_lasts (which : Bool) (previous : Option Nat) (stem left right : List Nat)
    (x y : Nat) (leftSlots rightSlots : Slots)
    (leftGood : WellFormed ⟨left ++ [x],leftSlots⟩)
    (rightGood : WellFormed ⟨right ++ [y],rightSlots⟩)
    (leftContext : PrefixContext previous stem ⟨left ++ [x],leftSlots⟩)
    (rightContext : PrefixContext previous stem ⟨right ++ [y],rightSlots⟩)
    (separatorsEqual : separators ⟨left ++ [x],leftSlots⟩ = separators ⟨right ++ [y],rightSlots⟩)
    (same : SameEval which (stem ++ renderForm ⟨left ++ [x],leftSlots⟩)
      (stem ++ renderForm ⟨right ++ [y],rightSlots⟩)) :
    x = y ∨ (x ∈ renderSlots leftSlots ∧ y ∈ renderSlots leftSlots) := by
  cases leftSlots with
  | nil =>
      cases rightSlots with
      | nil =>
          have observed : some x = some y := by
            simpa [renderForm,renderSlots,squareList_append,squareList_cons,squareList_nil] using same.last
          exact Or.inl (Option.some.inj observed)
      | cons slot rest => simp [separators] at separatorsEqual
  | cons slot rest =>
      cases rightSlots with
      | nil => simp [separators] at separatorsEqual
      | cons otherSlot otherRest =>
          rcases slot with ⟨separator,body⟩
          rcases otherSlot with ⟨otherSeparator,otherBody⟩
          have equal : separator = otherSeparator := (List.cons.inj separatorsEqual).1
          subst otherSeparator
          exact lasts_at_next which previous stem left right x y separator body otherBody rest otherRest
            leftGood rightGood leftContext rightContext same

theorem context_initial_replay (which : Bool) (previous : Option Nat) (stem : List Nat) (left right : SquareForm)
    (leftGood : WellFormed left) (rightGood : WellFormed right)
    (leftSaturated : Saturated left) (rightSaturated : Saturated right)
    (leftContext : PrefixContext previous stem left) (rightContext : PrefixContext previous stem right)
    (separatorsEqual : separators left = separators right)
    (same : SameEval which (stem ++ renderForm left) (stem ++ renderForm right)) :
    ListDerives (squareList left.initial ++ renderSlots left.slots)
      (squareList right.initial ++ renderSlots left.slots) := by
  rcases left with ⟨leftInitial,leftSlots⟩
  rcases right with ⟨rightInitial,rightSlots⟩
  have emptiness := context_initial_empty which previous stem _ _
    leftGood rightGood leftContext rightContext separatorsEqual same
  rcases nil_or_last leftInitial with rfl | ⟨left,x,rfl⟩
  · have emptyRight : rightInitial = [] := emptiness.mp rfl
    subst rightInitial
    exact S5_107.ListDerives.refl _
  · rcases nil_or_last rightInitial with rfl | ⟨right,y,rfl⟩
    · have impossible : left ++ [x] = [] := emptiness.mpr rfl
      simp at impossible
    · have content := context_initial_content which previous stem _ _
        leftGood rightGood leftSaturated rightSaturated leftContext rightContext separatorsEqual same
        (by simp) (by simp)
      have lasts := context_initial_lasts which previous stem left right x y leftSlots rightSlots
        leftGood rightGood leftContext rightContext separatorsEqual same
      simpa [squareList_append,squareList_cons,squareList_nil,List.append_assoc] using
        squareBlocks_replay_with_suffix x y left right (renderSlots leftSlots) content lasts

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.lasts_at_next
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.context_initial_lasts
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.context_initial_replay

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
