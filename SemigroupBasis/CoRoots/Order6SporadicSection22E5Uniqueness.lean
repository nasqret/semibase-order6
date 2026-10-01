import SemigroupBasis.CoRoots.Order6SporadicSection22E5FormObservations

/-! Rigidity up to derivability for saturated E5 forms. Equal observations
give equal protected block heads and contents. Removing a simple separator
restricts observations, rather than cancelling semigroup multiplication. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

theorem observed_derives : ∀ (leftSlots rightSlots : Slots) (leftInitial rightInitial : List Nat),
    WellFormed ⟨leftInitial,leftSlots⟩ → WellFormed ⟨rightInitial,rightSlots⟩ →
    Saturated ⟨leftInitial,leftSlots⟩ → Saturated ⟨rightInitial,rightSlots⟩ →
    FormObserved ⟨leftInitial,leftSlots⟩ ⟨rightInitial,rightSlots⟩ →
    ListDerives (renderForm ⟨leftInitial,leftSlots⟩) (renderForm ⟨rightInitial,rightSlots⟩) := by
  intro leftSlots
  induction leftSlots with
  | nil =>
      intro rightSlots leftInitial rightInitial leftGood rightGood leftSaturated rightSaturated observed
      have separatorsEqual := observed.separators_eq
      cases rightSlots with
      | nil =>
          simpa [renderForm,renderSlots] using
            observed_initial_derives _ _ leftGood rightGood leftSaturated rightSaturated observed
      | cons rightSlot rightRest => simp [separators] at separatorsEqual
  | cons leftSlot leftRest ih =>
      intro rightSlots leftInitial rightInitial leftGood rightGood leftSaturated rightSaturated observed
      have separatorsEqual := observed.separators_eq
      cases rightSlots with
      | nil => simp [separators] at separatorsEqual
      | cons rightSlot rightRest =>
          rcases leftSlot with ⟨separator,leftBody⟩
          rcases rightSlot with ⟨otherSeparator,rightBody⟩
          have sameSeparator : separator = otherSeparator := (List.cons.inj separatorsEqual).1
          subst otherSeparator
          have initial := observed_initial_derives _ _ leftGood rightGood leftSaturated rightSaturated observed
          have tails := observed_tail leftInitial rightInitial separator leftBody rightBody leftRest rightRest
            leftGood rightGood observed
          have tailDerives := ih rightRest leftBody rightBody
            (tail_wellFormed _ _ _ _ leftGood) (tail_wellFormed _ _ _ _ rightGood)
            leftSaturated.2 rightSaturated.2 tails
          have first : ListDerives (renderForm ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
              (squareList rightInitial ++ separator :: renderForm ⟨leftBody,leftRest⟩) := by
            simpa [renderForm,renderSlots,List.append_assoc] using
              initial.append (separator :: renderForm ⟨leftBody,leftRest⟩)
          have second : ListDerives (squareList rightInitial ++ separator :: renderForm ⟨leftBody,leftRest⟩)
              (renderForm ⟨rightInitial,(separator,rightBody) :: rightRest⟩) := by
            simpa [renderForm,renderSlots,List.append_assoc] using tailDerives.prepend (squareList rightInitial ++ [separator])
          exact first.trans second

theorem normalForms_derives (left right : List Nat) (same : SameEval left right) :
    ListDerives (renderForm (normalForm left)) (renderForm (normalForm right)) :=
  observed_derives (normalForm left).slots (normalForm right).slots (normalForm left).initial (normalForm right).initial
    (normalForm_wellFormed left) (normalForm_wellFormed right)
    (normalForm_saturated left) (normalForm_saturated right) (normalForm_observed left right same)

theorem sameEval_derives (left right : List Nat) (same : SameEval left right) : ListDerives left right :=
  (derives_normalForm left).trans ((normalForms_derives left right same).trans (derives_normalForm right).symm)

#print axioms observed_derives
#print axioms normalForms_derives
#print axioms sameEval_derives

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
