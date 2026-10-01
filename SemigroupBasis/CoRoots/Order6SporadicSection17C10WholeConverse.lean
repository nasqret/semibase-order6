import SemigroupBasis.CoRoots.Order6SporadicSection17C10FormReplay
import SemigroupBasis.Opposite

/-! Unrestricted whole-form comparison for Proposition17.5. A common
processed prefix remains in every semantic comparison. Empty blocks,
empty initial prefixes, terminal blocks, and later recurring last labels
are all handled by the context and probe lemmas. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis Semantics

theorem whole_form_derives (which : Bool) :
    ∀ (leftSlots rightSlots : Slots) (leftInitial rightInitial : List Nat)
      (previous : Option Nat) (stem : List Nat),
      WellFormed ⟨leftInitial,leftSlots⟩ → WellFormed ⟨rightInitial,rightSlots⟩ →
      Saturated ⟨leftInitial,leftSlots⟩ → Saturated ⟨rightInitial,rightSlots⟩ →
      PrefixContext previous stem ⟨leftInitial,leftSlots⟩ → PrefixContext previous stem ⟨rightInitial,rightSlots⟩ →
      separators ⟨leftInitial,leftSlots⟩ = separators ⟨rightInitial,rightSlots⟩ →
      SameEval which (stem ++ renderForm ⟨leftInitial,leftSlots⟩) (stem ++ renderForm ⟨rightInitial,rightSlots⟩) →
      ListDerives (stem ++ renderForm ⟨leftInitial,leftSlots⟩) (stem ++ renderForm ⟨rightInitial,rightSlots⟩) := by
  intro leftSlots
  induction leftSlots with
  | nil =>
      intro rightSlots leftInitial rightInitial previous stem leftGood rightGood
        leftSaturated rightSaturated leftContext rightContext separatorsEqual same
      cases rightSlots with
      | nil =>
          have initial := context_initial_replay which previous stem _ _ leftGood rightGood
            leftSaturated rightSaturated leftContext rightContext separatorsEqual same
          simpa [renderForm] using initial.prepend stem
      | cons slot rest => simp [separators] at separatorsEqual
  | cons leftSlot leftRest ih =>
      intro rightSlots leftInitial rightInitial previous stem leftGood rightGood
        leftSaturated rightSaturated leftContext rightContext separatorsEqual same
      cases rightSlots with
      | nil => simp [separators] at separatorsEqual
      | cons rightSlot rightRest =>
          rcases leftSlot with ⟨separator,leftBody⟩
          rcases rightSlot with ⟨otherSeparator,rightBody⟩
          have equal : separator = otherSeparator := (List.cons.inj separatorsEqual).1
          subst otherSeparator
          have tailSeparators : separators ⟨leftBody,leftRest⟩ = separators ⟨rightBody,rightRest⟩ :=
            (List.cons.inj separatorsEqual).2
          have leftFree : ∀ x ∈ separators ⟨leftInitial,(separator,leftBody) :: leftRest⟩, x ∉ rightInitial := by
            intro x member
            have rightMember : x ∈ separators ⟨rightInitial,(separator,rightBody) :: rightRest⟩ :=
              separatorsEqual ▸ member
            exact initial_noSeparator _ rightGood x rightMember
          have rightFree : ∀ x ∈ separators ⟨rightInitial,(separator,rightBody) :: rightRest⟩, x ∉ rightInitial :=
            fun x member => initial_noSeparator _ rightGood x member
          have nextLeftContext := leftContext.advance leftGood rightInitial leftFree
          have nextRightContext := rightContext.advance rightGood rightInitial rightFree
          have initial := context_initial_replay which previous stem _ _ leftGood rightGood
            leftSaturated rightSaturated leftContext rightContext separatorsEqual same
          have first : ListDerives (stem ++ renderForm ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
              ((stem ++ squareList rightInitial ++ [separator]) ++ renderForm ⟨leftBody,leftRest⟩) := by
            simpa [renderForm,renderSlots,List.append_assoc] using initial.prepend stem
          have nextSame : SameEval which
              ((stem ++ squareList rightInitial ++ [separator]) ++ renderForm ⟨leftBody,leftRest⟩)
              ((stem ++ squareList rightInitial ++ [separator]) ++ renderForm ⟨rightBody,rightRest⟩) := by
            have preserved := (derives_sameEval which first).symm.trans same
            simpa [renderForm,renderSlots,List.append_assoc] using preserved
          have tails := ih rightRest leftBody rightBody (some separator)
            (stem ++ squareList rightInitial ++ [separator])
            (tail_wellFormed _ _ _ _ leftGood) (tail_wellFormed _ _ _ _ rightGood)
            leftSaturated.2 rightSaturated.2 nextLeftContext nextRightContext tailSeparators nextSame
          have second : ListDerives
              ((stem ++ squareList rightInitial ++ [separator]) ++ renderForm ⟨leftBody,leftRest⟩)
              (stem ++ renderForm ⟨rightInitial,(separator,rightBody) :: rightRest⟩) := by
            simpa [renderForm,renderSlots,List.append_assoc] using tails
          exact first.trans second

theorem normalForm_separators (letters : List Nat) :
    separators (normalForm letters) = letters.filter (simpleMask letters) := by
  rw [normalForm,saturateForm_separators,decompose_separators]

theorem normalForms_derives (which : Bool) (left right : List Nat) (same : SameEval which left right) :
    ListDerives (renderForm (normalForm left)) (renderForm (normalForm right)) := by
  have leftNormalization := derives_sameEval which (derives_normalForm left)
  have rightNormalization := derives_sameEval which (derives_normalForm right)
  have joint := leftNormalization.symm.trans (same.trans rightNormalization)
  have separatorsEqual : separators (normalForm left) = separators (normalForm right) := by
    simpa [normalForm_separators] using same.simpleSubsequence
  simpa using whole_form_derives which (normalForm left).slots (normalForm right).slots
    (normalForm left).initial (normalForm right).initial none []
    (normalForm_wellFormed left) (normalForm_wellFormed right)
    (normalForm_saturated left) (normalForm_saturated right)
    (PrefixContext.initial _) (PrefixContext.initial _) separatorsEqual joint

theorem sameEval_derives (which : Bool) (left right : List Nat) (same : SameEval which left right) :
    ListDerives left right :=
  (derives_normalForm left).trans ((normalForms_derives which left right same).trans (derives_normalForm right).symm)

theorem complete (which : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (Semantics.table which).semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases identity with ⟨⟨leftHead,leftTail⟩,⟨rightHead,rightTail⟩⟩
  exact S5_107.ListDerives.toWord
    (sameEval_derives which _ _ (sameEval_valid which _ valid))

theorem paper_basis (which : Bool) : BasisFor (Semantics.table which).semigroup basis :=
  ⟨models which,complete which⟩

namespace S6_7987
theorem representative_paper_basis : BasisFor table.semigroup basis := paper_basis false
theorem opposite_paper_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_paper_basis.oppositeReversed
end S6_7987

namespace S6_7991
theorem representative_paper_basis : BasisFor table.semigroup basis := paper_basis true
theorem opposite_paper_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_paper_basis.oppositeReversed
end S6_7991

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.whole_form_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.normalForms_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.sameEval_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.complete
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.representative_paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7987.opposite_paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7991.representative_paper_basis
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.S6_7991.opposite_paper_basis

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
