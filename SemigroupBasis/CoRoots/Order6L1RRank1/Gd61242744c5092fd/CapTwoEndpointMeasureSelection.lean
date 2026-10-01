import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointEvents

/-!
# Lexicographic endpoint measure and six-case selection

This module is the constructive positive-measure-to-dispatcher boundary.  It
contains no finite coverage premise: the first positive coordinate supplies
E/F, F/F, or E/E data for arbitrary contexts.

Static off-tree source; not locally elaborated.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis.Examples

structure EndpointMeasure where
  separation : Nat
  firstOrder : Nat
  eventOrder : Nat
deriving DecidableEq, Repr

def endpointMeasure (letters : List Nat) : EndpointMeasure where
  separation := endpointSeparation letters
  firstOrder :=
    ascendingInversions (firstProjection (tagEndpoints letters))
  eventOrder := eventGapInversions (tagEndpoints letters)

/-- Explicit positivity for the lexicographic three-coordinate measure. -/
def EndpointMeasure.Positive (measure : EndpointMeasure) : Prop :=
  0 < measure.separation ∨
    (measure.separation = 0 ∧ 0 < measure.firstOrder) ∨
    (measure.separation = 0 ∧ measure.firstOrder = 0 ∧
      0 < measure.eventOrder)

/-- Explicit strict lexicographic order. -/
def EndpointMeasure.Lt
    (smaller larger : EndpointMeasure) : Prop :=
  smaller.separation < larger.separation ∨
    (smaller.separation = larger.separation ∧
      smaller.firstOrder < larger.firstOrder) ∨
    (smaller.separation = larger.separation ∧
      smaller.firstOrder = larger.firstOrder ∧
      smaller.eventOrder < larger.eventOrder)

/-- Constructive accessibility proof: strong induction on separation, inside
that on first-order inversions, and inside that on event-gap inversions. -/
private theorem endpointMeasure_lt_acc :
    ∀ separation firstOrder eventOrder : Nat,
      Acc EndpointMeasure.Lt
        ⟨separation, firstOrder, eventOrder⟩ := by
  intro separation
  induction separation using Nat.strongRecOn with
  | ind separation separationInduction =>
      intro firstOrder
      induction firstOrder using Nat.strongRecOn with
      | ind firstOrder firstInduction =>
          intro eventOrder
          induction eventOrder using Nat.strongRecOn with
          | ind eventOrder eventInduction =>
              apply Acc.intro
              intro smaller smallerLt
              rcases smaller with ⟨smallerSeparation,
                smallerFirst, smallerEvent⟩
              change
                smallerSeparation < separation ∨
                  (smallerSeparation = separation ∧
                    smallerFirst < firstOrder) ∨
                  (smallerSeparation = separation ∧
                    smallerFirst = firstOrder ∧
                    smallerEvent < eventOrder) at smallerLt
              rcases smallerLt with separationDrop |
                  ⟨separationSame, firstDrop⟩ |
                  ⟨separationSame, firstSame, eventDrop⟩
              · exact separationInduction smallerSeparation
                  separationDrop smallerFirst smallerEvent
              · subst smallerSeparation
                exact firstInduction smallerFirst firstDrop smallerEvent
              · subst smallerSeparation
                subst smallerFirst
                exact eventInduction smallerEvent eventDrop

theorem endpointMeasure_lt_wellFounded :
    WellFounded EndpointMeasure.Lt :=
  ⟨fun measure => by
    rcases measure with ⟨separation, firstOrder, eventOrder⟩
    exact endpointMeasure_lt_acc separation firstOrder eventOrder⟩

theorem endpointMeasure_positive_iff_ne_zero
    (letters : List Nat) :
    (endpointMeasure letters).Positive ↔
      endpointMeasure letters ≠ ⟨0, 0, 0⟩ := by
  constructor
  · intro positive equal
    rw [equal] at positive
    simp [EndpointMeasure.Positive] at positive
  · intro nonzero
    by_cases separationPositive :
        0 < (endpointMeasure letters).separation
    · exact Or.inl separationPositive
    · have separationZero :
          (endpointMeasure letters).separation = 0 :=
        Nat.eq_zero_of_not_pos separationPositive
      by_cases firstPositive :
          0 < (endpointMeasure letters).firstOrder
      · exact Or.inr (Or.inl ⟨separationZero, firstPositive⟩)
      · have firstZero :
            (endpointMeasure letters).firstOrder = 0 :=
          Nat.eq_zero_of_not_pos firstPositive
        have eventPositive :
            0 < (endpointMeasure letters).eventOrder := by
          by_cases positive : 0 < (endpointMeasure letters).eventOrder
          · exact positive
          · have eventZero :
                (endpointMeasure letters).eventOrder = 0 :=
              Nat.eq_zero_of_not_pos positive
            have zeroMeasure : endpointMeasure letters = ⟨0, 0, 0⟩ := by
              cases measureEq : endpointMeasure letters with
              | mk separation firstOrder eventOrder =>
                  have separationEq : separation = 0 := by
                    simpa [measureEq] using separationZero
                  have firstEq : firstOrder = 0 := by
                    simpa [measureEq] using firstZero
                  have eventEq : eventOrder = 0 := by
                    simpa [measureEq] using eventZero
                  subst separation
                  subst firstOrder
                  subst eventOrder
                  rfl
            exact False.elim (nonzero zeroMeasure)
        exact Or.inr
          (Or.inr ⟨separationZero, firstZero, eventPositive⟩)

/-- The first positive lexicographic coordinate constructively selects one
of the six literal frozen-path dispatcher cases. -/
theorem endpointDisorderCase_of_positiveMeasure
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters)
    (positive : (endpointMeasure letters).Positive) :
    EndpointDisorderCase letters := by
  rcases positive with separationPositive |
      ⟨separationZero, firstPositive⟩ |
      ⟨separationZero, firstZero, eventPositive⟩
  · exact
      (endpointEFCase_of_positiveSeparation twoLimited connected
        separationPositive).toDisorderCase
  · exact
      (endpointFFCase_of_positiveFirstInversion separationZero
        firstPositive).toDisorderCase
  · exact
      (endpointEECase_of_positiveEventInversion separationZero
        eventPositive).toDisorderCase

/-- Positive measure always produces an explicit nonempty contextual frozen
route.  Strict decrease of its recomputed target measure is deliberately the
next module's obligation. -/
theorem endpointDisorder_route_of_positiveMeasure
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters)
    (positive : (endpointMeasure letters).Positive) :
    EndpointRouteResult letters :=
  endpointDisorder_dispatch
    (endpointDisorderCase_of_positiveMeasure
      twoLimited connected positive)

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
