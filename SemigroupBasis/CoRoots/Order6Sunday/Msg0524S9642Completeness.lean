import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Derivations
import SemigroupBasis.Opposite

/-! Completeness of the exact seven-law S9642 basis. The proof handles all
short words literally; long words use supported interior unions, preserving
a unique head or replacing a repeated head by the final letter. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Completeness

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey (snoc depth)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Derivations

theorem tail_support_of_valid (head : Nat) (left right : List Nat) (last : Nat)
    (valid : (Identity.mk (cut head left last) (cut head right last)).SatisfiedBy (table 1).semigroup) :
    ∀ x, x ∈ left ++ [last] ↔ x ∈ right ++ [last] := by
  have support := support_of_valid (cut head left last) (cut head right last) valid
  have absent : (head ∉ left ++ [last]) ↔ (head ∉ right ++ [last]) := by
    simpa only [cut_head, cut_tail, true_and] using
      initial_marker_of_valid 1 (by decide) (Identity.mk (cut head left last) (cut head right last)) valid head
  intro x
  by_cases same : x = head
  · subst x
    constructor
    · intro present
      by_cases other : head ∈ right ++ [last]
      · exact other
      · exact False.elim ((absent.mpr other) present)
    · intro present
      by_cases other : head ∈ left ++ [last]
      · exact other
      · exact False.elim ((absent.mp other) present)
  · simpa [cut_toList, same] using support x

theorem long_complete (head other : Nat) (left right : List Nat) (last : Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (valid : (Identity.mk (cut head left last) (cut other right last)).SatisfiedBy (table 1).semigroup) :
    Derives basis (cut head left last) (cut other right last) := by
  by_cases same : head = other
  · subst other
    exact derivesSameHead head left right last leftNonempty rightNonempty
      (tail_support_of_valid head left right last valid)
  · have initial (marker : Nat) : UniqueInitial (cut head left last) marker ↔
        UniqueInitial (cut other right last) marker :=
      initial_marker_of_valid 1 (by decide) _ valid marker
    have leftRepeated : head ∈ left ++ [last] := by
      by_cases present : head ∈ left ++ [last]
      · exact present
      · have unique : UniqueInitial (cut head left last) head :=
          ⟨rfl, by simpa only [cut_tail] using present⟩
        have equal : other = head := by
          simpa only [cut_head] using ((initial head).mp unique).1
        exact False.elim (same equal.symm)
    have rightRepeated : other ∈ right ++ [last] := by
      by_cases present : other ∈ right ++ [last]
      · exact present
      · have unique : UniqueInitial (cut other right last) other :=
          ⟨rfl, by simpa only [cut_tail] using present⟩
        have equal : head = other := by
          simpa only [cut_head] using ((initial other).mpr unique).1
        exact False.elim (same equal)
    have first := derivesRepeatedHead head left last leftNonempty leftRepeated
    have second := derivesRepeatedHead other right last rightNonempty rightRepeated
    have changedValid :
        (Identity.mk (cut last (head :: last :: (left ++ [last])) last)
          (cut last (other :: last :: (right ++ [last])) last)).SatisfiedBy (table 1).semigroup := by
      intro valuation
      exact (Derives.sound models first valuation).symm.trans
        ((valid valuation).trans (Derives.sound models second valuation))
    have between := derivesSameHead last (head :: last :: (left ++ [last]))
      (other :: last :: (right ++ [last])) last (by simp) (by simp)
      (tail_support_of_valid last _ _ last changedValid)
    exact first.trans (between.trans second.symm)

theorem derives_of_cut_key (left right : List Nat) (a b : Nat)
    (key : SameCutKey left a right b) :
    Derives basis (snoc left a) (snoc right b) := by
  have valid := valid_of_key left right a b key
  rcases key with ⟨degree, finalSame, support, _initial⟩
  subst b
  cases left with
  | nil =>
      cases right with
      | nil => exact Derives.refl _
      | cons c rest => cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have same : c = d := by
                    by_cases h : c = a
                    · subst c
                      have present := (support d).mpr (by simp)
                      have da : d = a := by simpa using present
                      exact da.symm
                    · have present := (support c).mp (by simp)
                      simpa [h] using present
                  subst d
                  exact Derives.refl _
              | cons e rest => simp [depth] at degree
      | cons d rest =>
          cases right with
          | nil => simp [depth] at degree
          | cons e tail =>
              cases tail with
              | nil => simp [depth] at degree
              | cons f tail =>
                  have cutValid : (Identity.mk (cut c (d :: rest) a)
                      (cut e (f :: tail) a)).SatisfiedBy (table 1).semigroup := by
                    simpa only [cut_eq_snoc] using valid
                  simpa only [cut_eq_snoc] using
                    long_complete c e (d :: rest) (f :: tail) a (by simp) (by simp) cutValid

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy (table 1).semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases (semantic_key_iff identity.lhs identity.rhs).mp valid with
    ⟨leftStem, a, rightStem, b, hl, hr, key⟩
  rw [hl, hr]
  exact derives_of_cut_key leftStem rightStem a b key

theorem representative_basis : BasisFor (table 1).semigroup basis := ⟨models, complete⟩

theorem opposite_basis : BasisFor (table 1).semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Completeness
