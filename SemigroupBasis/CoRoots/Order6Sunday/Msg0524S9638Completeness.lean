import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Derivations
import SemigroupBasis.Opposite

/-! Complete four-law S9638 basis. Unique heads retain the ordered tail;
repeated heads are first moved to position two, then buffered normalization
uses the whole first-occurrence sequence. Short words are handled literally. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Completeness

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey (snoc depth)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey (UniqueInitial)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638SemanticKey
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Derivations

theorem firstOrder_cons_absent (head : Nat) (tail : List Nat) (absent : head ∉ tail) :
    firstOccurrenceSequence (head :: tail) = head :: firstOccurrenceSequence tail := by
  change head :: (firstOccurrenceSequence tail).filter (fun y => decide (y ≠ head)) =
    head :: firstOccurrenceSequence tail
  apply congrArg (List.cons head)
  apply List.filter_eq_self.mpr
  intro x present
  have inside : x ∈ tail := by simpa only [mem_firstOccurrenceSequence_iff] using present
  have different : x ≠ head := by
    intro same
    subst x
    exact absent inside
  simp [different]

theorem firstOrder_cons_repeat (head : Nat) (tail : List Nat) :
    firstOccurrenceSequence (head :: head :: tail) = firstOccurrenceSequence (head :: tail) := by
  simp [firstOccurrenceSequence, List.filter_filter]

theorem derivesExposeHead (head second : Nat) (tail : List Nat)
    (nonempty : tail ≠ []) (repeated : head ∈ second :: tail) :
    ∃ body : List Nat, body ≠ [] ∧
      Derives basis (Word.mk head (second :: tail)) (Word.mk head (head :: body)) := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp repeated
  cases before with
  | nil =>
      have same : second = head := (List.cons.inj split).1
      subst second
      exact ⟨tail, nonempty, Derives.refl _⟩
  | cons a rest =>
      refine ⟨(a :: rest) ++ after, by simp, ?_⟩
      rw [split]
      have base := derivesHeadReturn (Word.singleton head) (Word.mk a rest)
      cases after with
      | nil => simpa only [List.append_nil, Word.append_assoc] using base
      | cons b suffix =>
          have extended := Derives.appendRight base (Word.mk b suffix)
          change Derives basis (Word.mk head (((a :: rest) ++ [head]) ++ b :: suffix))
            (Word.mk head ((head :: a :: rest) ++ b :: suffix)) at extended
          simpa only [List.append_assoc, List.cons_append, List.singleton_append] using extended

theorem derivesSameTailOrder (head a b : Nat) (left right : List Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (order : firstOccurrenceSequence (a :: left) = firstOccurrenceSequence (b :: right)) :
    Derives basis (Word.mk head (a :: left)) (Word.mk head (b :: right)) := by
  have same : a = b := first_of_firstOrder a b left right order
  subst b
  have first := derivesLongNormal head a left leftNonempty
  have second := derivesLongNormal head a right rightNonempty
  have equal : suffixNormal (Word.mk a left) = suffixNormal (Word.mk a right) := by
    apply Word.toList_injective
    rw [suffixNormal_toList, suffixNormal_toList]
    exact order
  rw [equal] at first
  exact first.trans second.symm

theorem long_complete (head other a b : Nat) (left right : List Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (valid : (Identity.mk (Word.mk head (a :: left))
      (Word.mk other (b :: right))).SatisfiedBy (table 0).semigroup) :
    Derives basis (Word.mk head (a :: left)) (Word.mk other (b :: right)) := by
  have order := firstOrder_of_valid _ _ valid
  have heads : head = other := first_of_firstOrder head other (a :: left) (b :: right) order
  subst other
  have initial : UniqueInitial (Word.mk head (a :: left)) head ↔
      UniqueInitial (Word.mk head (b :: right)) head :=
    initial_marker_of_valid 0 (by decide) _ valid head
  by_cases repeated : head ∈ a :: left
  · have rightRepeated : head ∈ b :: right := by
      by_cases present : head ∈ b :: right
      · exact present
      · exact False.elim (((initial.mpr ⟨rfl, present⟩).2) repeated)
    obtain ⟨ls, ln, first⟩ := derivesExposeHead head a left leftNonempty repeated
    obtain ⟨rs, rn, second⟩ := derivesExposeHead head b right rightNonempty rightRepeated
    have changedValid : (Identity.mk (Word.mk head (head :: ls))
        (Word.mk head (head :: rs))).SatisfiedBy (table 0).semigroup := by
      intro valuation
      exact (Derives.sound models first valuation).symm.trans
        ((valid valuation).trans (Derives.sound models second valuation))
    have tailOrder := firstOrder_of_valid _ _ changedValid
    change firstOccurrenceSequence (head :: head :: ls) =
      firstOccurrenceSequence (head :: head :: rs) at tailOrder
    rw [firstOrder_cons_repeat, firstOrder_cons_repeat] at tailOrder
    exact first.trans ((derivesSameTailOrder head head head ls rs ln rn tailOrder).trans second.symm)
  · have rightAbsent : head ∉ b :: right := (initial.mp ⟨rfl, repeated⟩).2
    change firstOccurrenceSequence (head :: a :: left) =
      firstOccurrenceSequence (head :: b :: right) at order
    rw [firstOrder_cons_absent head (a :: left) repeated,
      firstOrder_cons_absent head (b :: right) rightAbsent] at order
    exact derivesSameTailOrder head a b left right leftNonempty rightNonempty (List.cons.inj order).2

theorem derives_of_cut_key (left right : List Nat) (a b : Nat)
    (key : SameCutKey left a right b) :
    Derives basis (snoc left a) (snoc right b) := by
  have valid := valid_of_key left right a b key
  rcases key with ⟨degree, order, _initial⟩
  have support := support_of_firstOrder (left ++ [a]) (right ++ [b]) order
  cases left with
  | nil =>
      cases right with
      | nil =>
          have same : a = b := first_of_firstOrder a b [] [] order
          subst b
          exact Derives.refl _
      | cons c rest => cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have heads : c = d := first_of_firstOrder c d [a] [b] order
                  subst d
                  have finalSame : a = b := by
                    by_cases h : a = c
                    · subst a
                      have present := (support b).mpr (by simp)
                      have bc : b = c := by simpa using present
                      exact bc.symm
                    · have present := (support a).mp (by simp)
                      simpa [h] using present
                  subst b
                  exact Derives.refl _
              | cons e rest => simp [depth] at degree
      | cons d rest =>
          cases right with
          | nil => simp [depth] at degree
          | cons e tail =>
              cases tail with
              | nil => simp [depth] at degree
              | cons f tail =>
                  exact long_complete c e d f (rest ++ [a]) (tail ++ [b]) (by simp) (by simp) valid

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy (table 0).semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases (semantic_key_iff identity.lhs identity.rhs).mp valid with
    ⟨leftStem, a, rightStem, b, hl, hr, key⟩
  rw [hl, hr]
  exact derives_of_cut_key leftStem rightStem a b key

theorem representative_basis : BasisFor (table 0).semigroup basis := ⟨models, complete⟩

theorem opposite_basis : BasisFor (table 0).semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Completeness
