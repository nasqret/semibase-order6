import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey

/-! Exact S9643 constructive calculus. Earlier-occurrence deletion replaces
S9642's invalid interior-swap rule; the prescribed seventh law changes a
repeated head only after sufficient supported duplication. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643Derivations

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey (snoc toList_snoc)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey (UniqueInitial)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey
open SemigroupBasis.CoRoots.S5_1089 (lastOccurrenceSequence)

def basis : List (Identity Nat) :=
  [⟨snoc [0, 0] 0, snoc [0, 0, 0] 0⟩,
   ⟨snoc [0, 0] 1, snoc [1, 0] 1⟩,
   ⟨snoc [0, 0] 1, snoc [0, 0, 0] 1⟩,
   ⟨snoc [0, 0] 1, snoc [0, 0, 1] 1⟩,
   ⟨snoc [0, 1] 1, snoc [0, 1, 1] 1⟩,
   ⟨snoc [0, 1] 2, snoc [0, 1, 1] 2⟩,
   ⟨snoc [0, 0, 1, 2] 3, snoc [3, 0, 1, 2] 3⟩]

theorem models : Models (table 2).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨rfl, rfl, by decide, ?_⟩
  all_goals intro marker
  all_goals simp [UniqueInitial, snoc, eq_comm]
  all_goals intros
  all_goals simp_all

private def substitute (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesXXY (x y : Word Nat) :
    Derives basis (x ++ (x ++ y)) (y ++ (x ++ y)) := by
  have base : Derives basis (snoc [0, 0] 1) (snoc [1, 0] 1) :=
    Derives.fromBasis (e := ⟨snoc [0, 0] 1, snoc [1, 0] 1⟩) (by simp [basis])
  simpa [snoc, substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y (Word.singleton 0))

theorem derivesXXYY (x y : Word Nat) :
    Derives basis (x ++ (x ++ y)) (x ++ (x ++ (y ++ y))) := by
  have base : Derives basis (snoc [0, 0] 1) (snoc [0, 0, 1] 1) :=
    Derives.fromBasis (e := ⟨snoc [0, 0] 1, snoc [0, 0, 1] 1⟩) (by simp [basis])
  simpa [snoc, substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y (Word.singleton 0))

theorem derivesMiddleDuplication (front block suffix : Word Nat) :
    Derives basis (front ++ (block ++ suffix)) (front ++ (block ++ (block ++ suffix))) := by
  have base : Derives basis (snoc [0, 1] 2) (snoc [0, 1, 1] 2) :=
    Derives.fromBasis (e := ⟨snoc [0, 1] 2, snoc [0, 1, 1] 2⟩) (by simp [basis])
  simpa [snoc, substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute front block suffix)

private def substituteFour (x y z t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem derivesHeadTransfer (x y z t : Word Nat) :
    Derives basis (x ++ (x ++ (y ++ (z ++ t)))) (t ++ (x ++ (y ++ (z ++ t)))) := by
  have base : Derives basis (snoc [0, 0, 1, 2] 3) (snoc [3, 0, 1, 2] 3) :=
    Derives.fromBasis (e := ⟨snoc [0, 0, 1, 2] 3, snoc [3, 0, 1, 2] 3⟩) (by simp [basis])
  simpa [snoc, substituteFour, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substituteFour x y z t)

theorem derivesReturnDeletion (front letter middle suffix : Word Nat) :
    Derives basis (front ++ (letter ++ (middle ++ (letter ++ suffix))))
      (front ++ (middle ++ (letter ++ suffix))) := by
  have first : Derives basis (front ++ (letter ++ (middle ++ (letter ++ suffix))))
      (front ++ (middle ++ (middle ++ (letter ++ suffix)))) := by
    simpa only [Word.append_assoc] using
      Derives.prepend front (Derives.appendRight (derivesXXY middle letter).symm suffix)
  exact first.trans (derivesMiddleDuplication front middle (letter ++ suffix)).symm

theorem derivesFinalDuplication (front middle last : Word Nat) :
    Derives basis (front ++ (middle ++ last)) (front ++ (middle ++ (last ++ last))) := by
  have first := derivesMiddleDuplication front middle last
  have second := Derives.prepend front (derivesXXYY middle last)
  have third := (derivesMiddleDuplication front middle (last ++ last)).symm
  exact first.trans (second.trans third)

theorem append_snoc_cons (front : Word Nat) (x : Nat) (middle : List Nat) (last : Nat) :
    front ++ snoc (x :: middle) last = (front ++ Word.singleton x) ++ snoc middle last := by
  rw [Word.append_assoc]
  exact congrArg (fun tail => front ++ tail) (by cases middle <;> rfl)

theorem derivesDeleteCurrent (front : Word Nat) (letter : Nat)
    (rest : List Nat) (last : Nat) (later : letter ∈ rest) :
    Derives basis (front ++ snoc (letter :: rest) last) (front ++ snoc rest last) := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp later
  cases before with
  | nil =>
      simpa only [split, List.nil_append, append_snoc_cons, Word.append_assoc] using
        (derivesMiddleDuplication front (Word.singleton letter) (snoc after last)).symm
  | cons a tail =>
      have first : front ++ snoc (letter :: rest) last =
          front ++ (Word.singleton letter ++ (Word.mk a tail ++
            (Word.singleton letter ++ snoc after last))) := by
        apply Word.toList_injective
        simp only [Word.toList_append, toList_snoc, Word.toList_singleton]
        simp only [split, Word.toList, List.cons_append, List.append_assoc, List.nil_append]
      have second : front ++ snoc rest last =
          front ++ (Word.mk a tail ++ (Word.singleton letter ++ snoc after last)) := by
        apply Word.toList_injective
        simp only [Word.toList_append, toList_snoc, Word.toList_singleton]
        simp only [split, Word.toList, List.cons_append, List.append_assoc, List.nil_append]
      rw [first, second]
      exact derivesReturnDeletion front (Word.singleton letter) (Word.mk a tail) (snoc after last)

theorem derivesNormalizeMiddle (front : Word Nat) (middle : List Nat) (last : Nat) :
    Derives basis (front ++ snoc middle last)
      (front ++ snoc (lastOccurrenceSequence middle) last) := by
  induction middle generalizing front with
  | nil => exact Derives.refl _
  | cons letter rest ih =>
      by_cases later : letter ∈ rest
      · have deleted := derivesDeleteCurrent front letter rest last later
        simpa only [lastOccurrenceSequence, if_pos later] using deleted.trans (ih front)
      · simpa only [lastOccurrenceSequence, if_neg later, append_snoc_cons] using
          ih (front ++ Word.singleton letter)

theorem derivesInsertMiddle (front : Word Nat) (middle : List Nat) (last marker : Nat)
    (present : marker ∈ middle) :
    Derives basis (front ++ snoc middle last) (front ++ snoc (marker :: middle) last) :=
  (derivesDeleteCurrent front marker middle last present).symm

def cut (head : Nat) (middle : List Nat) (last : Nat) : Word Nat :=
  Word.singleton head ++ snoc middle last

theorem cut_eq_snoc (head : Nat) (middle : List Nat) (last : Nat) :
    cut head middle last = snoc (head :: middle) last := by
  cases middle <;> rfl

theorem cut_head (head : Nat) (middle : List Nat) (last : Nat) :
    (cut head middle last).head = head := rfl

theorem cut_tail (head : Nat) (middle : List Nat) (last : Nat) :
    (cut head middle last).tail = middle ++ [last] := by
  cases middle <;> rfl

theorem cut_toList (head : Nat) (middle : List Nat) (last : Nat) :
    (cut head middle last).toList = head :: (middle ++ [last]) := by
  cases middle <;> rfl

theorem derivesSaturateFinal (head : Nat) (middle : List Nat) (last : Nat)
    (nonempty : middle ≠ []) :
    Derives basis (cut head middle last) (cut head (middle ++ [last]) last) := by
  cases middle with
  | nil => exact False.elim (nonempty rfl)
  | cons a rest =>
      simpa [cut, snoc, Word.append, Word.singleton, List.append_assoc] using
        derivesFinalDuplication (Word.singleton head) (Word.mk a rest) (Word.singleton last)

theorem derivesSameHead (head : Nat) (left right : List Nat) (last : Nat)
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (tailOrder : lastOccurrenceSequence (left ++ [last]) = lastOccurrenceSequence (right ++ [last])) :
    Derives basis (cut head left last) (cut head right last) := by
  have first := (derivesSaturateFinal head left last leftNonempty).trans
    (derivesNormalizeMiddle (Word.singleton head) (left ++ [last]) last)
  have second := (derivesSaturateFinal head right last rightNonempty).trans
    (derivesNormalizeMiddle (Word.singleton head) (right ++ [last]) last)
  rw [tailOrder] at first
  exact first.trans second.symm

theorem derivesRepeatedHead (head : Nat) (middle : List Nat) (last : Nat)
    (nonempty : middle ≠ []) (repeated : head ∈ middle ++ [last]) :
    Derives basis (cut head middle last)
      (cut last (head :: head :: head :: (middle ++ [last])) last) := by
  have first := derivesSaturateFinal head middle last nonempty
  have addOne := derivesInsertMiddle (Word.singleton head) (middle ++ [last]) last head repeated
  have addTwo := derivesInsertMiddle (Word.singleton head) (head :: (middle ++ [last])) last head (by simp)
  have addThree := derivesInsertMiddle (Word.singleton head) (head :: head :: (middle ++ [last])) last head (by simp)
  have changeHead : Derives basis (cut head (head :: head :: head :: (middle ++ [last])) last)
      (cut last (head :: head :: head :: (middle ++ [last])) last) := by
    have bridge : snoc (head :: middle) last ++ Word.singleton last =
        Word.singleton head ++ snoc (middle ++ [last]) last := by
      apply Word.toList_injective
      simp only [Word.toList_append, toList_snoc, Word.toList_singleton]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    have transferred := derivesHeadTransfer (Word.singleton head) (Word.singleton head)
      (snoc (head :: middle) last) (Word.singleton last)
    rw [bridge] at transferred
    simpa only [cut, append_snoc_cons, Word.append_assoc] using transferred
  exact first.trans (addOne.trans (addTwo.trans (addThree.trans changeHead)))

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643Derivations
