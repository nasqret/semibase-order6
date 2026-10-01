import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey

/-! Constructive interior permutations, supported insertion and repeated-head
replacement for the exact prescribed seven-law S9642 basis. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Derivations

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey (snoc)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey

def basis : List (Identity Nat) :=
  [⟨snoc [0, 0] 0, snoc [0, 0, 0] 0⟩,
   ⟨snoc [0, 0] 1, snoc [1, 0] 1⟩,
   ⟨snoc [0, 0] 1, snoc [0, 0, 0] 1⟩,
   ⟨snoc [0, 0] 1, snoc [0, 0, 1] 1⟩,
   ⟨snoc [0, 1] 1, snoc [0, 1, 1] 1⟩,
   ⟨snoc [0, 1] 2, snoc [0, 1, 1] 2⟩,
   ⟨snoc [0, 0, 1] 2, snoc [0, 1, 0] 2⟩]

theorem models : Models (table 1).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨rfl, rfl, ?_, ?_⟩
  all_goals intro marker
  all_goals simp [UniqueInitial, snoc, eq_comm, or_comm, or_left_comm]
  intro notZero notOne
  exact ⟨fun zero => False.elim (notZero zero), fun one => False.elim (notOne one)⟩

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

theorem derivesXXYZ (x y suffix : Word Nat) :
    Derives basis (x ++ (x ++ (y ++ suffix))) (x ++ (y ++ (x ++ suffix))) := by
  have base : Derives basis (snoc [0, 0, 1] 2) (snoc [0, 1, 0] 2) :=
    Derives.fromBasis (e := ⟨snoc [0, 0, 1] 2, snoc [0, 1, 0] 2⟩) (by simp [basis])
  simpa [snoc, substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y suffix)

theorem derivesInteriorSwap (front x y suffix : Word Nat) :
    Derives basis (front ++ (x ++ (y ++ suffix))) (front ++ (y ++ (x ++ suffix))) := by
  have first := derivesMiddleDuplication front x (y ++ suffix)
  have second : Derives basis (front ++ (x ++ (x ++ (y ++ suffix))))
      (front ++ (y ++ (x ++ (y ++ suffix)))) := by
    simpa only [Word.append_assoc] using
      Derives.prepend front (Derives.appendRight (derivesXXY x y) suffix)
  have third := Derives.prepend front (derivesXXYZ y x suffix).symm
  have fourth := (derivesMiddleDuplication front y (x ++ suffix)).symm
  exact first.trans (second.trans (third.trans fourth))

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

theorem derivesMiddlePermutation {left right : List Nat} (permutation : left.Perm right)
    (front : Word Nat) (last : Nat) :
    Derives basis (front ++ snoc left last) (front ++ snoc right last) := by
  induction permutation generalizing front with
  | nil => exact Derives.refl _
  | cons x _ ih =>
      simpa only [append_snoc_cons] using ih (front ++ Word.singleton x)
  | swap x y rest =>
      simpa only [append_snoc_cons, Word.append_assoc] using
        derivesInteriorSwap front (Word.singleton y) (Word.singleton x) (snoc rest last)
  | trans _ _ first second => exact (first front).trans (second front)

theorem derivesInsertMiddle (front : Word Nat) (middle : List Nat) (last marker : Nat)
    (present : marker ∈ middle) :
    Derives basis (front ++ snoc middle last) (front ++ snoc (marker :: middle) last) := by
  have expose : middle.Perm (marker :: middle.erase marker) := List.perm_cons_erase present
  have first := derivesMiddlePermutation expose front last
  have second : Derives basis (front ++ snoc (marker :: middle.erase marker) last)
      (front ++ snoc (marker :: marker :: middle.erase marker) last) := by
    simpa only [append_snoc_cons, Word.append_assoc] using
      derivesMiddleDuplication front (Word.singleton marker) (snoc (middle.erase marker) last)
  have restore : (marker :: marker :: middle.erase marker).Perm (marker :: middle) :=
    (List.Perm.cons marker expose).symm
  exact first.trans (second.trans (derivesMiddlePermutation restore front last))

theorem derivesInsertMiddleList (front : Word Nat) (middle extra : List Nat) (last : Nat)
    (supported : ∀ x ∈ extra, x ∈ middle) :
    Derives basis (front ++ snoc middle last) (front ++ snoc (extra ++ middle) last) := by
  induction extra with
  | nil => exact Derives.refl _
  | cons x rest ih =>
      have first := ih (fun y hy => supported y (by simp [hy]))
      have present : x ∈ rest ++ middle :=
        List.mem_append.mpr (Or.inr (supported x (by simp)))
      exact first.trans (derivesInsertMiddle front (rest ++ middle) last x present)

theorem derivesMiddleSupport (front : Word Nat) (left right : List Nat) (last : Nat)
    (support : ∀ x, x ∈ left ↔ x ∈ right) :
    Derives basis (front ++ snoc left last) (front ++ snoc right last) := by
  have first := derivesInsertMiddleList front left right last (fun x hx => (support x).mpr hx)
  have second := derivesInsertMiddleList front right left last (fun x hx => (support x).mp hx)
  have between := derivesMiddlePermutation
    (List.perm_append_comm : (right ++ left).Perm (left ++ right)) front last
  exact first.trans (between.trans second.symm)

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
    (tailSupport : ∀ x, x ∈ left ++ [last] ↔ x ∈ right ++ [last]) :
    Derives basis (cut head left last) (cut head right last) := by
  have first := derivesSaturateFinal head left last leftNonempty
  have second := derivesSaturateFinal head right last rightNonempty
  have between := derivesMiddleSupport (Word.singleton head) (left ++ [last])
    (right ++ [last]) last tailSupport
  exact first.trans (between.trans second.symm)

theorem derivesRepeatedHead (head : Nat) (middle : List Nat) (last : Nat)
    (nonempty : middle ≠ []) (repeated : head ∈ middle ++ [last]) :
    Derives basis (cut head middle last) (cut last (head :: last :: (middle ++ [last])) last) := by
  have first := derivesSaturateFinal head middle last nonempty
  have supported : ∀ x ∈ [head, last], x ∈ middle ++ [last] := by
    intro x present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · subst x
      exact repeated
    · subst x
      simp
  have second := derivesInsertMiddleList (Word.singleton head) (middle ++ [last])
    [head, last] last supported
  have third : Derives basis (cut head (head :: last :: (middle ++ [last])) last)
      (cut last (head :: last :: (middle ++ [last])) last) := by
    simpa only [cut, append_snoc_cons, Word.append_assoc] using
      Derives.appendRight (derivesXXY (Word.singleton head) (Word.singleton last))
        (snoc (middle ++ [last]) last)
  exact first.trans (second.trans third)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642Derivations
