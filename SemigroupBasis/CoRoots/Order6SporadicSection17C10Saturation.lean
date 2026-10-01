import SemigroupBasis.CoRoots.Order6SporadicSection17C10Squares

/-! The descending-content construction in Lemma17.7. Every simple letter
gets a separator slot, including slots with empty bodies. Saturation copies
only labels from later square blocks; it never fills an empty body. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

def SquareIn (x : Nat) (letters : List Nat) : Prop :=
  ∃ before after, letters = before ++ [x,x] ++ after

theorem squareIn_squareList (x : Nat) (letters : List Nat) (member : x ∈ letters) :
    SquareIn x (squareList letters) := by
  obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp member
  exact ⟨squareList before,squareList after,by
    simp [shape,squareList_append,squareList_cons,List.append_assoc]⟩

theorem SquareIn.prepend {x : Nat} {letters : List Nat} (occurs : SquareIn x letters)
    (stem : List Nat) : SquareIn x (stem ++ letters) := by
  obtain ⟨before,after,shape⟩ := occurs
  exact ⟨stem ++ before,after,by simp [shape,List.append_assoc]⟩

theorem SquareIn.append {x : Nat} {letters : List Nat} (occurs : SquareIn x letters)
    (suffix : List Nat) : SquareIn x (letters ++ suffix) := by
  obtain ⟨before,after,shape⟩ := occurs
  exact ⟨before,after ++ suffix,by simp [shape,List.append_assoc]⟩

theorem insertSquareFromSuffix (body : List Nat) (x : Nat) (suffix : List Nat)
    (nonempty : body ≠ []) (occurs : SquareIn x suffix) :
    ListDerives (squareList body ++ suffix) (squareList (x :: body) ++ suffix) := by
  cases body with
  | nil => exact False.elim (nonempty rfl)
  | cons h t =>
      obtain ⟨gap,after,shape⟩ := occurs
      simpa [shape,squareList_cons,List.append_assoc] using
        (inflateBeforeSquare h x (squareList t ++ gap)).append after

theorem prependSquaresFromSuffix (body extras suffix : List Nat) (nonempty : body ≠ [])
    (occurs : ∀ x ∈ extras, SquareIn x suffix) :
    ListDerives (squareList body ++ suffix) (squareList (extras ++ body) ++ suffix) := by
  induction extras with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      have first := ih (fun y member => occurs y (List.mem_cons_of_mem x member))
      have nextNonempty : xs ++ body ≠ [] := by
        intro empty
        exact nonempty (List.append_eq_nil_iff.mp empty).2
      exact first.trans (insertSquareFromSuffix (xs ++ body) x suffix nextNonempty (occurs x (by simp)))

abbrev Slots := List (Nat × List Nat)

def renderSlots : Slots → List Nat
  | [] => []
  | (separator,body) :: rest => separator :: (squareList body ++ renderSlots rest)

def slotSupport : Slots → List Nat
  | [] => []
  | (_,body) :: rest => body ++ slotSupport rest

structure SquareForm where
  initial : List Nat
  slots : Slots

def renderForm (form : SquareForm) : List Nat := squareList form.initial ++ renderSlots form.slots

theorem squareIn_renderSlots (x : Nat) (slots : Slots) (member : x ∈ slotSupport slots) :
    SquareIn x (renderSlots slots) := by
  induction slots with
  | nil => simp [slotSupport] at member
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      rcases List.mem_append.mp member with here | later
      · exact ((squareIn_squareList x body here).append (renderSlots rest)).prepend [separator]
      · exact (ih later).prepend (separator :: squareList body)

def saturateBody (body extras : List Nat) : List Nat :=
  if body = [] then [] else extras ++ body

def saturateSlots : Slots → Slots
  | [] => []
  | (separator,body) :: rest =>
      let later := saturateSlots rest
      (separator,saturateBody body (slotSupport later)) :: later

def saturateForm (form : SquareForm) : SquareForm :=
  let slots := saturateSlots form.slots
  ⟨saturateBody form.initial (slotSupport slots),slots⟩

theorem saturateBody_derives (body : List Nat) (slots : Slots) :
    ListDerives (squareList body ++ renderSlots slots)
      (squareList (saturateBody body (slotSupport slots)) ++ renderSlots slots) := by
  by_cases empty : body = []
  · simp only [saturateBody,empty,if_pos rfl]
    exact S5_107.ListDerives.refl _
  · simpa [saturateBody,empty] using prependSquaresFromSuffix body (slotSupport slots)
      (renderSlots slots) empty (fun x member => squareIn_renderSlots x slots member)

theorem saturateSlots_derives (slots : Slots) :
    ListDerives (renderSlots slots) (renderSlots (saturateSlots slots)) := by
  induction slots with
  | nil => exact S5_107.ListDerives.refl _
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      have first := ih.prepend (separator :: squareList body)
      have second := (saturateBody_derives body (saturateSlots rest)).prepend [separator]
      exact first.trans second

theorem saturateForm_derives (form : SquareForm) :
    ListDerives (renderForm form) (renderForm (saturateForm form)) := by
  have first := (saturateSlots_derives form.slots).prepend (squareList form.initial)
  have second := saturateBody_derives form.initial (saturateSlots form.slots)
  exact first.trans second

theorem saturateBody_empty (body extras : List Nat) : saturateBody body extras = [] ↔ body = [] := by
  by_cases empty : body = []
  · simp [saturateBody,empty]
  · simp [saturateBody,empty]

theorem saturateSlots_support (slots : Slots) (x : Nat) :
    x ∈ slotSupport (saturateSlots slots) ↔ x ∈ slotSupport slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      by_cases empty : body = []
      · simp [saturateSlots,saturateBody,empty,slotSupport,ih]
      · simp [saturateSlots,saturateBody,empty,slotSupport,ih,or_assoc,or_comm,or_left_comm]

def SaturatedSlots : Slots → Prop
  | [] => True
  | (_,body) :: rest =>
      (body ≠ [] → ∀ x ∈ slotSupport rest, x ∈ body) ∧ SaturatedSlots rest

def Saturated (form : SquareForm) : Prop :=
  (form.initial ≠ [] → ∀ x ∈ slotSupport form.slots, x ∈ form.initial) ∧ SaturatedSlots form.slots

theorem saturateBody_covers (body extras : List Nat) (nonempty : saturateBody body extras ≠ []) :
    ∀ x ∈ extras, x ∈ saturateBody body extras := by
  by_cases empty : body = []
  · simp [saturateBody,empty] at nonempty
  · intro x member
    simp [saturateBody,empty,List.mem_append,member]

theorem saturateSlots_saturated (slots : Slots) : SaturatedSlots (saturateSlots slots) := by
  induction slots with
  | nil => trivial
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      exact ⟨saturateBody_covers body (slotSupport (saturateSlots rest)),ih⟩

theorem saturateForm_saturated (form : SquareForm) : Saturated (saturateForm form) :=
  ⟨saturateBody_covers form.initial (slotSupport (saturateSlots form.slots)),
    saturateSlots_saturated form.slots⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.insertSquareFromSuffix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.prependSquaresFromSuffix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.saturateForm_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.saturateSlots_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.saturateForm_saturated

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
