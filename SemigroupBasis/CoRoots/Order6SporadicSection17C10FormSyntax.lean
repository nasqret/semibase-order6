import SemigroupBasis.CoRoots.Order6SporadicSection17C10SimpleOrder
import SemigroupBasis.CoRoots.Order6SporadicSection17C10LastSimpleDetectors
import SemigroupBasis.CoRoots.Order6SporadicSection17C10BlockReplay

/-! Representation boundaries for whole-form comparison. The processed
stem is retained explicitly; no semigroup cancellation is available. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
open SemigroupBasis

theorem squareList_mem (letters : List Nat) (x : Nat) : x ∈ squareList letters ↔ x ∈ letters := by
  induction letters with
  | nil => simp [squareList_nil]
  | cons h t ih => simp [squareList_cons,ih]

theorem squareList_empty (letters : List Nat) : squareList letters = [] ↔ letters = [] := by
  cases letters <;> simp [squareList_nil,squareList_cons]

theorem renderSlots_mem (slots : Slots) (x : Nat) :
    x ∈ renderSlots slots ↔ x ∈ slots.map Prod.fst ∨ x ∈ slotSupport slots := by
  induction slots with
  | nil => simp [renderSlots,slotSupport]
  | cons slot rest ih =>
      rcases slot with ⟨separator,body⟩
      simp [renderSlots,slotSupport,squareList_mem,ih,or_assoc,or_left_comm,or_comm]

theorem renderForm_mem (form : SquareForm) (x : Nat) :
    x ∈ renderForm form ↔ x ∈ bodySupport form ∨ x ∈ separators form := by
  simp [renderForm,bodySupport,separators,renderSlots_mem,squareList_mem,or_assoc,or_left_comm,or_comm]

theorem squareInitial_noSeparator (form : SquareForm) (good : WellFormed form) (separator : Nat)
    (member : separator ∈ separators form) : separator ∉ squareList form.initial := by
  intro occurs
  exact good.2 separator (List.mem_append.mpr (Or.inl ((squareList_mem _ _).mp occurs))) member

theorem initial_noSeparator (form : SquareForm) (good : WellFormed form) (separator : Nat)
    (member : separator ∈ separators form) : separator ∉ form.initial := by
  intro occurs
  exact good.2 separator (List.mem_append.mpr (Or.inl occurs)) member

theorem tail_wellFormed (initial : List Nat) (separator : Nat) (body : List Nat) (rest : Slots)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) : WellFormed ⟨body,rest⟩ := by
  constructor
  · exact (List.nodup_cons.mp good.1).2
  · intro x member simpleMember
    exact good.2 x (List.mem_append.mpr (Or.inr member)) (List.mem_cons_of_mem separator simpleMember)

theorem first_separator_noTail (initial : List Nat) (separator : Nat) (body : List Nat) (rest : Slots)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) :
    separator ∉ renderForm ⟨body,rest⟩ := by
  intro member
  rcases (renderForm_mem ⟨body,rest⟩ separator).mp member with bodyMember | simpleMember
  · exact good.2 separator (List.mem_append.mpr (Or.inr bodyMember)) (by simp [separators])
  · exact (List.nodup_cons.mp good.1).1 simpleMember

theorem saturated_initial_mem (form : SquareForm) (good : WellFormed form) (saturated : Saturated form)
    (nonempty : form.initial ≠ []) (x : Nat) :
    x ∈ form.initial ↔ x ∈ renderForm form ∧ x ∉ separators form := by
  constructor
  · intro member
    have bodyMember : x ∈ bodySupport form := List.mem_append.mpr (Or.inl member)
    exact ⟨(renderForm_mem form x).mpr (Or.inl bodyMember),good.2 x bodyMember⟩
  · rintro ⟨member,notSimple⟩
    rcases (renderForm_mem form x).mp member with bodyMember | simpleMember
    · rcases List.mem_append.mp bodyMember with initialMember | laterMember
      · exact initialMember
      · exact saturated.1 nonempty x laterMember
    · exact False.elim (notSimple simpleMember)

theorem last_append_of_nonempty (before after : List Nat) (nonempty : after ≠ []) :
    (before ++ after).getLast? = after.getLast? := by
  rw [List.getLast?_append]
  cases last : after.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp last))
  | some x => rfl

theorem last_boundary (before : List Nat) (separator : Nat) (after : List Nat)
    (absent : separator ∉ after) :
    (before ++ [separator] ++ after).getLast? = some separator ↔ after = [] := by
  by_cases empty : after = []
  · simp [empty]
  · rw [last_append_of_nonempty _ after empty]
    simp [empty,Semantics.last_ne_of_absent separator after absent]

theorem squareList_last (letters : List Nat) : (squareList letters).getLast? = letters.getLast? := by
  rcases Semantics.nil_or_last letters with rfl | ⟨before,last,rfl⟩
  · rfl
  · simp [squareList_append,squareList_cons,squareList_nil]

structure PrefixContext (previous : Option Nat) (stem : List Nat) (form : SquareForm) : Prop where
  futureAbsent : ∀ separator ∈ separators form, separator ∉ stem
  previousBoundary : match previous with
    | none => stem = []
    | some p => ∃ before, stem = before ++ [p] ∧ p ∉ before ∧ p ∉ renderForm form

theorem PrefixContext.initial (form : SquareForm) : PrefixContext none [] form :=
  ⟨fun _ _ => by simp,rfl⟩

theorem PrefixContext.beforeAbsent {previous : Option Nat} {stem initial : List Nat}
    {separator : Nat} {body : List Nat} {rest : Slots}
    (context : PrefixContext previous stem ⟨initial,(separator,body) :: rest⟩)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) :
    separator ∉ stem ++ squareList initial := by
  intro member
  rcases List.mem_append.mp member with earlier | current
  · exact context.futureAbsent separator (by simp [separators]) earlier
  · exact squareInitial_noSeparator _ good separator (by simp [separators]) current

/-- The inserted body is only required to avoid future simple labels.
This permits replaying the right body while retaining the left suffix. -/
theorem PrefixContext.advance {previous : Option Nat} {stem initial : List Nat}
    {separator : Nat} {body : List Nat} {rest : Slots}
    (context : PrefixContext previous stem ⟨initial,(separator,body) :: rest⟩)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩)
    (inserted : List Nat)
    (free : ∀ x ∈ separators ⟨initial,(separator,body) :: rest⟩, x ∉ inserted) :
    PrefixContext (some separator) (stem ++ squareList inserted ++ [separator]) ⟨body,rest⟩ := by
  constructor
  · intro later laterMember occurs
    have parentMember : later ∈ separators ⟨initial,(separator,body) :: rest⟩ :=
      List.mem_cons_of_mem separator laterMember
    have noStem := context.futureAbsent later parentMember
    have noInserted : later ∉ squareList inserted := fun member => free later parentMember
      ((squareList_mem inserted later).mp member)
    have different : later ≠ separator := by
      intro equal
      exact (List.nodup_cons.mp good.1).1 (by simpa [separators,equal] using laterMember)
    rcases List.mem_append.mp occurs with before | final
    · rcases List.mem_append.mp before with inStem | inInserted
      · exact noStem inStem
      · exact noInserted inInserted
    · exact different (by simpa using final)
  · refine ⟨stem ++ squareList inserted,rfl,?_,first_separator_noTail _ _ _ _ good⟩
    intro occurs
    rcases List.mem_append.mp occurs with inStem | inInserted
    · exact context.futureAbsent separator (by simp [separators]) inStem
    · exact free separator (by simp [separators]) ((squareList_mem inserted separator).mp inInserted)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.saturated_initial_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.first_separator_noTail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.last_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.squareList_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1.PrefixContext.advance

end SemigroupBasis.CoRoots.Order6SporadicSection17.C10D1
