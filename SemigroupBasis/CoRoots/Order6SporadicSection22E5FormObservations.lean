import SemigroupBasis.CoRoots.Order6SporadicSection22E5SimpleOrder

/-! Structural observations of saturated E5 forms. No semantic cancellation
is used: observations at a later separator are read from the original full
word and then restricted to the corresponding tail form. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

theorem squareList_mem (letters : List Nat) (x : Nat) : x ∈ squareList letters ↔ x ∈ letters := by
  induction letters with
  | nil => simp [squareList_nil]
  | cons h t ih => simp [squareList_cons,ih]

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

structure FormObserved (left right : SquareForm) : Prop where
  separators_eq : separators left = separators right
  heads : (renderForm left).head? = (renderForm right).head?
  support : ∀ x, x ∈ renderForm left ↔ x ∈ renderForm right
  nextHeads : ∀ separator ∈ separators left,
    (afterFirst separator (renderForm left)).head? = (afterFirst separator (renderForm right)).head?
  afterSupports : ∀ separator ∈ separators left, ∀ x,
    x ∈ afterFirst separator (renderForm left) ↔ x ∈ afterFirst separator (renderForm right)

theorem normalForm_separators (letters : List Nat) :
    separators (normalForm letters) = letters.filter (simpleMask letters) := by
  rw [normalForm,saturateForm_separators,decompose_separators]

theorem normalForm_observed (left right : List Nat) (same : SameEval left right) :
    FormObserved (normalForm left) (normalForm right) := by
  have leftRun := derives_sameEval (derives_normalForm left)
  have rightRun := derives_sameEval (derives_normalForm right)
  have joint := leftRun.symm.trans (same.trans rightRun)
  have separatorCount (separator : Nat) (member : separator ∈ separators (normalForm left)) :
      (renderForm (normalForm left)).count separator = 1 := by
    rw [normalForm_separators] at member
    have one : left.count separator = 1 := by simpa [simpleMask] using (List.mem_filter.mp member).2
    exact (leftRun.countOne separator).mp one
  exact ⟨by simpa [normalForm_separators] using same.simpleSubsequence,
    joint.head,joint.mem,
    fun separator member => (joint.afterFirst separator (separatorCount separator member)).1,
    fun separator member => (joint.afterFirst separator (separatorCount separator member)).2⟩

theorem squareInitial_noSeparator (form : SquareForm) (good : WellFormed form) (separator : Nat)
    (member : separator ∈ separators form) : separator ∉ squareList form.initial := by
  intro occurs
  exact good.2 separator (List.mem_append.mpr (Or.inl ((squareList_mem _ _).mp occurs))) member

theorem renderHead_simple_of_empty (form : SquareForm) (empty : form.initial = []) (x : Nat)
    (head : (renderForm form).head? = some x) : x ∈ separators form := by
  cases slotsShape : form.slots with
  | nil => simp [renderForm,empty,slotsShape,squareList_nil,renderSlots] at head
  | cons slot rest =>
      rcases slot with ⟨separator,body⟩
      have equal : separator = x := by
        simpa [renderForm,empty,slotsShape,squareList_nil,renderSlots] using head
      simp [separators,slotsShape,equal]

theorem observed_initial_heads (left right : SquareForm) (leftGood : WellFormed left)
    (rightGood : WellFormed right) (observed : FormObserved left right) :
    left.initial.head? = right.initial.head? := by
  cases leftShape : left.initial with
  | nil =>
      cases rightShape : right.initial with
      | nil => rfl
      | cons y ys =>
          have head : (renderForm left).head? = some y := observed.heads.trans
            (by simp [renderForm,rightShape,squareList_cons])
          have simpleLeft := renderHead_simple_of_empty left leftShape y head
          have simpleRight : y ∈ separators right := by simpa [← observed.separators_eq] using simpleLeft
          have bodyRight : y ∈ bodySupport right := by simp [bodySupport,rightShape]
          exact False.elim (rightGood.2 y bodyRight simpleRight)
  | cons x xs =>
      cases rightShape : right.initial with
      | nil =>
          have head : (renderForm right).head? = some x := observed.heads.symm.trans
            (by simp [renderForm,leftShape,squareList_cons])
          have simpleRight := renderHead_simple_of_empty right rightShape x head
          have simpleLeft : x ∈ separators left := by simpa [observed.separators_eq] using simpleRight
          have bodyLeft : x ∈ bodySupport left := by simp [bodySupport,leftShape]
          exact False.elim (leftGood.2 x bodyLeft simpleLeft)
      | cons y ys =>
          simpa [renderForm,leftShape,rightShape,squareList_cons] using observed.heads

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

theorem observed_initial_derives (left right : SquareForm) (leftGood : WellFormed left)
    (rightGood : WellFormed right) (leftSaturated : Saturated left) (rightSaturated : Saturated right)
    (observed : FormObserved left right) : ListDerives (squareList left.initial) (squareList right.initial) := by
  have heads := observed_initial_heads left right leftGood rightGood observed
  cases leftShape : left.initial with
  | nil =>
      cases rightShape : right.initial with
      | nil => exact S5_107.ListDerives.refl _
      | cons y ys => simp [leftShape,rightShape] at heads
  | cons x xs =>
      cases rightShape : right.initial with
      | nil => simp [leftShape,rightShape] at heads
      | cons y ys =>
          have equal : x = y := by simpa [leftShape,rightShape] using heads
          subst y
          have leftNonempty : left.initial ≠ [] := by simp [leftShape]
          have rightNonempty : right.initial ≠ [] := by simp [rightShape]
          have content : ∀ marker, marker ∈ x :: xs ↔ marker ∈ x :: ys := by
            intro marker
            have leftBoundary := saturated_initial_mem left leftGood leftSaturated leftNonempty marker
            have rightBoundary := saturated_initial_mem right rightGood rightSaturated rightNonempty marker
            have relation : marker ∈ left.initial ↔ marker ∈ right.initial := by
              rw [leftBoundary,rightBoundary]
              exact and_congr (observed.support marker) (by rw [observed.separators_eq])
            simpa [leftShape,rightShape] using relation
          simpa [leftShape,rightShape] using squareBlocks_same_content x xs ys content

theorem tail_wellFormed (initial : List Nat) (separator : Nat) (body : List Nat) (rest : Slots)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) : WellFormed ⟨body,rest⟩ := by
  constructor
  · exact (List.nodup_cons.mp good.1).2
  · intro x member simpleMember
    exact good.2 x (List.mem_append.mpr (Or.inr member)) (List.mem_cons_of_mem separator simpleMember)

theorem first_separator_suffix (initial : List Nat) (separator : Nat) (body : List Nat) (rest : Slots)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) :
    afterFirst separator (renderForm ⟨initial,(separator,body) :: rest⟩) = renderForm ⟨body,rest⟩ := by
  have absent := squareInitial_noSeparator _ good separator (by simp [separators])
  rw [renderForm,afterFirst_append separator _ _ absent]
  simp [renderSlots,afterFirst,renderForm]

theorem later_separator_suffix (initial : List Nat) (separator : Nat) (body : List Nat) (rest : Slots)
    (good : WellFormed ⟨initial,(separator,body) :: rest⟩) (later : Nat) (member : later ∈ rest.map Prod.fst) :
    afterFirst later (renderForm ⟨initial,(separator,body) :: rest⟩) =
      afterFirst later (renderForm ⟨body,rest⟩) := by
  have absent := squareInitial_noSeparator _ good later (List.mem_cons_of_mem separator member)
  have different : separator ≠ later := by
    intro equal
    exact (List.nodup_cons.mp good.1).1 (by simpa [equal] using member)
  rw [renderForm,afterFirst_append later _ _ absent]
  simp [renderSlots,afterFirst,different,renderForm]

theorem observed_tail (leftInitial rightInitial : List Nat) (separator : Nat)
    (leftBody rightBody : List Nat) (leftRest rightRest : Slots)
    (leftGood : WellFormed ⟨leftInitial,(separator,leftBody) :: leftRest⟩)
    (rightGood : WellFormed ⟨rightInitial,(separator,rightBody) :: rightRest⟩)
    (observed : FormObserved ⟨leftInitial,(separator,leftBody) :: leftRest⟩
      ⟨rightInitial,(separator,rightBody) :: rightRest⟩) :
    FormObserved ⟨leftBody,leftRest⟩ ⟨rightBody,rightRest⟩ := by
  have tailSeparators : leftRest.map Prod.fst = rightRest.map Prod.fst :=
    (List.cons.inj observed.separators_eq).2
  have current : separator ∈ separators ⟨leftInitial,(separator,leftBody) :: leftRest⟩ := by
    simp [separators]
  constructor
  · exact tailSeparators
  · have equal := observed.nextHeads separator current
    simpa [first_separator_suffix _ _ _ _ leftGood,first_separator_suffix _ _ _ _ rightGood] using equal
  · intro x
    have equal := observed.afterSupports separator current x
    simpa [first_separator_suffix _ _ _ _ leftGood,first_separator_suffix _ _ _ _ rightGood] using equal
  · intro later member
    have rightMember : later ∈ rightRest.map Prod.fst := by
      rw [← tailSeparators]
      exact member
    have equal := observed.nextHeads later (List.mem_cons_of_mem separator member)
    rw [later_separator_suffix _ _ _ _ leftGood later member,
      later_separator_suffix _ _ _ _ rightGood later rightMember] at equal
    exact equal
  · intro later member x
    have rightMember : later ∈ rightRest.map Prod.fst := by
      rw [← tailSeparators]
      exact member
    have equal := observed.afterSupports later (List.mem_cons_of_mem separator member) x
    rw [later_separator_suffix _ _ _ _ leftGood later member,
      later_separator_suffix _ _ _ _ rightGood later rightMember] at equal
    exact equal

#print axioms normalForm_observed
#print axioms observed_initial_heads
#print axioms saturated_initial_mem
#print axioms observed_initial_derives
#print axioms tail_wellFormed
#print axioms first_separator_suffix
#print axioms later_separator_suffix
#print axioms observed_tail

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
