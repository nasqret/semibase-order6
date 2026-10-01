import SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay

/-! The canonical phase state and its protected-initial marker. These are
unbounded list invariants; no finite word window is used in their statements. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseData

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_831

def HasDouble (phases : List Phase) : Prop :=
  ∃ phase ∈ phases, phase.doubled = true

instance (phases : List Phase) : Decidable (HasDouble phases) := by
  unfold HasDouble
  infer_instance

@[simp] theorem hasDouble_nil : ¬ HasDouble [] := by simp [HasDouble]
@[simp] theorem hasDouble_cons (phase : Phase) (rest : List Phase) :
    HasDouble (phase :: rest) ↔ phase.doubled = true ∨ HasDouble rest := by
  simp [HasDouble]
@[simp] theorem hasDouble_append (front back : List Phase) :
    HasDouble (front ++ back) ↔ HasDouble front ∨ HasDouble back := by
  simp [HasDouble, List.mem_append, or_and_right, exists_or]

/-- The first doubled phase holds the protected initial letter; later phases
are ordinary lower canonical runs. -/
def marked (head : Nat) : List Phase → List Nat
  | [] => []
  | phase :: rest =>
      if phase.doubled then
        [phase.label, head] ++ renderPhases rest
      else phase.label :: marked head rest

def renderState (head : Nat) (phases : List Phase) (repeated : Bool) : List Nat :=
  if repeated then marked head phases else renderPhases phases

def nextRepeated (head : Nat) (repeated : Bool) (letter : Nat) : Bool :=
  repeated || decide (letter = head)

structure StateOK (head : Nat) (phases : List Phase) (repeated : Bool) : Prop where
  shape : ∃ doubled rest, phases = ⟨head, doubled⟩ :: rest
  labelsNodup : (phaseLabels phases).Nodup
  freshHead : repeated = false → ∃ rest, phases = ⟨head, false⟩ :: rest
  markedPhase : repeated = true → HasDouble phases

theorem initialStateOK (head : Nat) : StateOK head [⟨head, false⟩] false where
  shape := ⟨false, [], rfl⟩
  labelsNodup := by simp [phaseLabels]
  freshHead := by intro _; exact ⟨[], rfl⟩
  markedPhase := by simp

theorem StateOK.ne_nil {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) : phases ≠ [] := by
  obtain ⟨bit, rest, rfl⟩ := ok.shape
  simp

theorem StateOK.head_mem {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) : head ∈ phaseLabels phases := by
  obtain ⟨bit, rest, rfl⟩ := ok.shape
  simp [phaseLabels]

theorem hasDouble_markLast (phases : List Phase) (nonempty : phases ≠ []) :
    HasDouble (markLastDoubled phases) := by
  induction phases with
  | nil => exact (nonempty rfl).elim
  | cons phase rest ih =>
      cases rest with
      | nil => simp [markLastDoubled]
      | cons next tail =>
          exact (hasDouble_cons _ _).2 (Or.inr (ih (by simp)))

theorem markLast_shape (head : Nat) (doubled : Bool) (rest : List Phase) :
    ∃ bit tail, markLastDoubled (⟨head, doubled⟩ :: rest) = ⟨head, bit⟩ :: tail := by
  cases rest with
  | nil => exact ⟨true, [], rfl⟩
  | cons phase tail => exact ⟨doubled, markLastDoubled (phase :: tail), rfl⟩

theorem stateOK_step {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (letter : Nat) :
    StateOK head (phaseStep phases letter) (nextRepeated head repeated letter) := by
  by_cases old : letter ∈ phaseLabels phases
  · rw [phaseStep, if_pos old]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨bit, rest, rfl⟩ := ok.shape
      exact markLast_shape head bit rest
    · simpa only [phaseLabels_markLastDoubled] using ok.labelsNodup
    · intro nextFalse
      have repFalse : repeated = false := by
        cases repeated <;> simp_all [nextRepeated]
      have notHead : letter ≠ head := by
        intro equal
        subst letter
        simp [nextRepeated] at nextFalse
      obtain ⟨rest, shape⟩ := ok.freshHead repFalse
      rw [shape] at old ⊢
      cases rest with
      | nil => simp [phaseLabels, notHead] at old
      | cons phase tail => exact ⟨markLastDoubled (phase :: tail), rfl⟩
    · intro _
      exact hasDouble_markLast phases ok.ne_nil
  · rw [phaseStep, if_neg old]
    have notHead : letter ≠ head := by
      intro equal
      exact old (by simpa only [equal] using ok.head_mem)
    have sameRepeated : nextRepeated head repeated letter = repeated := by
      simp [nextRepeated, notHead]
    rw [sameRepeated]
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨bit, rest, rfl⟩ := ok.shape
      exact ⟨bit, rest ++ [⟨letter, false⟩], rfl⟩
    · have labels : phaseLabels (phases ++ [⟨letter, false⟩]) = phaseLabels phases ++ [letter] := by
        simp [phaseLabels]
      rw [labels]
      apply List.nodup_append.mpr
      refine ⟨ok.labelsNodup, by simp, ?_⟩
      intro left leftMember right rightMember equal
      have rightEq : right = letter := by simpa using rightMember
      subst right
      subst left
      exact old leftMember
    · intro fresh
      obtain ⟨rest, rfl⟩ := ok.freshHead fresh
      exact ⟨rest ++ [⟨letter, false⟩], rfl⟩
    · intro repeatedTrue
      exact (hasDouble_append _ _).2 (Or.inl (ok.markedPhase repeatedTrue))

theorem mem_marked_of_mem_labels (head letter : Nat) :
    ∀ phases : List Phase, letter ∈ phaseLabels phases → letter ∈ marked head phases
  | [], member => by simp [phaseLabels] at member
  | phase :: rest, member => by
      have alternatives : letter = phase.label ∨ letter ∈ phaseLabels rest := by
        simpa [phaseLabels] using member
      cases bit : phase.doubled with
      | false =>
          rcases alternatives with equal | later
          · simp [marked, bit, equal]
          · simp [marked, bit, mem_marked_of_mem_labels head letter rest later]
      | true =>
          rcases alternatives with equal | later
          · simp [marked, bit, equal]
          · simp [marked, bit, (mem_renderPhases_iff letter rest).2 later]

theorem head_mem_marked (head : Nat) :
    ∀ phases : List Phase, HasDouble phases → head ∈ marked head phases
  | [], present => (hasDouble_nil present).elim
  | phase :: rest, present => by
      cases bit : phase.doubled with
      | true => simp [marked, bit]
      | false =>
          have later : HasDouble rest := by simpa [bit] using present
          simp [marked, bit, head_mem_marked head rest later]

theorem plain_eq_labels_of_noDouble (phases : List Phase) (none : ¬ HasDouble phases) :
    renderPhases phases = phaseLabels phases := by
  induction phases with
  | nil => rfl
  | cons phase rest ih =>
      have neither : phase.doubled ≠ true ∧ ¬ HasDouble rest := by simpa using none
      have bit : phase.doubled = false := by cases value : phase.doubled <;> simp_all
      change renderPhase phase ++ renderPhases rest = phase.label :: phaseLabels rest
      rw [ih neither.2]
      simp [renderPhase, bit]

theorem marked_eq_labels_of_noDouble (head : Nat) (phases : List Phase) (none : ¬ HasDouble phases) :
    marked head phases = phaseLabels phases := by
  induction phases with
  | nil => rfl
  | cons phase rest ih =>
      have neither : phase.doubled ≠ true ∧ ¬ HasDouble rest := by simpa using none
      have bit : phase.doubled = false := by cases value : phase.doubled <;> simp_all
      simp [marked, phaseLabels, bit, ih neither.2]

theorem marked_append (head : Nat) (front back : List Phase) :
    marked head (front ++ back) =
      if HasDouble front then marked head front ++ renderPhases back
      else phaseLabels front ++ marked head back := by
  classical
  induction front with
  | nil => simp [marked, phaseLabels]
  | cons phase rest ih =>
      cases bit : phase.doubled <;> by_cases present : HasDouble rest <;>
        simp [marked, bit, present, ih, phaseLabels, renderPhases, List.append_assoc]

theorem first_double_split {phases : List Phase} (present : HasDouble phases) :
    ∃ before phase after, phases = before ++ phase :: after ∧
      ¬ HasDouble before ∧ phase.doubled = true := by
  induction phases with
  | nil => exact (hasDouble_nil present).elim
  | cons phase rest ih =>
      by_cases doubled : phase.doubled = true
      · exact ⟨[], phase, rest, rfl, hasDouble_nil, doubled⟩
      · have later : HasDouble rest := by simpa [doubled] using present
        obtain ⟨before, selected, after, shape, none, bit⟩ := ih later
        exact ⟨phase :: before, selected, after, by simp [shape], by simp [doubled, none], bit⟩

theorem marked_first_double (head : Nat) (before : List Phase) (phase : Phase) (after : List Phase)
    (none : ¬ HasDouble before) (doubled : phase.doubled = true) :
    marked head (before ++ phase :: after) =
      phaseLabels before ++ [phase.label, head] ++ renderPhases after := by
  rw [marked_append, if_neg none]
  simp [marked, doubled, List.append_assoc]

theorem plain_first_double (before : List Phase) (phase : Phase) (after : List Phase)
    (none : ¬ HasDouble before) (doubled : phase.doubled = true) :
    renderPhases (before ++ phase :: after) =
      phaseLabels before ++ [phase.label, phase.label] ++ renderPhases after := by
  simp only [renderPhases, List.flatMap_append, List.flatMap_cons]
  change renderPhases before ++ (renderPhase phase ++ renderPhases after) = _
  rw [plain_eq_labels_of_noDouble before none]
  simp [renderPhase, doubled, List.append_assoc, renderPhases]

theorem markLast_append_nonempty (front back : List Phase) (nonempty : back ≠ []) :
    markLastDoubled (front ++ back) = front ++ markLastDoubled back := by
  induction front with
  | nil => simp
  | cons phase rest ih =>
      cases rest with
      | nil => cases back <;> simp_all [markLastDoubled]
      | cons next tail => simpa [markLastDoubled] using congrArg (phase :: ·) ih

theorem marked_markLast_of_noDouble (head : Nat) (phases : List Phase)
    (nonempty : phases ≠ []) (none : ¬ HasDouble phases) :
    marked head (markLastDoubled phases) = phaseLabels phases ++ [head] := by
  induction phases with
  | nil => exact (nonempty rfl).elim
  | cons phase rest ih =>
      have neither : phase.doubled ≠ true ∧ ¬ HasDouble rest := by simpa using none
      have bit : phase.doubled = false := by cases value : phase.doubled <;> simp_all
      cases rest with
      | nil => simp [marked, markLastDoubled, phaseLabels, renderPhases]
      | cons next tail =>
          simpa [marked, markLastDoubled, phaseLabels, bit] using
            congrArg (phase.label :: ·) (ih (by simp) neither.2)

theorem renderState_shape {head : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) :
    ∃ tail, renderState head phases repeated = head :: tail := by
  cases repeated with
  | false =>
      obtain ⟨rest, rfl⟩ := ok.freshHead rfl
      exact ⟨renderPhases rest, rfl⟩
  | true =>
      obtain ⟨bit, rest, rfl⟩ := ok.shape
      cases bit with
      | false => exact ⟨marked head rest, rfl⟩
      | true => exact ⟨head :: renderPhases rest, rfl⟩

theorem renderState_tail_contains {head letter : Nat} {phases : List Phase} {repeated : Bool}
    (ok : StateOK head phases repeated) (member : letter ∈ phaseLabels phases)
    (allowed : repeated = true ∨ letter ≠ head) :
    letter ∈ (renderState head phases repeated).tail := by
  cases repeated with
  | false =>
      have notHead : letter ≠ head := by simpa using allowed
      obtain ⟨rest, rfl⟩ := ok.freshHead rfl
      have later : letter ∈ phaseLabels rest := by simpa [phaseLabels, notHead] using member
      simpa [renderState, renderPhases, renderPhase] using (mem_renderPhases_iff letter rest).2 later
  | true =>
      obtain ⟨bit, rest, shape⟩ := ok.shape
      rw [shape] at member ⊢
      have alternatives : letter = head ∨ letter ∈ phaseLabels rest := by simpa [phaseLabels] using member
      cases bit with
      | true =>
          rcases alternatives with equal | later
          · simp [renderState, marked, equal]
          · simpa [renderState, marked] using
              (show letter = head ∨ letter ∈ renderPhases rest from Or.inr ((mem_renderPhases_iff letter rest).2 later))
      | false =>
          rcases alternatives with equal | later
          · have present : HasDouble rest := by simpa [shape] using ok.markedPhase rfl
            simpa [renderState, marked, equal] using head_mem_marked head rest present
          · simpa [renderState, marked] using mem_marked_of_mem_labels head letter rest later

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03PhaseData
