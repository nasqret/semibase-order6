import SemigroupBasis.Examples.SymmetricThreeCompletenessWalsh

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

private theorem finTwoEncoding_mul_one (value : Fin 2) : value * 1 = value := by
  decide +revert

private theorem finTwoEncoding_mul_zero (value : Fin 2) : value * 0 = 0 := by
  decide +revert

private theorem finTwoEncoding_zero_add (value : Fin 2) : 0 + value = value := by
  decide +revert

/-- Keep one copy of every label.  Order is irrelevant; only the explicit
finite support and its duplicate-free property are used below. -/
def distinctSupport : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := distinctSupport rest
      if letter ∈ reduced then reduced else letter :: reduced

theorem distinctSupport_nodup (letters : List Nat) :
    (distinctSupport letters).Nodup := by
  induction letters with
  | nil => exact List.nodup_nil
  | cons letter rest inductionHypothesis =>
      simp only [distinctSupport]
      by_cases member : letter ∈ distinctSupport rest
      · rw [if_pos member]
        exact inductionHypothesis
      · rw [if_neg member]
        exact List.nodup_cons.mpr ⟨member, inductionHypothesis⟩

theorem mem_distinctSupport_iff (tested : Nat) (letters : List Nat) :
    tested ∈ distinctSupport letters ↔ tested ∈ letters := by
  induction letters with
  | nil => simp [distinctSupport]
  | cons letter rest inductionHypothesis =>
      simp only [distinctSupport]
      by_cases member : letter ∈ distinctSupport rest
      · rw [if_pos member, List.mem_cons]
        constructor
        · intro testedMember
          exact Or.inr (inductionHypothesis.mp testedMember)
        · intro sourceMember
          rcases sourceMember with same | restMember
          · subst tested
            exact member
          · exact inductionHypothesis.mpr restMember
      · rw [if_neg member, List.mem_cons, List.mem_cons]
        constructor
        · intro selected
          rcases selected with same | restMember
          · exact Or.inl same
          · exact Or.inr (inductionHypothesis.mp restMember)
        · intro source
          rcases source with same | restMember
          · exact Or.inl same
          · exact Or.inr (inductionHypothesis.mpr restMember)

/-- Characteristic vector of a state on an explicit finite label list. -/
def encodeState : (labels : List Nat) → List Nat → BitState labels.length
  | [], _ => fun impossible => Fin.elim0 impossible
  | label :: rest, state =>
      bitCons (if label ∈ state then 1 else 0) (encodeState rest state)

/-- Extend a finite Boolean vector to a reflection assignment on all natural
variables.  Labels outside the support receive zero. -/
def reflectionOfVector :
    (labels : List Nat) → BitState labels.length → Nat → Fin 2
  | [], _, _ => 0
  | label :: rest, assignment, tested =>
      if tested = label then assignment ⟨0, by simp⟩
      else reflectionOfVector rest (bitTail assignment) tested

/-- Labels selected by a state's characteristic vector. -/
def selectedLabels (labels state : List Nat) : List Nat :=
  labels.filter (fun label => decide (label ∈ state))

private theorem reflectionSum_congr_on
    (left right : Nat → Fin 2) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters → left letter = right letter) →
      reflectionSum left letters = reflectionSum right letters
  | [], _ => rfl
  | letter :: rest, agreement => by
      simp only [reflectionSum_cons]
      rw [agreement letter (by simp),
        reflectionSum_congr_on left right rest]
      intro tested member
      exact agreement tested (by simp [member])

private theorem reflectionSum_cons_support_tail
    (label : Nat) (rest state : List Nat)
    (assignment : BitState (label :: rest).length)
    (fresh : label ∉ rest) :
    reflectionSum (reflectionOfVector (label :: rest) assignment)
        (selectedLabels rest state) =
      reflectionSum (reflectionOfVector rest (bitTail assignment))
        (selectedLabels rest state) := by
  apply reflectionSum_congr_on
  intro tested member
  have restMember : tested ∈ rest :=
    (List.mem_filter.mp member).1
  have different : tested ≠ label := by
    intro same
    subst tested
    exact fresh restMember
  simp [reflectionOfVector, different]

/-- Dot product against the characteristic vector is the same character as
summing the extended reflection assignment over the selected support. -/
theorem bitDot_encodeState (labels state : List Nat)
    (assignment : BitState labels.length)
    (labelsNodup : labels.Nodup) :
    bitDot assignment (encodeState labels state) =
      reflectionSum (reflectionOfVector labels assignment)
        (selectedLabels labels state) := by
  induction labels with
  | nil => rfl
  | cons label rest inductionHypothesis =>
      have fresh := (List.nodup_cons.mp labelsNodup).1
      have restNodup := (List.nodup_cons.mp labelsNodup).2
      have tailAgreement := reflectionSum_cons_support_tail
        label rest state assignment fresh
      have tailResult := inductionHypothesis (bitTail assignment) restNodup
      by_cases member : label ∈ state
      · have selected :
            selectedLabels (label :: rest) state =
              label :: selectedLabels rest state := by
          simp [selectedLabels, member]
        rw [selected]
        simp only [encodeState, member, if_pos, bitDot, bitCons_zero,
          bitTail_bitCons, reflectionSum_cons]
        rw [tailAgreement, ← tailResult]
        simp only [reflectionOfVector, if_pos, finTwoEncoding_mul_one]
        apply congrArg (fun head : Fin 2 =>
          head + bitDot (bitTail assignment) (encodeState rest state))
        apply congrArg assignment
        apply Fin.ext
        rfl
      · have selected :
            selectedLabels (label :: rest) state =
              selectedLabels rest state := by
          simp [selectedLabels, member]
        rw [selected]
        simp only [encodeState, if_neg member, bitDot, bitCons_zero,
          bitTail_bitCons]
        rw [tailAgreement, ← tailResult]
        rw [finTwoEncoding_mul_zero, finTwoEncoding_zero_add]

private theorem selectedLabels_perm_state
    (labels state : List Nat) (labelsNodup : labels.Nodup)
    (stateNodup : state.Nodup)
    (subset : ∀ tested, tested ∈ state → tested ∈ labels) :
    state.Perm (selectedLabels labels state) := by
  rw [List.perm_iff_count]
  intro tested
  rw [stateNodup.count]
  have selectedNodup : (selectedLabels labels state).Nodup := by
    unfold selectedLabels
    exact labelsNodup.filter _
  rw [selectedNodup.count]
  unfold selectedLabels
  simp only [List.mem_filter, decide_eq_true_eq]
  by_cases member : tested ∈ state
  · simp [member, subset tested member]
  · simp [member]

/-- Reflection sums on a duplicate-free state are exactly Boolean dot
products, provided the label list contains the state. -/
theorem reflectionSum_eq_bitDot_encodeState
    (labels state : List Nat) (assignment : BitState labels.length)
    (labelsNodup : labels.Nodup) (stateNodup : state.Nodup)
    (subset : ∀ tested, tested ∈ state → tested ∈ labels) :
    reflectionSum (reflectionOfVector labels assignment) state =
      bitDot assignment (encodeState labels state) := by
  calc
    reflectionSum (reflectionOfVector labels assignment) state =
        reflectionSum (reflectionOfVector labels assignment)
          (selectedLabels labels state) :=
      reflectionSum_perm _
        (selectedLabels_perm_state labels state labelsNodup stateNodup subset)
    _ = bitDot assignment (encodeState labels state) :=
      (bitDot_encodeState labels state assignment labelsNodup).symm

private theorem encodeState_eq_mem_on_labels :
    ∀ (labels left right : List Nat),
      encodeState labels left = encodeState labels right →
      ∀ tested, tested ∈ labels → (tested ∈ left ↔ tested ∈ right)
  | [], _, _, _, tested, member => by
      simp at member
  | label :: rest, left, right, equality, tested, member => by
      have heads := congrFun equality ⟨0, by simp⟩
      have tails := congrArg bitTail equality
      change (if label ∈ left then 1 else 0) =
        (if label ∈ right then 1 else 0) at heads
      change encodeState rest left = encodeState rest right at tails
      simp only [List.mem_cons] at member
      rcases member with same | restMember
      · subst tested
        by_cases leftMember : label ∈ left <;>
          by_cases rightMember : label ∈ right <;>
          simp [leftMember, rightMember] at heads ⊢
      · exact encodeState_eq_mem_on_labels rest left right tails
          tested restMember

/-- Encoding is injective on canonical parity states contained in the same
finite support. -/
theorem encodeState_injective_on_canonical
    (labels left right : List Nat)
    (leftCanonical : canonicalParity left = left)
    (rightCanonical : canonicalParity right = right)
    (leftSubset : ∀ tested, tested ∈ left → tested ∈ labels)
    (rightSubset : ∀ tested, tested ∈ right → tested ∈ labels)
    (encoded : encodeState labels left = encodeState labels right) :
    left = right := by
  have leftNodup : left.Nodup := by
    rw [← leftCanonical]
    exact canonicalParity_nodup left
  have rightNodup : right.Nodup := by
    rw [← rightCanonical]
    exact canonicalParity_nodup right
  have membership : ∀ tested, tested ∈ left ↔ tested ∈ right := by
    intro tested
    constructor
    · intro leftMember
      exact (encodeState_eq_mem_on_labels labels left right encoded
        tested (leftSubset tested leftMember)).mp leftMember
    · intro rightMember
      exact (encodeState_eq_mem_on_labels labels left right encoded
        tested (rightSubset tested rightMember)).mpr rightMember
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro tested
    rw [leftNodup.count, rightNodup.count]
    simp only [membership tested]
  have leftSorted : left.Pairwise (· ≤ ·) := by
    rw [← leftCanonical]
    exact canonicalParity_pairwise left
  have rightSorted : right.Pairwise (· ≤ ·) := by
    rw [← rightCanonical]
    exact canonicalParity_pairwise right
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

end SemigroupBasis.Examples.SymmetricThreeCompleteness
