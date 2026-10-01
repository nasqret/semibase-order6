import SemigroupBasis.Examples.SymmetricThreeCompletenessEncoding

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

theorem mem_toggleState_source
    {tested : Nat} {state : List Nat} {letter : Nat}
    (member : tested ∈ toggleState state letter) :
    tested ∈ state ∨ tested = letter := by
  have source := mem_canonicalParity_source (by
    simpa only [toggleState] using member)
  simp only [List.mem_append, List.mem_singleton] at source
  exact source

theorem transitionKeysFrom_head_source :
    ∀ (state letters : List Nat) (key : Word Nat),
      key ∈ transitionKeysFrom state letters → key.head ∈ letters
  | _, [], _, member => by
      simp only [transitionKeysFrom, List.not_mem_nil] at member
  | state, letter :: rest, key, member => by
      simp only [transitionKeysFrom, List.mem_cons] at member
      rcases member with same | later
      · subst key
        simp only [transitionKey_head, List.mem_cons, true_or]
      · exact List.mem_cons_of_mem letter
          (transitionKeysFrom_head_source
            (toggleState state letter) rest key later)

theorem transitionKeysFrom_tail_source :
    ∀ (state letters : List Nat) (key : Word Nat),
      key ∈ transitionKeysFrom state letters →
      ∀ tested, tested ∈ key.tail → tested ∈ state ∨ tested ∈ letters
  | _, [], _, member, _, _ => by
      simp only [transitionKeysFrom, List.not_mem_nil] at member
  | state, letter :: rest, key, member, tested, tailMember => by
      simp only [transitionKeysFrom, List.mem_cons] at member
      rcases member with same | later
      · subst key
        exact Or.inl tailMember
      · have source := transitionKeysFrom_tail_source
          (toggleState state letter) rest key later tested tailMember
        rcases source with toggled | inRest
        · rcases mem_toggleState_source toggled with inState | same
          · exact Or.inl inState
          · exact Or.inr (by simp [same])
        · exact Or.inr (List.mem_cons_of_mem letter inRest)

def identitySupport (identity : Identity Nat) : List Nat :=
  distinctSupport (identity.lhs.toList ++ identity.rhs.toList)

theorem identitySupport_nodup (identity : Identity Nat) :
    (identitySupport identity).Nodup := by
  exact distinctSupport_nodup _

theorem lhsTransition_tail_subset
    (identity : Identity Nat) {key : Word Nat}
    (member : key ∈ transitionKeysFrom [] identity.lhs.toList) :
    ∀ tested, tested ∈ key.tail → tested ∈ identitySupport identity := by
  intro tested tailMember
  have source := transitionKeysFrom_tail_source [] identity.lhs.toList
    key member tested tailMember
  rcases source with impossible | inLeft
  · simp at impossible
  · apply (mem_distinctSupport_iff _ _).mpr
    exact List.mem_append.mpr (Or.inl inLeft)

theorem rhsTransition_tail_subset
    (identity : Identity Nat) {key : Word Nat}
    (member : key ∈ transitionKeysFrom [] identity.rhs.toList) :
    ∀ tested, tested ∈ key.tail → tested ∈ identitySupport identity := by
  intro tested tailMember
  have source := transitionKeysFrom_tail_source [] identity.rhs.toList
    key member tested tailMember
  rcases source with impossible | inRight
  · simp at impossible
  · apply (mem_distinctSupport_iff _ _).mpr
    exact List.mem_append.mpr (Or.inr inRight)

structure KeyEncodingConditions (labels : List Nat)
    (keys : List (Word Nat)) : Prop where
  canonical : ∀ key, key ∈ keys → canonicalParity key.tail = key.tail
  subset : ∀ key, key ∈ keys →
    ∀ tested, tested ∈ key.tail → tested ∈ labels

theorem lhsKeyEncodingConditions (identity : Identity Nat) :
    KeyEncodingConditions (identitySupport identity)
      (transitionKeysFrom [] identity.lhs.toList) where
  canonical := by
    intro key member
    exact transitionKeysFrom_nil_tail_canonical member
  subset := by
    intro key member
    exact lhsTransition_tail_subset identity member

theorem rhsKeyEncodingConditions (identity : Identity Nat) :
    KeyEncodingConditions (identitySupport identity)
      (transitionKeysFrom [] identity.rhs.toList) where
  canonical := by
    intro key member
    exact transitionKeysFrom_nil_tail_canonical member
  subset := by
    intro key member
    exact rhsTransition_tail_subset identity member

/-- Encode the tails of all transitions carrying one selected letter. -/
def encodedTransitionStates (labels : List Nat) (tested : Nat)
    (keys : List (Word Nat)) : List (BitState labels.length) :=
  (keys.filter (fun key => decide (key.head = tested))).map
    (fun key => encodeState labels key.tail)

private theorem tail_conditions {labels : List Nat} {key : Word Nat}
    {rest : List (Word Nat)}
    (conditions : KeyEncodingConditions labels (key :: rest)) :
    KeyEncodingConditions labels rest where
  canonical := by
    intro tested member
    exact conditions.canonical tested (by simp [member])
  subset := by
    intro tested member
    exact conditions.subset tested (by simp [member])

/-- Transition coefficients are exactly Walsh sums of the encoded states. -/
theorem bitWalshSum_encodedTransitionStates
    (labels : List Nat) (tested : Nat) (assignment : BitState labels.length)
    (labelsNodup : labels.Nodup) :
    ∀ (keys : List (Word Nat)),
      KeyEncodingConditions labels keys →
      bitWalshSum assignment
          (encodedTransitionStates labels tested keys) =
        transitionCoefficient tested (reflectionOfVector labels assignment)
          keys
  | [], _ => rfl
  | key :: rest, conditions => by
      have canonical := conditions.canonical key (by simp)
      have subset := conditions.subset key (by simp)
      have stateNodup : key.tail.Nodup := by
        rw [← canonical]
        exact canonicalParity_nodup key.tail
      have character :
          bitWalshSign assignment (encodeState labels key.tail) =
            walshSign
              (reflectionSum (reflectionOfVector labels assignment)
                key.tail) := by
        unfold bitWalshSign
        rw [reflectionSum_eq_bitDot_encodeState labels key.tail assignment
          labelsNodup stateNodup subset]
      have inductionHypothesis := bitWalshSum_encodedTransitionStates
        labels tested assignment labelsNodup rest
        (tail_conditions conditions)
      by_cases selected : key.head = tested
      · simp [encodedTransitionStates, transitionCoefficient,
          keyContribution, selected, character]
        exact congrArg (fun suffix : Fin 3 =>
          walshSign
              (reflectionSum (reflectionOfVector labels assignment) key.tail) +
            suffix) inductionHypothesis
      · simp [encodedTransitionStates, transitionCoefficient,
          keyContribution, selected]
        exact inductionHypothesis

private theorem word_eq_of_head_tail {left right : Word Nat}
    (head : left.head = right.head) (tail : left.tail = right.tail) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at head tail
          subst rightHead
          subst rightTail
          rfl

/-- Counting one encoded state in its letter fiber is the same as counting
the corresponding transition key. -/
theorem count_encodedTransitionStates
    (labels : List Nat) (target : Word Nat)
    (targetCanonical : canonicalParity target.tail = target.tail)
    (targetSubset : ∀ tested, tested ∈ target.tail → tested ∈ labels) :
    ∀ (keys : List (Word Nat)),
      KeyEncodingConditions labels keys →
      keys.count target =
        (encodedTransitionStates labels target.head keys).count
          (encodeState labels target.tail)
  | [], _ => rfl
  | key :: rest, conditions => by
      have inductionHypothesis := count_encodedTransitionStates labels target
        targetCanonical targetSubset rest (tail_conditions conditions)
      by_cases same : key = target
      · subst key
        simp [encodedTransitionStates, inductionHypothesis]
      · by_cases sameHead : key.head = target.head
        · have keyCanonical := conditions.canonical key (by simp)
          have keySubset := conditions.subset key (by simp)
          have encodedDifferent :
              encodeState labels key.tail ≠ encodeState labels target.tail := by
            intro encodedSame
            have tails := encodeState_injective_on_canonical
              labels key.tail target.tail keyCanonical targetCanonical
              keySubset targetSubset encodedSame
            exact same (word_eq_of_head_tail sameHead tails)
          simp [encodedTransitionStates, same, sameHead, encodedDifferent,
            inductionHypothesis]
        · simp [encodedTransitionStates, same, sameHead,
            inductionHypothesis]

theorem encodedTransitionTransforms_eq_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup)
    (tested : Nat) (assignment : BitState (identitySupport identity).length) :
    bitWalshSum assignment
        (encodedTransitionStates (identitySupport identity) tested
          (transitionKeysFrom [] identity.lhs.toList)) =
      bitWalshSum assignment
        (encodedTransitionStates (identitySupport identity) tested
          (transitionKeysFrom [] identity.rhs.toList)) := by
  calc
    bitWalshSum assignment
        (encodedTransitionStates (identitySupport identity) tested
          (transitionKeysFrom [] identity.lhs.toList)) =
        transitionCoefficient tested
          (reflectionOfVector (identitySupport identity) assignment)
          (transitionKeysFrom [] identity.lhs.toList) :=
      bitWalshSum_encodedTransitionStates
        (identitySupport identity) tested assignment
        (identitySupport_nodup identity)
        (transitionKeysFrom [] identity.lhs.toList)
        (lhsKeyEncodingConditions identity)
    _ = transitionCoefficient tested
          (reflectionOfVector (identitySupport identity) assignment)
          (transitionKeysFrom [] identity.rhs.toList) :=
      transitionCoefficient_eq_of_valid identity valid tested _
    _ = bitWalshSum assignment
        (encodedTransitionStates (identitySupport identity) tested
          (transitionKeysFrom [] identity.rhs.toList)) :=
      (bitWalshSum_encodedTransitionStates
        (identitySupport identity) tested assignment
        (identitySupport_nodup identity)
        (transitionKeysFrom [] identity.rhs.toList)
        (rhsKeyEncodingConditions identity)).symm

/-- S3 validity determines every directed transition multiplicity modulo
three. -/
theorem transitionKey_modCounts_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy symmetricThree.semigroup) :
    ∀ key : Word Nat,
      (transitionKeysFrom [] identity.lhs.toList).count key % 3 =
        (transitionKeysFrom [] identity.rhs.toList).count key % 3 := by
  intro key
  let labels := identitySupport identity
  let leftKeys := transitionKeysFrom [] identity.lhs.toList
  let rightKeys := transitionKeysFrom [] identity.rhs.toList
  have transforms :
      ∀ tested (assignment : BitState labels.length),
        bitWalshSum assignment
            (encodedTransitionStates labels tested leftKeys) =
          bitWalshSum assignment
            (encodedTransitionStates labels tested rightKeys) := by
    intro tested assignment
    exact encodedTransitionTransforms_eq_of_valid identity valid
      tested assignment
  have vectorCounts (tested : Nat) :
      ∀ target : BitState labels.length,
        (encodedTransitionStates labels tested leftKeys).count target % 3 =
          (encodedTransitionStates labels tested rightKeys).count target % 3 :=
    bitWalshSum_modCounts labels.length
      (encodedTransitionStates labels tested leftKeys)
      (encodedTransitionStates labels tested rightKeys)
      (transforms tested)
  by_cases inLeft : key ∈ leftKeys
  · have keyCanonical := (lhsKeyEncodingConditions identity).canonical key inLeft
    have keySubset := (lhsKeyEncodingConditions identity).subset key inLeft
    rw [count_encodedTransitionStates labels key keyCanonical keySubset
        leftKeys (lhsKeyEncodingConditions identity),
      count_encodedTransitionStates labels key keyCanonical keySubset
        rightKeys (rhsKeyEncodingConditions identity)]
    exact vectorCounts key.head (encodeState labels key.tail)
  · by_cases inRight : key ∈ rightKeys
    · have keyCanonical :=
        (rhsKeyEncodingConditions identity).canonical key inRight
      have keySubset := (rhsKeyEncodingConditions identity).subset key inRight
      rw [count_encodedTransitionStates labels key keyCanonical keySubset
          leftKeys (lhsKeyEncodingConditions identity),
        count_encodedTransitionStates labels key keyCanonical keySubset
          rightKeys (rhsKeyEncodingConditions identity)]
      exact vectorCounts key.head (encodeState labels key.tail)
    · rw [List.count_eq_zero.mpr inLeft, List.count_eq_zero.mpr inRight]

end SemigroupBasis.Examples.SymmetricThreeCompleteness
