import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.Examples

/-- The supports of two lists are disjoint. -/
def ConnectedComponentSupportsDisjoint
    {α : Type} (left right : List α) : Prop :=
  ∀ letter, letter ∈ left → letter ∉ right

/-- The supports of two lists intersect. -/
def ConnectedComponentSupportsIntersect
    {α : Type} (left right : List α) : Prop :=
  ∃ letter, letter ∈ left ∧ letter ∈ right

theorem connectedComponentSupportsIntersect_symm
    {α : Type} {left right : List α}
    (intersect : ConnectedComponentSupportsIntersect left right) :
    ConnectedComponentSupportsIntersect right left := by
  rcases intersect with ⟨letter, leftMember, rightMember⟩
  exact ⟨letter, rightMember, leftMember⟩

/-- A list is support-connected when every nontrivial displayed cut has a
letter on both sides. This formulation is convenient for the suffix-peeling
induction used in the `S4_70` normalizer. -/
def ConnectedComponentSupportConnected
    {α : Type} (letters : List α) : Prop :=
  ∀ left right,
    letters = left ++ right →
      left ≠ [] →
        right ≠ [] →
          ConnectedComponentSupportsIntersect left right

theorem connectedComponentSupportConnected_cons_tail
    {α : Type} {head : α} {tail : List α}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ []) :
    head ∈ tail := by
  have intersect :=
    connected [head] tail (by simp) (by simp) tailNonempty
  rcases intersect with ⟨letter, leftMember, rightMember⟩
  have letterEq : letter = head := by
    simpa using leftMember
  simpa [letterEq] using rightMember

theorem connectedComponent_head_count_eq_two
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ [])
    (twoLimited : UniqueSeparatorTwoLimited (head :: tail)) :
    (head :: tail).count head = 2 := by
  have headInTail :=
    connectedComponentSupportConnected_cons_tail connected tailNonempty
  have tailPositive : 1 ≤ tail.count head :=
    List.one_le_count_iff.mpr headInTail
  have totalAtMost := twoLimited head
  simp only [List.count_cons_self] at totalAtMost ⊢
  omega

/-- A fixed prefix is linked to a remaining suffix when every nonempty tail
of that suffix intersects the prefix together with the part already passed.
This is exactly the fragment of connectedness needed after an envelope
crossing is absorbed. -/
def ConnectedComponentSuffixLinked
    {α : Type} (front suffix : List α) : Prop :=
  ∀ left right,
    suffix = left ++ right →
      right ≠ [] →
        ConnectedComponentSupportsIntersect (front ++ left) right

theorem connectedComponentSuffixLinked_of_connected
    {α : Type} {letters front suffix : List α}
    (connected : ConnectedComponentSupportConnected letters)
    (shape : letters = front ++ suffix)
    (frontNonempty : front ≠ []) :
    ConnectedComponentSuffixLinked front suffix := by
  intro left right suffixShape rightNonempty
  apply connected (front ++ left) right
  · rw [shape, suffixShape, List.append_assoc]
  · intro empty
    have frontEmpty : front = [] := by
      have lengths := congrArg List.length empty
      simp only [List.length_append, List.length_nil] at lengths
      exact List.eq_nil_of_length_eq_zero (by omega)
    exact frontNonempty frontEmpty
  · exact rightNonempty

/-- The induction state after choosing an endpoint. All cuts in the
unprocessed suffix remain linked to the current endpoint envelope. -/
structure ConnectedComponentEnvelopeState
    (endpoint : Nat) (interior suffix : List Nat) : Prop where
  linked :
    ConnectedComponentSuffixLinked
      (endpoint :: interior ++ [endpoint]) suffix

/-- A nonempty linked suffix contains either the endpoint or a letter already
present in the interior. -/
theorem ConnectedComponentEnvelopeState.exists_crossing
    {endpoint : Nat} {interior suffix : List Nat}
    (state :
      ConnectedComponentEnvelopeState endpoint interior suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ letter,
      (letter = endpoint ∨ letter ∈ interior) ∧ letter ∈ suffix := by
  have intersect :=
    state.linked [] suffix (by simp) suffixNonempty
  rcases intersect with ⟨letter, prefixMember, suffixMember⟩
  have prefixMember' :
      letter ∈ endpoint :: interior ++ [endpoint] := by
    simpa using prefixMember
  have endpointOrInterior :
      letter = endpoint ∨ letter ∈ interior := by
    rcases List.mem_append.mp prefixMember' with
      headOrInterior | endpointMember
    · rcases List.mem_cons.mp headOrInterior with equals | interiorMember
      · exact Or.inl equals
      · exact Or.inr interiorMember
    · have equals : letter = endpoint := by
        simpa using endpointMember
      exact Or.inl equals
  exact ⟨letter, endpointOrInterior, suffixMember⟩

private theorem connectedComponent_peel_prefix_mem
    {endpoint letter value : Nat}
    {interior before left : List Nat}
    (member :
      value ∈
        (endpoint :: interior ++ [endpoint]) ++
          before ++ letter :: left) :
    value ∈
      (endpoint ::
          (letter :: interior.erase letter ++ before) ++ [endpoint]) ++
        left := by
  by_cases valueEq : value = letter
  · subst value
    simp
  · have eraseIff :
        value ∈ interior.erase letter ↔ value ∈ interior :=
      List.mem_erase_of_ne valueEq
    simpa [List.mem_append, valueEq, eraseIff,
      or_comm, or_left_comm, or_assoc] using member

/-- Absorb a crossing occurrence from the suffix into the envelope. The new
prefix has the same support as the old prefix through that occurrence, so all
later suffix cuts remain linked. -/
theorem ConnectedComponentEnvelopeState.peelInterior
    {endpoint letter : Nat} {interior suffix before after : List Nat}
    (state :
      ConnectedComponentEnvelopeState endpoint interior suffix)
    (_letterInInterior : letter ∈ interior)
    (suffixShape : suffix = before ++ letter :: after) :
    ConnectedComponentEnvelopeState endpoint
      (letter :: interior.erase letter ++ before) after := by
  refine { linked := ?_ }
  intro left right afterShape rightNonempty
  have oldSuffixShape :
      suffix =
        (before ++ letter :: left) ++ right := by
    rw [suffixShape, afterShape]
    simp [List.append_assoc]
  have oldIntersect :=
    state.linked (before ++ letter :: left) right
      oldSuffixShape rightNonempty
  rcases oldIntersect with
    ⟨value, oldPrefixMember, rightMember⟩
  exact
    ⟨value,
      connectedComponent_peel_prefix_mem
        (by simpa [List.append_assoc] using oldPrefixMember),
      rightMember⟩

/-- Absorb another occurrence of the endpoint itself. -/
theorem ConnectedComponentEnvelopeState.peelEndpoint
    {endpoint : Nat} {interior suffix before after : List Nat}
    (state :
      ConnectedComponentEnvelopeState endpoint interior suffix)
    (suffixShape : suffix = before ++ endpoint :: after) :
    ConnectedComponentEnvelopeState endpoint
      (interior ++ before) after := by
  refine { linked := ?_ }
  intro left right afterShape rightNonempty
  have oldSuffixShape :
      suffix =
        (before ++ endpoint :: left) ++ right := by
    rw [suffixShape, afterShape]
    simp [List.append_assoc]
  have oldIntersect :=
    state.linked (before ++ endpoint :: left) right
      oldSuffixShape rightNonempty
  rcases oldIntersect with
    ⟨value, oldPrefixMember, rightMember⟩
  refine ⟨value, ?_, rightMember⟩
  simpa [List.mem_append, List.mem_cons, List.mem_singleton,
    or_assoc, or_left_comm, or_comm] using oldPrefixMember

theorem connectedComponent_peel_suffix_length_lt
    {letter : Nat} {suffix before after : List Nat}
    (shape : suffix = before ++ letter :: after) :
    after.length < suffix.length := by
  rw [shape]
  simp
  omega

/-- A finite plan for absorbing every crossing occurrence from the suffix
into the endpoint envelope. Each step is justified by a letter already in the
interior and removes a nonempty prefix ending at its next occurrence. -/
inductive ConnectedComponentEnvelopePlan
    (endpoint : Nat) : List Nat → List Nat → List Nat → Prop
  | done (interior : List Nat) :
      ConnectedComponentEnvelopePlan endpoint interior [] interior
  | interior
      {interior suffix before after finalInterior : List Nat}
      {letter : Nat} :
      letter ∈ interior →
      suffix = before ++ letter :: after →
      ConnectedComponentEnvelopePlan endpoint
        (letter :: interior.erase letter ++ before)
        after finalInterior →
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior
  | endpoint
      {interior suffix before after finalInterior : List Nat} :
      suffix = before ++ endpoint :: after →
      ConnectedComponentEnvelopePlan endpoint
        (interior ++ before) after finalInterior →
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior

/-- Render an endpoint envelope together with its unprocessed suffix. -/
def connectedComponentEnvelopeRender
    (endpoint : Nat) (interior suffix : List Nat) : List Nat :=
  endpoint :: (interior ++ endpoint :: suffix)

/-- Replay an absorption plan in any transitive relation that can permute an
envelope interior and absorb one crossing occurrence. The concrete
`S4_70` list derivability relation supplies these two operations. -/
theorem ConnectedComponentEnvelopePlan.replay
    (relation : List Nat → List Nat → Prop)
    (relationRefl :
      ∀ letters, relation letters letters)
    (relationTrans :
      ∀ {left middle right},
        relation left middle →
          relation middle right →
            relation left right)
    (interiorPermutation :
      ∀ (endpoint : Nat) (suffix : List Nat)
        {left right : List Nat},
        left.Perm right →
          relation
            (connectedComponentEnvelopeRender endpoint left suffix)
            (connectedComponentEnvelopeRender endpoint right suffix))
    (crossingAbsorption :
      ∀ (endpoint letter : Nat)
        (middle before after : List Nat),
        relation
          (connectedComponentEnvelopeRender endpoint
            (letter :: middle) (before ++ letter :: after))
          (connectedComponentEnvelopeRender endpoint
            (letter :: middle ++ before) after))
    (endpointAbsorption :
      ∀ (endpoint : Nat) (interior before after : List Nat),
        relation
          (connectedComponentEnvelopeRender endpoint
            interior (before ++ endpoint :: after))
          (connectedComponentEnvelopeRender endpoint
            (interior ++ before) after))
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior) :
    relation
      (connectedComponentEnvelopeRender endpoint interior suffix)
      (connectedComponentEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact relationRefl _
  | @interior interior suffix before after finalInterior letter
      letterInInterior suffixShape _ ih =>
      subst suffix
      have arrange :
          interior.Perm (letter :: interior.erase letter) :=
        List.perm_cons_erase letterInInterior
      have first :=
        interiorPermutation endpoint
          (before ++ letter :: after) arrange
      have second :=
        crossingAbsorption endpoint letter
          (interior.erase letter) before after
      exact relationTrans first (relationTrans second ih)
  | @endpoint interior suffix before after finalInterior
      suffixShape _ ih =>
      subst suffix
      exact relationTrans
        (endpointAbsorption endpoint interior before after) ih

/-- Absorption preserves exactly the support of the endpoint envelope and
the unprocessed suffix. -/
theorem ConnectedComponentEnvelopePlan.support_iff
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior)
    (tested : Nat) :
    (tested = endpoint ∨ tested ∈ finalInterior) ↔
      (tested = endpoint ∨ tested ∈ interior ∨ tested ∈ suffix) := by
  induction plan with
  | done current =>
      simp
  | @interior interior suffix before after finalInterior letter
      letterInInterior suffixShape _ ih =>
      rw [ih, suffixShape]
      have arrange :
          interior.Perm (letter :: interior.erase letter) :=
        List.perm_cons_erase letterInInterior
      have sameInterior :
          tested ∈ letter :: interior.erase letter ↔
            tested ∈ interior :=
        arrange.mem_iff.symm
      simp only [List.mem_cons, List.mem_append] at sameInterior ⊢
      rw [sameInterior]
      by_cases testedEq : tested = letter
      · subst tested
        simp [letterInInterior]
      · simp [testedEq, or_assoc]
  | @endpoint interior suffix before after finalInterior
      suffixShape _ ih =>
      rw [ih, suffixShape]
      simp only [List.mem_cons, List.mem_append]
      simp [or_assoc, or_left_comm]

/-- The linked-suffix invariant always yields a terminating absorption plan. -/
theorem ConnectedComponentEnvelopeState.exists_plan
    {endpoint : Nat} :
    ∀ (interior suffix : List Nat),
      ConnectedComponentEnvelopeState endpoint interior suffix →
        ∃ finalInterior,
          ConnectedComponentEnvelopePlan endpoint
            interior suffix finalInterior := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, .done interior⟩
  · rcases state.exists_crossing suffixEmpty with
      ⟨letter, endpointOrInterior, letterInSuffix⟩
    rcases List.append_of_mem letterInSuffix with
      ⟨before, after, suffixShape⟩
    rcases endpointOrInterior with rfl | letterInInterior
    · have nextState :=
        state.peelEndpoint suffixShape
      rcases
          ConnectedComponentEnvelopeState.exists_plan
            (interior ++ before) after nextState with
        ⟨finalInterior, plan⟩
      exact
        ⟨finalInterior,
          .endpoint suffixShape plan⟩
    · have nextState :=
        state.peelInterior letterInInterior suffixShape
      rcases
          ConnectedComponentEnvelopeState.exists_plan
            (letter :: interior.erase letter ++ before)
            after nextState with
        ⟨finalInterior, plan⟩
      exact
        ⟨finalInterior,
          .interior letterInInterior suffixShape plan⟩
termination_by interior suffix _state => suffix.length

private theorem connectedComponent_peel_mem_iff
    {letter value : Nat} {interior before after : List Nat}
    (letterInInterior : letter ∈ interior) :
    value ∈
        (letter :: interior.erase letter ++ before) ++ after ↔
      value ∈ interior ∨ value ∈ before ++ letter :: after := by
  by_cases valueEq : value = letter
  · subst value
    simp [letterInInterior]
  · have eraseIff :
        value ∈ interior.erase letter ↔ value ∈ interior :=
      List.mem_erase_of_ne valueEq
    simp [List.mem_append, valueEq, eraseIff]

/-- Every connected two-limited list of length at least two admits a first
endpoint envelope and a linked suffix state. -/
theorem connectedComponent_exists_initial_envelope
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ interior suffix,
      head :: tail =
        head :: interior ++ head :: suffix ∧
      ConnectedComponentEnvelopeState head interior suffix := by
  have tailNonempty : tail ≠ [] := by
    intro empty
    subst tail
    simp at lengthAtLeastTwo
  have headInTail :=
    connectedComponentSupportConnected_cons_tail connected tailNonempty
  rcases List.append_of_mem headInTail with
    ⟨interior, suffix, tailShape⟩
  have wholeShape :
      head :: tail =
        (head :: interior ++ [head]) ++ suffix := by
    rw [tailShape]
    simp [List.append_assoc]
  have linked :
      ConnectedComponentSuffixLinked
        (head :: interior ++ [head]) suffix :=
    connectedComponentSuffixLinked_of_connected
      connected wholeShape (by simp)
  refine ⟨interior, suffix, ?_, ?_⟩
  · rw [tailShape]
    simp
  · exact
      { linked := linked }

end SemigroupBasis.Examples
