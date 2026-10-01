import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- Render a fixed-endpoint envelope together with its unprocessed suffix. -/
def parityEnvelopeRender
    (endpoint : Nat) (interior suffix : List Nat) : List Nat :=
  endpoint :: (interior ++ endpoint :: suffix)

/-- The suffix remains linked to the support already enclosed by the two
displayed endpoint occurrences. -/
structure ParityEnvelopeState
    (endpoint : Nat) (interior suffix : List Nat) : Prop where
  linked :
    ConnectedComponentSuffixLinked
      (endpoint :: interior ++ [endpoint]) suffix

/-- One parity-preserving absorption step.

For an interior crossing, an interior permutation first displays one retained
copy of `crossing`. The suffix copy is then moved into the interior as a second
retained copy, followed by the passed block. For an endpoint crossing, the
later endpoint is moved into the interior. Neither constructor deletes an
occurrence. -/
inductive ParityEnvelopeStep (endpoint : Nat) :
    List Nat → List Nat → List Nat → List Nat → Prop
  | crossing
      {interior middle before after : List Nat}
      {crossing : Nat}
      (arrange : interior.Perm (crossing :: middle)) :
      ParityEnvelopeStep endpoint
        interior (before ++ crossing :: after)
        (crossing :: crossing :: (middle ++ before)) after
  | endpoint
      {interior before after : List Nat} :
      ParityEnvelopeStep endpoint
        interior (before ++ endpoint :: after)
        (interior ++ before ++ [endpoint]) after

private theorem parityEnvelope_crossing_prefix_mem
    {endpoint crossing value : Nat}
    {interior middle before left : List Nat}
    (arrange : interior.Perm (crossing :: middle))
    (member :
      value ∈
        (endpoint :: interior ++ [endpoint]) ++
          (before ++ crossing :: left)) :
    value ∈
      (endpoint ::
          (crossing :: crossing :: (middle ++ before)) ++
            [endpoint]) ++ left := by
  have interiorMembership :
      value ∈ interior ↔ value ∈ crossing :: middle :=
    arrange.mem_iff
  simpa [List.mem_append, interiorMembership,
    or_assoc, or_left_comm, or_comm] using member

private theorem parityEnvelope_endpoint_prefix_mem
    {endpoint value : Nat}
    {interior before left : List Nat}
    (member :
      value ∈
        (endpoint :: interior ++ [endpoint]) ++
          (before ++ endpoint :: left)) :
    value ∈
      (endpoint ::
          (interior ++ before ++ [endpoint]) ++
            [endpoint]) ++ left := by
  simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
    member

namespace ParityEnvelopeState

/-- A nonempty linked suffix contains either the endpoint or a letter already
present in the current interior. -/
theorem exists_absorbable
    {endpoint : Nat} {interior suffix : List Nat}
    (state : ParityEnvelopeState endpoint interior suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ letter,
      (letter = endpoint ∨ letter ∈ interior) ∧
        letter ∈ suffix := by
  have intersect :=
    state.linked [] suffix (by simp) suffixNonempty
  rcases intersect with
    ⟨letter, prefixMember, suffixMember⟩
  have prefixMember' :
      letter ∈ endpoint :: interior ++ [endpoint] := by
    simpa using prefixMember
  have endpointOrInterior :
      letter = endpoint ∨ letter ∈ interior := by
    rcases List.mem_append.mp prefixMember' with
      headOrInterior | endpointMember
    · rcases List.mem_cons.mp headOrInterior with
        equals | interiorMember
      · exact Or.inl equals
      · exact Or.inr interiorMember
    · have equals : letter = endpoint := by
        simpa using endpointMember
      exact Or.inl equals
  exact ⟨letter, endpointOrInterior, suffixMember⟩

/-- Retaining both crossing copies preserves the linked-suffix invariant. -/
theorem absorbCrossing
    {endpoint crossing : Nat}
    {interior middle before after : List Nat}
    (state :
      ParityEnvelopeState endpoint interior
        (before ++ crossing :: after))
    (arrange : interior.Perm (crossing :: middle)) :
    ParityEnvelopeState endpoint
      (crossing :: crossing :: (middle ++ before)) after := by
  refine { linked := ?_ }
  intro left right afterShape rightNonempty
  have oldSuffixShape :
      before ++ crossing :: after =
        (before ++ crossing :: left) ++ right := by
    rw [afterShape]
    simp [List.append_assoc]
  have oldIntersect :=
    state.linked (before ++ crossing :: left) right
      oldSuffixShape rightNonempty
  rcases oldIntersect with
    ⟨value, oldPrefixMember, rightMember⟩
  exact
    ⟨value,
      parityEnvelope_crossing_prefix_mem
        arrange oldPrefixMember,
      rightMember⟩

/-- Retaining a later endpoint inside the interior preserves linkedness. -/
theorem absorbEndpoint
    {endpoint : Nat} {interior before after : List Nat}
    (state :
      ParityEnvelopeState endpoint interior
        (before ++ endpoint :: after)) :
    ParityEnvelopeState endpoint
      (interior ++ before ++ [endpoint]) after := by
  refine { linked := ?_ }
  intro left right afterShape rightNonempty
  have oldSuffixShape :
      before ++ endpoint :: after =
        (before ++ endpoint :: left) ++ right := by
    rw [afterShape]
    simp [List.append_assoc]
  have oldIntersect :=
    state.linked (before ++ endpoint :: left) right
      oldSuffixShape rightNonempty
  rcases oldIntersect with
    ⟨value, oldPrefixMember, rightMember⟩
  exact
    ⟨value,
      parityEnvelope_endpoint_prefix_mem oldPrefixMember,
      rightMember⟩

end ParityEnvelopeState

namespace ParityEnvelopeStep

/-- Every transition preserves the linked-suffix state. -/
theorem preserves_state
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix)
    (state : ParityEnvelopeState endpoint interior suffix) :
    ParityEnvelopeState endpoint nextInterior nextSuffix := by
  cases step with
  | crossing arrange =>
      exact state.absorbCrossing arrange
  | endpoint =>
      exact state.absorbEndpoint

/-- A transition strictly shortens the unprocessed suffix. -/
theorem suffix_length_lt
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    nextSuffix.length < suffix.length := by
  cases step <;> simp <;> omega

/-- Each transition preserves every rendered occurrence count exactly. -/
theorem render_count_eq
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix)
    (tested : Nat) :
    (parityEnvelopeRender endpoint interior suffix).count tested =
      (parityEnvelopeRender endpoint
        nextInterior nextSuffix).count tested := by
  cases step with
  | crossing arrange =>
      have interiorCount :=
        (List.perm_iff_count.mp arrange) tested
      simp only [parityEnvelopeRender, List.count_cons,
        List.count_append, List.count_nil] at interiorCount ⊢
      omega
  | endpoint =>
      simp only [parityEnvelopeRender, List.count_cons,
        List.count_append, List.count_nil]
      omega

/-- The rendered words before and after a transition are the same multiset. -/
theorem render_perm
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    (parityEnvelopeRender endpoint interior suffix).Perm
      (parityEnvelopeRender endpoint nextInterior nextSuffix) := by
  rw [List.perm_iff_count]
  exact step.render_count_eq

/-- Transition support preservation, independent of any derivation replay. -/
theorem render_mem_iff
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix)
    (tested : Nat) :
    tested ∈ parityEnvelopeRender endpoint interior suffix ↔
      tested ∈
        parityEnvelopeRender endpoint nextInterior nextSuffix :=
  step.render_perm.mem_iff

/-- Exact count preservation implies coordinatewise parity preservation. -/
theorem render_count_mod_two_eq
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix)
    (tested : Nat) :
    (parityEnvelopeRender endpoint interior suffix).count tested % 2 =
      (parityEnvelopeRender endpoint
        nextInterior nextSuffix).count tested % 2 :=
  congrArg (fun count => count % 2) (step.render_count_eq tested)

end ParityEnvelopeStep

/-- A finite sequence of parity-preserving absorptions ending with an empty
suffix. -/
inductive ParityEnvelopePlan
    (endpoint : Nat) : List Nat → List Nat → List Nat → Prop
  | done (interior : List Nat) :
      ParityEnvelopePlan endpoint interior [] interior
  | advance
      {interior suffix nextInterior nextSuffix finalInterior : List Nat}
      (step :
        ParityEnvelopeStep endpoint
          interior suffix nextInterior nextSuffix)
      (remaining :
        ParityEnvelopePlan endpoint
          nextInterior nextSuffix finalInterior) :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior

namespace ParityEnvelopePlan

/-- A complete plan preserves the rendered multiset exactly. -/
theorem render_perm
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    (parityEnvelopeRender endpoint interior suffix).Perm
      (parityEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact List.Perm.refl _
  | advance step remaining ih =>
      exact step.render_perm.trans ih

/-- A complete plan preserves every occurrence count exactly. -/
theorem render_count_eq
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior)
    (tested : Nat) :
    (parityEnvelopeRender endpoint interior suffix).count tested =
      (parityEnvelopeRender endpoint finalInterior []).count tested :=
  List.perm_iff_count.mp plan.render_perm tested

/-- A complete plan preserves rendered support. -/
theorem render_mem_iff
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior)
    (tested : Nat) :
    tested ∈ parityEnvelopeRender endpoint interior suffix ↔
      tested ∈ parityEnvelopeRender endpoint finalInterior [] :=
  plan.render_perm.mem_iff

/-- A complete plan preserves coordinatewise occurrence parity. -/
theorem render_count_mod_two_eq
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior)
    (tested : Nat) :
    (parityEnvelopeRender endpoint interior suffix).count tested % 2 =
      (parityEnvelopeRender endpoint
        finalInterior []).count tested % 2 :=
  congrArg (fun count => count % 2) (plan.render_count_eq tested)

/-- The final envelope contains exactly the support of the initial endpoint,
interior, and suffix. -/
theorem support_iff
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ParityEnvelopePlan endpoint
        interior suffix finalInterior)
    (tested : Nat) :
    (tested = endpoint ∨ tested ∈ finalInterior) ↔
      (tested = endpoint ∨
        tested ∈ interior ∨ tested ∈ suffix) := by
  have renderedMembership :
      tested ∈ parityEnvelopeRender endpoint finalInterior [] ↔
        tested ∈ parityEnvelopeRender endpoint interior suffix :=
    (plan.render_mem_iff tested).symm
  simpa [parityEnvelopeRender, List.mem_append,
    or_assoc, or_left_comm, or_comm] using renderedMembership

end ParityEnvelopePlan

namespace ParityEnvelopeState

/-- The linked-state invariant supplies a concrete next transition whenever
the suffix is nonempty. The returned strict inequality is the termination
measure used by `exists_plan`. -/
theorem exists_step
    {endpoint : Nat} {interior suffix : List Nat}
    (state : ParityEnvelopeState endpoint interior suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ nextInterior nextSuffix,
      ParityEnvelopeStep endpoint
          interior suffix nextInterior nextSuffix ∧
        ParityEnvelopeState endpoint nextInterior nextSuffix ∧
        nextSuffix.length < suffix.length := by
  rcases state.exists_absorbable suffixNonempty with
    ⟨letter, endpointOrInterior, letterInSuffix⟩
  rcases List.append_of_mem letterInSuffix with
    ⟨before, after, suffixShape⟩
  rcases endpointOrInterior with endpointEq | letterInInterior
  · subst letter
    subst suffix
    have step :
        ParityEnvelopeStep endpoint
          interior (before ++ endpoint :: after)
          (interior ++ before ++ [endpoint]) after :=
      .endpoint
    exact
      ⟨interior ++ before ++ [endpoint], after,
        step, step.preserves_state state,
        step.suffix_length_lt⟩
  · subst suffix
    have arrange :
        interior.Perm (letter :: interior.erase letter) :=
      List.perm_cons_erase letterInInterior
    have step :
        ParityEnvelopeStep endpoint
          interior (before ++ letter :: after)
          (letter :: letter ::
            (interior.erase letter ++ before)) after :=
      .crossing arrange
    exact
      ⟨letter :: letter :: (interior.erase letter ++ before),
        after, step, step.preserves_state state,
        step.suffix_length_lt⟩

/-- Every linked suffix admits a terminating parity-preserving absorption
plan. Recursive calls strictly decrease the suffix length. -/
theorem exists_plan
    {endpoint : Nat} :
    ∀ (interior suffix : List Nat),
      ParityEnvelopeState endpoint interior suffix →
        ∃ finalInterior,
          ParityEnvelopePlan endpoint
            interior suffix finalInterior := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, .done interior⟩
  · obtain
      ⟨nextInterior, nextSuffix, step, nextState, suffixShorter⟩ :=
        state.exists_step suffixEmpty
    obtain ⟨finalInterior, remaining⟩ :=
      ParityEnvelopeState.exists_plan
        nextInterior nextSuffix nextState
    exact
      ⟨finalInterior, .advance step remaining⟩
termination_by interior suffix _state => suffix.length
decreasing_by exact suffixShorter

end ParityEnvelopeState

/-- Every support-connected list of length at least two has an initial
parity-envelope state at its first letter. -/
theorem exists_initialParityEnvelopeState
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ interior suffix,
      head :: tail =
        parityEnvelopeRender head interior suffix ∧
      ParityEnvelopeState head interior suffix := by
  obtain ⟨interior, suffix, shape, state⟩ :=
    connectedComponent_exists_initial_envelope
      connected lengthAtLeastTwo
  refine ⟨interior, suffix, ?_, ?_⟩
  · simpa [parityEnvelopeRender] using shape
  · exact ⟨state.linked⟩

/-- A support-connected source therefore admits a complete parity-preserving
envelope plan. Exact-cut-freeness alone is not used: linkedness is the
structural hypothesis needed to guarantee a crossing at every suffix cut. -/
theorem exists_parityEnvelopePlan_of_connected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ interior suffix finalInterior,
      head :: tail =
          parityEnvelopeRender head interior suffix ∧
        ParityEnvelopeState head interior suffix ∧
        ParityEnvelopePlan head
          interior suffix finalInterior := by
  obtain ⟨interior, suffix, shape, state⟩ :=
    exists_initialParityEnvelopeState
      connected lengthAtLeastTwo
  obtain ⟨finalInterior, plan⟩ :=
    state.exists_plan
  exact
    ⟨interior, suffix, finalInterior,
      shape, state, plan⟩

end SemigroupBasis.CoRoots.S5_441
