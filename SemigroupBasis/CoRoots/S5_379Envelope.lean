import SemigroupBasis.CoRoots.S5_379MultiplicityCap
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_379

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## A multiplicity-preserving envelope plan -/

/-- Render a current endpoint envelope and its unprocessed suffix. -/
def multiplicityEnvelopeRender
    (endpoint : Nat) (interior suffix : List Nat) : List Nat :=
  endpoint :: (interior ++ endpoint :: suffix)

/-- The suffix remains support-linked to the current envelope. Unlike the
`S4_70` plan, crossing absorption will retain two copies of the crossing
letter. -/
structure MultiplicityEnvelopeState
    (endpoint : Nat) (interior suffix : List Nat) : Prop where
  linked :
    ConnectedComponentSuffixLinked
      (endpoint :: interior ++ [endpoint]) suffix

private def MultiplicityEnvelopeState.supportState
    {endpoint : Nat} {interior suffix : List Nat}
    (state : MultiplicityEnvelopeState endpoint interior suffix) :
    ConnectedComponentEnvelopeState endpoint interior suffix :=
  ⟨state.linked⟩

theorem MultiplicityEnvelopeState.exists_crossing
    {endpoint : Nat} {interior suffix : List Nat}
    (state : MultiplicityEnvelopeState endpoint interior suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ letter,
      (letter = endpoint ∨ letter ∈ interior) ∧ letter ∈ suffix :=
  state.supportState.exists_crossing suffixNonempty

theorem MultiplicityEnvelopeState.peelInterior
    {endpoint letter : Nat} {interior suffix before after : List Nat}
    (state : MultiplicityEnvelopeState endpoint interior suffix)
    (letterInInterior : letter ∈ interior)
    (suffixShape : suffix = before ++ letter :: after) :
    MultiplicityEnvelopeState endpoint
      (letter :: letter :: interior.erase letter ++ before) after := by
  have base :=
    state.supportState.peelInterior letterInInterior suffixShape
  refine ⟨?_⟩
  intro left right afterShape rightNonempty
  obtain ⟨value, prefixMember, rightMember⟩ :=
    base.linked left right afterShape rightNonempty
  refine ⟨value, ?_, rightMember⟩
  simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
    prefixMember

theorem MultiplicityEnvelopeState.peelEndpoint
    {endpoint : Nat} {interior suffix before after : List Nat}
    (state : MultiplicityEnvelopeState endpoint interior suffix)
    (suffixShape : suffix = before ++ endpoint :: after) :
    MultiplicityEnvelopeState endpoint (interior ++ before) after :=
  ⟨(state.supportState.peelEndpoint suffixShape).linked⟩

/-- A finite absorption plan which duplicates a crossing interior letter
instead of contracting it to a single occurrence. -/
inductive MultiplicityEnvelopePlan
    (endpoint : Nat) : List Nat → List Nat → List Nat → Prop
  | done (interior : List Nat) :
      MultiplicityEnvelopePlan endpoint interior [] interior
  | interior
      {interior suffix before after finalInterior : List Nat}
      {letter : Nat} :
      letter ∈ interior →
      suffix = before ++ letter :: after →
      MultiplicityEnvelopePlan endpoint
        (letter :: letter :: interior.erase letter ++ before)
        after finalInterior →
      MultiplicityEnvelopePlan endpoint interior suffix finalInterior
  | endpoint
      {interior suffix before after finalInterior : List Nat} :
      suffix = before ++ endpoint :: after →
      MultiplicityEnvelopePlan endpoint
        (interior ++ before) after finalInterior →
      MultiplicityEnvelopePlan endpoint interior suffix finalInterior

theorem MultiplicityEnvelopeState.exists_plan
    {endpoint : Nat} :
    ∀ (interior suffix : List Nat),
      MultiplicityEnvelopeState endpoint interior suffix →
        ∃ finalInterior,
          MultiplicityEnvelopePlan endpoint
            interior suffix finalInterior := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, .done interior⟩
  · obtain ⟨letter, endpointOrInterior, letterInSuffix⟩ :=
      state.exists_crossing suffixEmpty
    obtain ⟨before, after, suffixShape⟩ :=
      List.append_of_mem letterInSuffix
    rcases endpointOrInterior with rfl | letterInInterior
    · have nextState := state.peelEndpoint suffixShape
      obtain ⟨finalInterior, plan⟩ :=
        MultiplicityEnvelopeState.exists_plan
          (interior ++ before) after nextState
      exact ⟨finalInterior, .endpoint suffixShape plan⟩
    · have nextState :=
        state.peelInterior letterInInterior suffixShape
      obtain ⟨finalInterior, plan⟩ :=
        MultiplicityEnvelopeState.exists_plan
          (letter :: letter :: interior.erase letter ++ before)
          after nextState
      exact
        ⟨finalInterior,
          .interior letterInInterior suffixShape plan⟩
termination_by interior suffix _state => suffix.length

/-- Replay a multiplicity-preserving plan using only S5_379 derivations. -/
theorem MultiplicityEnvelopePlan.replay
    {endpoint : Nat} {interior suffix finalInterior : List Nat}
    (plan :
      MultiplicityEnvelopePlan endpoint interior suffix finalInterior) :
    ListDerives
      (multiplicityEnvelopeRender endpoint interior suffix)
      (multiplicityEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact S5_107.ListDerives.refl _
  | @interior interior suffix before after finalInterior letter
      letterInInterior suffixShape _ induction =>
      subst suffix
      have arrange :
          interior.Perm (letter :: interior.erase letter) :=
        List.perm_cons_erase letterInInterior
      have first :=
        listDerivesInteriorPermutation endpoint
          (before ++ letter :: after) arrange
      have second :=
        (listDerivesCrossingPreservingMultiplicity endpoint letter
          (interior.erase letter) before).append after
      have firstAligned :
          ListDerives
            (multiplicityEnvelopeRender endpoint interior
              (before ++ letter :: after))
            (multiplicityEnvelopeRender endpoint
              (letter :: interior.erase letter)
              (before ++ letter :: after)) := by
        simpa [multiplicityEnvelopeRender, List.append_assoc] using first
      have secondAligned :
          ListDerives
            (multiplicityEnvelopeRender endpoint
              (letter :: interior.erase letter)
              (before ++ letter :: after))
            (multiplicityEnvelopeRender endpoint
              ((letter :: letter :: interior.erase letter) ++ before)
              after) := by
        simpa [multiplicityEnvelopeRender, List.append_assoc] using second
      exact firstAligned.trans (secondAligned.trans induction)
  | @endpoint interior suffix before after finalInterior
      suffixShape _ induction =>
      subst suffix
      have absorbed :
          ListDerives
            (multiplicityEnvelopeRender endpoint interior
              (before ++ endpoint :: after))
            (multiplicityEnvelopeRender endpoint (interior ++ before)
              after) := by
        simpa [multiplicityEnvelopeRender, List.append_assoc] using
          listDerivesEndpointAbsorption endpoint interior before after
      exact absorbed.trans induction

/-! ## Interior cap and sorting -/

theorem listDerivesRemoveEndpoint
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      ListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint ::
          interior.filter (fun letter => decide (letter ≠ endpoint)) ++
            endpoint :: suffix)
  | [], suffix => S5_107.ListDerives.refl _
  | letter :: rest, suffix => by
      by_cases equal : letter = endpoint
      · subst letter
        have delete :
            ListDerives
              (endpoint :: endpoint :: rest ++ endpoint :: suffix)
              (endpoint :: rest ++ endpoint :: suffix) := by
          simpa [List.append_assoc] using
            (listDerivesDeleteMiddleCore endpoint [] rest).append suffix
        have recurse :=
          listDerivesRemoveEndpoint endpoint rest suffix
        simpa using delete.trans recurse
      · have recurse :=
          listDerivesRemoveEndpoint endpoint rest suffix
        have lifted :=
          listDerivesInteriorCons endpoint letter suffix recurse
        simpa [equal] using lifted

/-- Sort after deleting the endpoint and retaining the first and last copies
of every other repeated letter. -/
def normalizedInterior (endpoint : Nat) (interior : List Nat) : List Nat :=
  (capScan
    (interior.filter (fun letter => decide (letter ≠ endpoint)))).mergeSort
      (fun left right : Nat => decide (left ≤ right))

/-- Direct derivation from any endpoint envelope to its sorted cap-two
interior. -/
theorem listDerivesNormalizeInterior
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (endpoint :: interior ++ endpoint :: suffix)
      (endpoint :: normalizedInterior endpoint interior ++
        endpoint :: suffix) := by
  let filtered :=
    interior.filter (fun letter => decide (letter ≠ endpoint))
  let capped := capScan filtered
  have removed := listDerivesRemoveEndpoint endpoint interior suffix
  have cappedDerivation :
      ListDerives
        (endpoint :: filtered ++ endpoint :: suffix)
        (endpoint :: capped ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      (listDerivesCapScan filtered).context [endpoint]
        (endpoint :: suffix)
  have sortedDerivation :
      ListDerives
        (endpoint :: capped ++ endpoint :: suffix)
        (endpoint ::
          capped.mergeSort
            (fun left right : Nat => decide (left ≤ right)) ++
          endpoint :: suffix) :=
    listDerivesInteriorPermutation endpoint suffix <|
      (List.mergeSort_perm capped
        (fun left right : Nat => decide (left ≤ right))).symm
  simpa [normalizedInterior, filtered, capped] using
    removed.trans (cappedDerivation.trans sortedDerivation)

private theorem count_filter_ne
    (endpoint tested : Nat) :
    ∀ interior : List Nat,
      (interior.filter
        (fun letter => decide (letter ≠ endpoint))).count tested =
      if tested = endpoint then 0 else interior.count tested
  | interior => by
      by_cases equal : tested = endpoint
      · subst tested
        rw [if_pos rfl]
        apply List.count_eq_zero.mpr
        simp
      · rw [if_neg equal]
        exact List.count_filter
          (p := fun letter => decide (letter ≠ endpoint))
          (by simp [equal])

/-- Exact multiplicity of the normalized interior. -/
theorem normalizedInterior_count
    (endpoint tested : Nat) (interior : List Nat) :
    (normalizedInterior endpoint interior).count tested =
      if tested = endpoint then 0 else min (interior.count tested) 2 := by
  let filtered :=
    interior.filter (fun letter => decide (letter ≠ endpoint))
  let capped := capScan filtered
  have sortedCount :
      (capped.mergeSort
          (fun left right : Nat => decide (left ≤ right))).count tested =
        capped.count tested :=
    (List.perm_iff_count.mp
      (List.mergeSort_perm capped
        (fun left right : Nat => decide (left ≤ right)))) tested
  rw [normalizedInterior]
  change
    (capped.mergeSort
        (fun left right : Nat => decide (left ≤ right))).count tested = _
  rw [sortedCount, capScan_count, count_filter_ne]
  split <;> simp_all

theorem normalizedInterior_endpoint_absent
    (endpoint : Nat) (interior : List Nat) :
    endpoint ∉ normalizedInterior endpoint interior := by
  apply List.count_eq_zero.mp
  rw [normalizedInterior_count, if_pos rfl]

theorem normalizedInterior_count_le_two
    (endpoint tested : Nat) (interior : List Nat) :
    (normalizedInterior endpoint interior).count tested ≤ 2 := by
  rw [normalizedInterior_count]
  split <;> omega

theorem normalizedInterior_sorted
    (endpoint : Nat) (interior : List Nat) :
    (normalizedInterior endpoint interior).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ a b c : Nat,
        decide (a ≤ b) = true →
        decide (b ≤ c) = true →
        decide (a ≤ c) = true := by
    intro a b c ab bc
    exact decide_eq_true <|
      Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)
  have total :
      ∀ a b : Nat,
        (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    rcases Nat.le_total a b with ab | ba
    · simp [ab]
    · simp [ba]
  exact
    (List.pairwise_mergeSort transitive total _).imp
      (fun relation => of_decide_eq_true relation)

theorem normalizedEnvelope_twoLimited
    (endpoint : Nat) (interior : List Nat) :
    UniqueSeparatorTwoLimited
      (endpoint :: normalizedInterior endpoint interior ++ [endpoint]) := by
  intro tested
  by_cases equal : tested = endpoint
  · subst tested
    simp only [List.count_append, List.count_cons_self,
      normalizedInterior_count, if_pos, List.count_nil,
      Nat.zero_add, Nat.add_zero]
    omega
  · simpa only [List.count_append,
      List.count_cons_of_ne (Ne.symm equal), List.count_nil,
      Nat.zero_add, Nat.add_zero] using
        normalizedInterior_count_le_two endpoint tested interior

/-! ## Connected-component normalization boundary -/

/-- Every non-unary support-connected component derives to an endpoint
envelope whose interior is sorted and whose total multiplicity of every
letter is exactly the source multiplicity capped at two. -/
theorem existsConnectedComponentEnvelopeNormal
    (head next : Nat) (rest : List Nat)
    (connected :
      ConnectedComponentSupportConnected (head :: next :: rest)) :
    ∃ interior,
      ListDerives
        (head :: next :: rest)
        (head :: interior ++ [head]) ∧
      head ∉ interior ∧
      interior.Pairwise (· ≤ ·) ∧
      UniqueSeparatorTwoLimited (head :: interior ++ [head]) ∧
      (∀ tested,
        (head :: interior ++ [head]).count tested =
          min ((head :: next :: rest).count tested) 2) := by
  obtain ⟨initialInterior, suffix, initialShape, supportState⟩ :=
    connectedComponent_exists_initial_envelope connected (by simp)
  let state : MultiplicityEnvelopeState head initialInterior suffix :=
    ⟨supportState.linked⟩
  obtain ⟨finalInterior, plan⟩ := state.exists_plan
  have absorbed :
      ListDerives
        (head :: next :: rest)
        (multiplicityEnvelopeRender head finalInterior []) := by
    rw [initialShape]
    simpa [multiplicityEnvelopeRender, List.append_assoc] using plan.replay
  have normalized :=
    listDerivesNormalizeInterior head finalInterior []
  have combined :
      ListDerives
        (head :: next :: rest)
        (head :: normalizedInterior head finalInterior ++ [head]) := by
    exact absorbed.trans <| by
      simpa [multiplicityEnvelopeRender, List.append_assoc] using normalized
  let interior := normalizedInterior head finalInterior
  have limited :
      UniqueSeparatorTwoLimited (head :: interior ++ [head]) :=
    normalizedEnvelope_twoLimited head finalInterior
  refine
    ⟨interior, combined,
      normalizedInterior_endpoint_absent head finalInterior,
      normalizedInterior_sorted head finalInterior,
      limited, ?_⟩
  intro tested
  have capped :=
    listDerives_cappedCount_eq combined (by simp) (by simp) tested
  have targetBound := limited tested
  calc
    (head :: interior ++ [head]).count tested =
        min ((head :: interior ++ [head]).count tested) 2 :=
      (Nat.min_eq_left targetBound).symm
    _ = min ((head :: next :: rest).count tested) 2 := capped.symm

/-- Unary components are already normalized; non-unary components use the
multiplicity-preserving envelope theorem above. -/
theorem existsConnectedComponentNormal
    {component : List Nat} (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ∃ target,
      ListDerives component target ∧
      UniqueSeparatorTwoLimited target ∧
      (∀ tested,
        target.count tested = min (component.count tested) 2) ∧
      (target.length = 1 ∨
        ∃ endpoint interior,
          target = endpoint :: interior ++ [endpoint] ∧
          endpoint ∉ interior ∧
          interior.Pairwise (· ≤ ·)) := by
  cases component with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          refine ⟨[head], S5_107.ListDerives.refl _, ?_, ?_, Or.inl ?_⟩
          · intro tested
            by_cases equal : tested = head
            · subst tested
              rw [List.count_cons_self, List.count_nil]
              omega
            · rw [List.count_cons_of_ne (Ne.symm equal), List.count_nil]
              omega
          · intro tested
            by_cases equal : tested = head
            · subst tested
              rw [List.count_cons_self, List.count_nil]
              omega
            · rw [List.count_cons_of_ne (Ne.symm equal), List.count_nil]
              omega
          · simp
      | cons next rest =>
          obtain
            ⟨interior, derivation, endpointAbsent, sorted,
              limited, capped⟩ :=
            existsConnectedComponentEnvelopeNormal head next rest connected
          exact
            ⟨head :: interior ++ [head], derivation, limited, capped,
              Or.inr ⟨head, interior, rfl, endpointAbsent, sorted⟩⟩

end SemigroupBasis.CoRoots.S5_379
