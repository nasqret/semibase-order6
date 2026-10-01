import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058ParityEnvelopePrimitives
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeInteriorNormalize

/-!
# Rank-058 owner-only parity-preserving connected-component replay

The abstract `S5_441.ParityEnvelopePlan` is purely list combinatorics.  Every
derivation below is nevertheless in the actual frozen eleven-law rank-058
basis.  In particular, no `S5_441`, `S5_442`, or `S5_804` derivation is
transported into the owner basis.

The two generic plan steps are rebuilt using the independently kernel-green
owner interior permutation and alternating-span theorem.  The interior
normalizer lifts only the harmless `x = xxx` and `xy = yx` commutative-parity
laws inside a closed owner envelope.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityComponentReplay

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank058.basis

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private abbrev render :=
  SemigroupBasis.CoRoots.S5_441.parityEnvelopeRender

private theorem moveOccurrenceToEnd_perm
    (before after : List Nat) (letter : Nat) :
    (before ++ letter :: after).Perm
      (before ++ after ++ [letter]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

/-- A later endpoint can be retained; no occurrence is deleted or created. -/
theorem listDerivesRetainedEndpoint
    (endpoint : Nat) (interior before after : List Nat) :
    ListDerives
      (render endpoint interior (before ++ endpoint :: after))
      (render endpoint (interior ++ before ++ [endpoint]) after) := by
  have permutation := moveOccurrenceToEnd_perm interior before endpoint
  have derived :=
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint after permutation
  simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using derived

/-- Retain BOTH crossing occurrences and absorb all passed support. -/
theorem listDerivesRetainedCrossing
    (endpoint crossing : Nat) (middle before after : List Nat) :
    ListDerives
      (render endpoint (crossing :: middle)
        (before ++ crossing :: after))
      (render endpoint
        (crossing :: crossing :: middle ++ before) after) := by
  have permutation := moveOccurrenceToEnd_perm middle before endpoint
  have rotate :=
    ParityEnvelope.listDerivesInteriorPermutation
      crossing after permutation
  have first :
      ListDerives
        (render endpoint (crossing :: middle)
          (before ++ crossing :: after))
        (endpoint :: crossing :: middle ++ before ++
          endpoint :: crossing :: after) := by
    simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using
      rotate.prepend [endpoint]
  have attach :=
    ParityEnvelope.listDerivesProtectedInteriorSpanExtension
      endpoint crossing (middle ++ before) after
  have second :
      ListDerives
        (endpoint :: crossing :: middle ++ before ++
          endpoint :: crossing :: after)
        (render endpoint
          (crossing :: crossing :: middle ++ before) after) := by
    simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using attach
  exact first.trans second

/-- Replay one PURE COMBINATORIAL step using only owner-basis derivations. -/
private theorem replayCrossing
    {endpoint crossing : Nat}
    {interior middle before after : List Nat}
    (arrange : interior.Perm (crossing :: middle)) :
    ListDerives
      (render endpoint interior (before ++ crossing :: after))
      (render endpoint
        (crossing :: crossing :: middle ++ before) after) := by
  have permuted :=
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint (before ++ crossing :: after) arrange
  have first :
      ListDerives
        (render endpoint interior (before ++ crossing :: after))
        (render endpoint (crossing :: middle)
          (before ++ crossing :: after)) := by
    simpa [render, S5_441.parityEnvelopeRender] using permuted
  exact first.trans
    (listDerivesRetainedCrossing endpoint crossing middle before after)

/-- Replay one PURE COMBINATORIAL step using only owner-basis derivations. -/
theorem parityEnvelopeStepReplay
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      S5_441.ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    ListDerives
      (render endpoint interior suffix)
      (render endpoint nextInterior nextSuffix) := by
  cases step with
  | crossing arrange =>
      exact replayCrossing arrange
  | endpoint =>
      exact listDerivesRetainedEndpoint _ _ _ _

/-- Terminating unrestricted suffix induction; every transition retains parity. -/
theorem parityEnvelopePlanReplay
    {endpoint : Nat} {interior suffix finalInterior : List Nat}
    (plan :
      S5_441.ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    ListDerives
      (render endpoint interior suffix)
      (render endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact S5_107.ListDerives.refl _
  | advance step remaining induction =>
      exact (parityEnvelopeStepReplay step).trans induction

/-- Every connected component closes at its ACTUAL FIRST endpoint. -/
theorem existsParityEnvelopeDerivationOfConnected
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
          (head :: tail)
          (render head finalInterior []) ∧
        (head :: tail).Perm (render head finalInterior []) := by
  obtain ⟨interior, suffix, finalInterior, shape, _state, plan⟩ :=
    S5_441.exists_parityEnvelopePlan_of_connected
      connected lengthAtLeastTwo
  refine ⟨finalInterior, ?_, ?_⟩
  · rw [shape]
    exact parityEnvelopePlanReplay plan
  · rw [shape]
    exact S5_441.ParityEnvelopePlan.render_perm plan

/-- Prefix-generalized lift inside a fixed closed endpoint envelope. -/
theorem listDerivesInteriorPrefix
    (endpoint : Nat) (initial suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ListDerives
        (render endpoint left suffix)
        (render endpoint right suffix)) :
    ListDerives
      (render endpoint (initial ++ left) suffix)
      (render endpoint (initial ++ right) suffix) := by
  induction initial with
  | nil =>
      simpa using derivation
  | cons letter remaining induction =>
      have lifted :=
        ParityEnvelope.listDerivesInteriorCons
          endpoint letter suffix induction
      simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using
        lifted

/-- Remove two copies of ANY nonempty block at the end of an envelope. -/
theorem listDerivesInteriorBlockTripleContractionCore
    (endpoint : Nat) (block : Word Nat) (suffix : List Nat) :
    ListDerives
      (render endpoint
        (block.toList ++ block.toList ++ block.toList) suffix)
      (render endpoint block.toList suffix) := by
  have core :=
    ParityEnvelope.derivesInteriorTripleContraction
      (Word.singleton endpoint) block
  simpa [render, S5_441.parityEnvelopeRender, Word.toList_append,
    Word.toList_singleton, List.append_assoc] using
      (S5_107.ListDerives.ofWord core).append suffix

/-- Add TWO arbitrary nonempty interior blocks while preserving any context. -/
theorem listDerivesInteriorBlockTripleExpansionContext
    (endpoint : Nat) (before after suffix : List Nat)
    (block : Word Nat) :
    ListDerives
      (render endpoint (before ++ block.toList ++ after) suffix)
      (render endpoint
        (before ++ block.toList ++ block.toList ++
          block.toList ++ after) suffix) := by
  have moveSingle :
      (before ++ block.toList ++ after).Perm
        (before ++ after ++ block.toList) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have first :=
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint suffix moveSingle
  have expand :=
    listDerivesInteriorPrefix endpoint (before ++ after) suffix
      (listDerivesInteriorBlockTripleContractionCore
        endpoint block suffix).symm
  have moveTriple :
      (before ++ after ++ block.toList ++ block.toList ++ block.toList).Perm
        (before ++ block.toList ++ block.toList ++ block.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have third :=
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint suffix moveTriple
  have firstAligned :
      ListDerives
        (render endpoint (before ++ block.toList ++ after) suffix)
        (render endpoint (before ++ after ++ block.toList) suffix) := by
    simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using first
  have expandAligned :
      ListDerives
        (render endpoint (before ++ after ++ block.toList) suffix)
        (render endpoint
          (before ++ after ++ block.toList ++ block.toList ++ block.toList)
          suffix) := by
    simpa [List.append_assoc] using expand
  have thirdAligned :
      ListDerives
        (render endpoint
          (before ++ after ++ block.toList ++ block.toList ++ block.toList)
          suffix)
        (render endpoint
          (before ++ block.toList ++ block.toList ++ block.toList ++ after)
          suffix) := by
    simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using third
  exact firstAligned.trans (expandAligned.trans thirdAligned)

/-- Swap nonempty arbitrary blocks anywhere inside a fixed owner envelope. -/
theorem listDerivesInteriorBlockSwapContext
    (endpoint : Nat) (before after suffix : List Nat)
    (left right : Word Nat) :
    ListDerives
      (render endpoint
        (before ++ left.toList ++ right.toList ++ after) suffix)
      (render endpoint
        (before ++ right.toList ++ left.toList ++ after) suffix) := by
  have permutation :
      (before ++ left.toList ++ right.toList ++ after).Perm
        (before ++ right.toList ++ left.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  simpa [render, S5_441.parityEnvelopeRender] using
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint suffix permutation

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Lift ONLY the two owner-valid interior parity/swap laws. -/
theorem liftInteriorParity
    {left right : Word Nat}
    (derivation : Derives commutativeParityBasis left right)
    (endpoint : Nat) (before after suffix : List Nat)
    (substitution : Nat → Word Nat) :
    ListDerives
      (render endpoint
        (before ++ (left.bind substitution).toList ++ after) suffix)
      (render endpoint
        (before ++ (right.bind substitution).toList ++ after) suffix) := by
  induction derivation generalizing before after substitution with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX,
          Word.bind, Word.append, Word.singleton,
          render, S5_441.parityEnvelopeRender, List.append_assoc] using
          listDerivesInteriorBlockTripleExpansionContext
            endpoint before after suffix (substitution 0)
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton,
          render, S5_441.parityEnvelopeRender, List.append_assoc] using
          listDerivesInteriorBlockSwapContext
            endpoint before after suffix (substitution 0) (substitution 1)
  | refl =>
      exact S5_107.ListDerives.refl _
  | symm _ induction =>
      exact (induction before after substitution).symm
  | trans _ _ first second =>
      exact
        (first before after substitution).trans
          (second before after substitution)
  | prepend initial _ induction =>
      simpa [bind_append, Word.toList_append, List.append_assoc] using
        induction
          (before ++ (initial.bind substitution).toList)
          after substitution
  | appendRight _ trailing induction =>
      simpa [bind_append, Word.toList_append, List.append_assoc] using
        induction before
          ((trailing.bind substitution).toList ++ after) substitution
  | subst _ replacement induction =>
      simpa [bind_bind] using
        induction before after
          (fun letter => (replacement letter).bind substitution)

/-- Normalize EVERY positive interior multiplicity while retaining its parity. -/
theorem listDerivesPositiveParityReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (render endpoint interior suffix)
      (render endpoint (positiveParityReduce interior) suffix) := by
  cases interior with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head tail =>
      have normalized :=
        positiveParityDerivesNormal (wordOfCons head tail)
      change
        match positiveParityReduce (head :: tail) with
        | [] => False
        | nextHead :: nextTail =>
            Derives commutativeParityBasis
              (wordOfCons head tail) (Word.mk nextHead nextTail)
        at normalized
      cases reduced : positiveParityReduce (head :: tail) with
      | nil =>
          have present : head ∈ positiveParityReduce (head :: tail) :=
            (mem_positiveParityReduce_iff head (head :: tail)).mpr (by simp)
          simp [reduced] at present
      | cons nextHead nextTail =>
          rw [reduced] at normalized
          have lifted :=
            liftInteriorParity normalized endpoint
              [] [] suffix Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          simpa [wordOfCons, Word.toList, reduced] using lifted

/-- Delete exactly TWO internal fixed endpoints, including the empty case. -/
theorem listDerivesRemoveInteriorEndpointPair
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (render endpoint ([endpoint, endpoint] ++ interior) suffix)
      (render endpoint interior suffix) := by
  simpa [render, S5_441.parityEnvelopeRender, List.append_assoc] using
    ParityEnvelope.listDerivesAnchorPrefixPairContraction
      endpoint interior suffix

private theorem twoEndpointCopies_perm
    (endpoint : Nat) (letters : List Nat)
    (countEq : letters.count endpoint = 2) :
    letters.Perm
      (endpoint :: endpoint ::
        (letters.erase endpoint).erase endpoint) := by
  have present : endpoint ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase present
  have eraseCount : (letters.erase endpoint).count endpoint = 1 := by
    rw [List.count_erase_self, countEq]
  have remains : endpoint ∈ letters.erase endpoint :=
    List.count_pos_iff.mp (by omega)
  exact
    first.trans
      (List.Perm.cons endpoint (List.perm_cons_erase remains))

/-- Reduce the anchor to zero/one copies and all others to one/two copies. -/
theorem listDerivesFixedEndpointParityReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (render endpoint interior suffix)
      (render endpoint
        (S5_441.fixedEndpointParityReduce endpoint interior) suffix) := by
  have positive := listDerivesPositiveParityReduce endpoint interior suffix
  by_cases countEq : (positiveParityReduce interior).count endpoint = 2
  · let remainder :=
      ((positiveParityReduce interior).erase endpoint).erase endpoint
    have permutation :
        (positiveParityReduce interior).Perm
          ([endpoint, endpoint] ++ remainder) := by
      simpa [remainder] using
        twoEndpointCopies_perm endpoint
          (positiveParityReduce interior) countEq
    have arrange :=
      ParityEnvelope.listDerivesInteriorPermutation
        endpoint suffix permutation
    have arrange' :
        ListDerives
          (render endpoint (positiveParityReduce interior) suffix)
          (render endpoint ([endpoint, endpoint] ++ remainder) suffix) := by
      simpa [render, S5_441.parityEnvelopeRender] using arrange
    have remove :=
      listDerivesRemoveInteriorEndpointPair endpoint remainder suffix
    exact positive.trans <| by
      simpa [S5_441.fixedEndpointParityReduce, countEq, remainder] using
        arrange'.trans remove
  · simpa [S5_441.fixedEndpointParityReduce, countEq] using positive

/-- Full fixed-anchor owner normalization from support and occurrence parity. -/
theorem listDerivesFixedEndpointNormalize
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (supportEq : ∀ tested, tested ≠ endpoint →
      (tested ∈ left ↔ tested ∈ right))
    (parityEq : ∀ tested,
      left.count tested % 2 = right.count tested % 2) :
    ListDerives
      (render endpoint left suffix)
      (render endpoint right suffix) := by
  have permutation :=
    S5_441.fixedEndpointParityReduce_perm supportEq parityEq
  have first :=
    listDerivesFixedEndpointParityReduce endpoint left suffix
  have second :=
    ParityEnvelope.listDerivesInteriorPermutation
      endpoint suffix permutation
  have second' :
      ListDerives
        (render endpoint
          (S5_441.fixedEndpointParityReduce endpoint left) suffix)
        (render endpoint
          (S5_441.fixedEndpointParityReduce endpoint right) suffix) := by
    simpa [render, S5_441.parityEnvelopeRender] using second
  have third :=
    (listDerivesFixedEndpointParityReduce endpoint right suffix).symm
  exact first.trans (second'.trans third)

private theorem mem_render_iff_of_ne
    (endpoint tested : Nat) (interior : List Nat)
    (different : tested ≠ endpoint) :
    tested ∈ render endpoint interior [] ↔ tested ∈ interior := by
  simp [render, S5_441.parityEnvelopeRender, different]

private theorem render_count_mod_two
    (endpoint tested : Nat) (interior : List Nat) :
    (render endpoint interior []).count tested % 2 =
      interior.count tested % 2 := by
  by_cases equal : endpoint = tested
  · subst tested
    simp [render, S5_441.parityEnvelopeRender]
    omega
  · simp [render, S5_441.parityEnvelopeRender, equal]

/-- Closed-envelope completeness from ACTUAL full support and parity data. -/
theorem listDerivesFixedEndpointNormalizeOfRenderedInvariants
    (endpoint : Nat) {left right : List Nat}
    (supportEq : ∀ tested,
      tested ∈ render endpoint left [] ↔
        tested ∈ render endpoint right [])
    (parityEq : ∀ tested,
      (render endpoint left []).count tested % 2 =
        (render endpoint right []).count tested % 2) :
    ListDerives
      (render endpoint left [])
      (render endpoint right []) := by
  apply listDerivesFixedEndpointNormalize endpoint []
  · intro tested different
    rw [← mem_render_iff_of_ne endpoint tested left different,
      ← mem_render_iff_of_ne endpoint tested right different]
    exact supportEq tested
  · intro tested
    rw [← render_count_mod_two endpoint tested left,
      ← render_count_mod_two endpoint tested right]
    exact parityEq tested

/-- Two nonsingleton connected components with the SAME ACTUAL FIRST letter. -/
theorem listDerivesConnectedComponentsOfSameHeadSupportParity
    {head : Nat} {leftTail rightTail : List Nat}
    (leftConnected : ConnectedComponentSupportConnected (head :: leftTail))
    (rightConnected : ConnectedComponentSupportConnected (head :: rightTail))
    (leftLength : 2 ≤ (head :: leftTail).length)
    (rightLength : 2 ≤ (head :: rightTail).length)
    (sameSupport : ∀ tested,
      tested ∈ head :: leftTail ↔ tested ∈ head :: rightTail)
    (sameParity : ∀ tested,
      (head :: leftTail).count tested % 2 =
        (head :: rightTail).count tested % 2) :
    ListDerives (head :: leftTail) (head :: rightTail) := by
  obtain ⟨leftInterior, leftDerivation, leftPermutation⟩ :=
    existsParityEnvelopeDerivationOfConnected leftConnected leftLength
  obtain ⟨rightInterior, rightDerivation, rightPermutation⟩ :=
    existsParityEnvelopeDerivationOfConnected rightConnected rightLength
  have support : ∀ tested,
      tested ∈ render head leftInterior [] ↔
        tested ∈ render head rightInterior [] := by
    intro tested
    exact leftPermutation.mem_iff.symm.trans
      ((sameSupport tested).trans rightPermutation.mem_iff)
  have parity : ∀ tested,
      (render head leftInterior []).count tested % 2 =
        (render head rightInterior []).count tested % 2 := by
    intro tested
    have leftCount := (List.perm_iff_count.mp leftPermutation) tested
    have rightCount := (List.perm_iff_count.mp rightPermutation) tested
    exact (congrArg (fun count => count % 2) leftCount).symm.trans
      ((sameParity tested).trans
        (congrArg (fun count => count % 2) rightCount))
  have middle :=
    listDerivesFixedEndpointNormalizeOfRenderedInvariants head support parity
  exact leftDerivation.trans (middle.trans rightDerivation.symm)

end SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityComponentReplay
