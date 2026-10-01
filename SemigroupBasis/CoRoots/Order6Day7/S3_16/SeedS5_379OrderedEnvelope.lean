import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

/-!
# First-order-preserving envelopes for S3_16 × S5_379

Reuse the lower factor's support-connected suffix induction, but NOT its
interior permutation. Every crossing is absorbed in its original interior
position. The nine displayed target laws supply all steps, including every
empty-filler case. No model equality is used to manufacture a derivation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.OrderedEnvelope

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

private abbrev listWordOfCons := S5_107.listWordOfCons

private def instantiateThree (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerExpansion (x : Word Nat) :
    Derives basis (x ++ x) ((x ++ x) ++ x) := by
  have core : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x x x)

theorem derivesLeftDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ x) ++ y) ++ x) := by
  have core : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) :=
    (Derives.fromBasis (e := law01) (by simp [basis])).symm
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x y y)

theorem derivesRightDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have core : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x y y)

theorem derivesCrossingFinal (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y) (((x ++ y) ++ y) ++ x) := by
  have core : Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x y y)

theorem derivesThirdDeletion (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x) (((x ++ y) ++ z) ++ x) := by
  have core : Derives basis (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [1, 2, 0]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x y z)

theorem derivesCrossingRight (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ y) ((((x ++ y) ++ y) ++ z) ++ x) := by
  have core : Derives basis (Word.mk 0 [1, 0, 2, 1]) (Word.mk 0 [1, 1, 2, 0]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst core (instantiateThree x y z)

theorem derivesCrossingLeftFiller (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ z) ++ x) ++ y) ((((x ++ y) ++ y) ++ z) ++ x) := by
  have first : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 0, 2, 1]) :=
    (Derives.fromBasis (e := law06) (by simp [basis])).symm
  have second : Derives basis (Word.mk 0 [1, 0, 2, 1]) (Word.mk 0 [1, 1, 2, 0]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
    Derives.subst (first.trans second) (instantiateThree x y z)

theorem derivesCrossingBothFillers (x y z u : Word Nat) :
    Derives basis (((((x ++ y) ++ z) ++ x) ++ u) ++ y)
      (((((x ++ y) ++ y) ++ z) ++ u) ++ x) := by
  have first := Derives.appendRight (derivesThirdDeletion x y z).symm (u ++ y)
  have second := derivesCrossingRight x y ((z ++ x) ++ u)
  have third := derivesThirdDeletion x ((y ++ y) ++ z) u
  simp only [Word.append_assoc] at first second third ⊢
  exact first.trans (second.trans third)

/-- Actual third-occurrence deletion, with arbitrary possibly empty gaps. -/
theorem listDeleteMiddle (letter : Nat) (left right : List Nat) :
    ListDerives ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              (derivesLeftDuplication (Word.singleton letter)
                (listWordOfCons rightHead rightTail)).symm
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              (derivesRightDuplication (Word.singleton letter)
                (listWordOfCons leftHead leftTail)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              derivesThirdDeletion (Word.singleton letter)
                (listWordOfCons leftHead leftTail) (listWordOfCons rightHead rightTail)

/-- Absorb a crossing following the initial two letters, retaining two
copies of the crossing letter and preserving the entire first order. -/
theorem listCrossing (endpoint crossing : Nat) (middle before : List Nat) :
    ListDerives (endpoint :: crossing :: middle ++ endpoint :: before ++ [crossing])
      (endpoint :: crossing :: crossing :: middle ++ before ++ [endpoint]) := by
  cases middle with
  | nil =>
      cases before with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              derivesCrossingFinal (Word.singleton endpoint) (Word.singleton crossing)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              derivesCrossingRight (Word.singleton endpoint) (Word.singleton crossing)
                (listWordOfCons beforeHead beforeTail)
  | cons middleHead middleTail =>
      cases before with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              derivesCrossingLeftFiller (Word.singleton endpoint) (Word.singleton crossing)
                (listWordOfCons middleHead middleTail)
      | cons beforeHead beforeTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, S5_107.listWordOfCons, Word.singleton, Word.append, Word.append_assoc, List.append_assoc] using
              derivesCrossingBothFillers (Word.singleton endpoint) (Word.singleton crossing)
                (listWordOfCons middleHead middleTail) (listWordOfCons beforeHead beforeTail)

/-- Keep the original interior prefix fixed. Repeated endpoints provide the
needed contexts; NO prefix is moved across the crossing letter. -/
theorem listCrossingInOrder (endpoint crossing : Nat) (pre middle before : List Nat) :
    ListDerives
      (endpoint :: pre ++ crossing :: middle ++ endpoint :: before ++ [crossing])
      (endpoint :: pre ++ crossing :: crossing :: middle ++ before ++ [endpoint]) := by
  have first := (listDeleteMiddle endpoint pre (crossing :: middle)).symm.append (before ++ [crossing])
  have second := (listCrossing endpoint crossing middle before).prepend (endpoint :: pre)
  have third := listDeleteMiddle endpoint pre (crossing :: crossing :: middle ++ before)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at first second third ⊢
  exact first.trans (second.trans third)

/-- An actual envelope derivation can be lifted past ANY fixed interior
prefix, using endpoint insertion and removal, not interior permutation. -/
theorem listInteriorPrefix (endpoint : Nat) (pre suffix : List Nat)
    {left right : List Nat}
    (derivation : ListDerives (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix)) :
    ListDerives (endpoint :: pre ++ left ++ endpoint :: suffix)
      (endpoint :: pre ++ right ++ endpoint :: suffix) := by
  have first := (listDeleteMiddle endpoint pre left).symm.append suffix
  have second := derivation.prepend (endpoint :: pre)
  have third := (listDeleteMiddle endpoint pre right).append suffix
  simp only [List.append_assoc, List.cons_append, List.nil_append] at first second third ⊢
  exact first.trans (second.trans third)

/-- Gather a second copy of the first interior letter without moving its
first occurrence. The later interior letters keep their order. -/
theorem listGather (endpoint letter : Nat) (middle after : List Nat) :
    ListDerives (endpoint :: letter :: middle ++ letter :: after ++ [endpoint])
      (endpoint :: letter :: letter :: middle ++ after ++ [endpoint]) := by
  have first := (listDeleteMiddle endpoint (letter :: middle) (letter :: after)).symm
  have second := (listCrossing endpoint letter middle []).append (after ++ [endpoint])
  have third := listDeleteMiddle endpoint (letter :: letter :: middle) after
  simp only [List.append_assoc, List.cons_append, List.nil_append] at first second third ⊢
  exact first.trans (second.trans third)

theorem listGatherAfterPrefix (endpoint letter : Nat) (pre middle after : List Nat) :
    ListDerives (endpoint :: pre ++ letter :: middle ++ letter :: after ++ [endpoint])
      (endpoint :: pre ++ letter :: letter :: middle ++ after ++ [endpoint]) := by
  simpa [List.append_assoc] using
    listInteriorPrefix endpoint pre [] (listGather endpoint letter middle after)

/-- The new suffix state depends only on support. The interior prefix is
retained in place, unlike the lower factor's permutation-based plan. -/
theorem peelInteriorInOrder
    {endpoint letter : Nat} {interior suffix pre middle before after : List Nat}
    (state : ConnectedComponentEnvelopeState endpoint interior suffix)
    (interiorShape : interior = pre ++ letter :: middle)
    (suffixShape : suffix = before ++ letter :: after) :
    ConnectedComponentEnvelopeState endpoint
      (pre ++ letter :: letter :: middle ++ before) after := by
  refine ⟨?_⟩
  intro left right afterShape rightNonempty
  have oldShape : suffix = (before ++ letter :: left) ++ right := by
    rw [suffixShape, afterShape]
    simp [List.append_assoc]
  obtain ⟨value, oldMember, rightMember⟩ :=
    state.linked (before ++ letter :: left) right oldShape rightNonempty
  refine ⟨value, ?_, rightMember⟩
  simpa [interiorShape, List.mem_append, or_assoc, or_left_comm, or_comm] using oldMember

inductive OrderedPlan (endpoint : Nat) : List Nat → List Nat → List Nat → Prop
  | done (interior : List Nat) : OrderedPlan endpoint interior [] interior
  | interior {interior suffix pre middle before after finalInterior : List Nat} {letter : Nat} :
      interior = pre ++ letter :: middle →
      suffix = before ++ letter :: after →
      OrderedPlan endpoint (pre ++ letter :: letter :: middle ++ before) after finalInterior →
      OrderedPlan endpoint interior suffix finalInterior
  | endpoint {interior suffix before after finalInterior : List Nat} :
      suffix = before ++ endpoint :: after →
      OrderedPlan endpoint (interior ++ before) after finalInterior →
      OrderedPlan endpoint interior suffix finalInterior

theorem exists_orderedPlan {endpoint : Nat} :
    ∀ (interior suffix : List Nat), ConnectedComponentEnvelopeState endpoint interior suffix →
      ∃ finalInterior, OrderedPlan endpoint interior suffix finalInterior := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, .done interior⟩
  · obtain ⟨letter, endpointOrInterior, inSuffix⟩ := state.exists_crossing suffixEmpty
    obtain ⟨before, after, suffixShape⟩ := List.append_of_mem inSuffix
    rcases endpointOrInterior with rfl | inInterior
    · obtain ⟨finalInterior, plan⟩ :=
        exists_orderedPlan (interior ++ before) after (state.peelEndpoint suffixShape)
      exact ⟨finalInterior, .endpoint suffixShape plan⟩
    · obtain ⟨pre, middle, interiorShape⟩ := List.append_of_mem inInterior
      obtain ⟨finalInterior, plan⟩ :=
        exists_orderedPlan (pre ++ letter :: letter :: middle ++ before) after
          (peelInteriorInOrder state interiorShape suffixShape)
      exact ⟨finalInterior, .interior interiorShape suffixShape plan⟩
termination_by interior suffix _ => suffix.length
decreasing_by all_goals exact connectedComponent_peel_suffix_length_lt suffixShape

abbrev envelopeRender := connectedComponentEnvelopeRender

theorem OrderedPlan.replay {endpoint : Nat} {interior suffix finalInterior : List Nat}
    (plan : OrderedPlan endpoint interior suffix finalInterior) :
    ListDerives (envelopeRender endpoint interior suffix) (envelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current => exact S5_107.ListDerives.refl _
  | @interior interior suffix pre middle before after finalInterior letter
      interiorShape suffixShape _ induction =>
      subst interior
      subst suffix
      have crossing := (listCrossingInOrder endpoint letter pre middle before).append after
      have aligned :
          ListDerives (envelopeRender endpoint (pre ++ letter :: middle) (before ++ letter :: after))
            (envelopeRender endpoint (pre ++ letter :: letter :: middle ++ before) after) := by
        simpa [envelopeRender, connectedComponentEnvelopeRender, List.append_assoc] using crossing
      exact aligned.trans induction
  | @endpoint interior suffix before after finalInterior suffixShape _ induction =>
      subst suffix
      have deletion := (listDeleteMiddle endpoint interior before).append after
      have aligned :
          ListDerives (envelopeRender endpoint interior (before ++ endpoint :: after))
            (envelopeRender endpoint (interior ++ before) after) := by
        simpa [envelopeRender, connectedComponentEnvelopeRender, List.append_assoc] using deletion
      exact aligned.trans induction

/-- Every nontrivial connected component gains a genuine envelope at its
ORIGINAL FIRST letter, without changing first order or capped multiplicity. -/
theorem existsConnectedEnvelope (head next : Nat) (rest : List Nat)
    (connected : ConnectedComponentSupportConnected (head :: next :: rest)) :
    ∃ interior, ListDerives (head :: next :: rest) (head :: interior ++ [head]) := by
  obtain ⟨initialInterior, suffix, initialShape, state⟩ :=
    connectedComponent_exists_initial_envelope connected (by simp)
  obtain ⟨finalInterior, plan⟩ := exists_orderedPlan initialInterior suffix state
  refine ⟨finalInterior, ?_⟩
  rw [initialShape]
  simpa [envelopeRender, connectedComponentEnvelopeRender, List.append_assoc] using plan.replay

theorem existsConnectedEnvelope_preserves (head next : Nat) (rest : List Nat)
    (connected : ConnectedComponentSupportConnected (head :: next :: rest)) :
    ∃ interior,
      ListDerives (head :: next :: rest) (head :: interior ++ [head]) ∧
      firstOccurrenceSequence (head :: next :: rest) = firstOccurrenceSequence (head :: interior ++ [head]) ∧
      ∀ tested, min ((head :: next :: rest).count tested) 2 = min ((head :: interior ++ [head]).count tested) 2 := by
  obtain ⟨interior, derivation⟩ := existsConnectedEnvelope head next rest connected
  exact ⟨interior, derivation, listDerives_firstOrder derivation, listDerives_cappedCounts derivation⟩

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.OrderedEnvelope
