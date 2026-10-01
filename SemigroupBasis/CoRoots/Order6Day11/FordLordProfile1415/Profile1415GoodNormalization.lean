import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415Bridges
import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415GoodBlocks

/-! Unrestricted good-word reach through certified connected components. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.GoodWords

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14
  (existsClosedEndpointAdjustedNormal componentParityBlock)

theorem component_derives_good (component : List Nat)
    (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ∃ target, ListDerives basis component target ∧ Good target := by
  cases component with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      by_cases tailEmpty : tail = []
      · subst tail
        exact ⟨[head], ListDerives.refl _, good_singleton head⟩
      · obtain ⟨interior, normalized⟩ :=
          existsClosedEndpointAdjustedNormal connected tailEmpty
        have normalizedB := replayCondition14List normalized
        let payload : List Nat :=
          (parityInitialNormalList interior).filter (fun letter => decide (letter ≠ head))
        have closed : ∃ middle,
            ListDerives basis (head :: tail) (head :: middle ++ [head]) := by
          by_cases even : (head :: tail).count head % 2 = 0
          · refine ⟨payload, ?_⟩
            simpa only [componentParityBlock, if_pos rfl, if_pos even,
              List.cons_append, List.nil_append, payload] using normalizedB
          · refine ⟨head :: payload, ?_⟩
            simpa only [componentParityBlock, if_pos rfl, if_neg even,
              List.cons_append, List.nil_append, payload] using normalizedB
        obtain ⟨middle, closedDerivation⟩ := closed
        obtain ⟨target, collapse, repeated⟩ := collapse_closed head middle
        exact ⟨target, closedDerivation.trans collapse, good_of_repeated repeated⟩

theorem components_derive_good (components : List (List Nat)) :
    (∀ component ∈ components, component ≠ []) →
    (∀ component ∈ components, ConnectedComponentSupportConnected component) →
    components.Pairwise ConnectedComponentSupportsDisjoint →
    ∃ target, ListDerives basis components.flatten target ∧ Good target := by
  induction components with
  | nil =>
      intro _ _ _
      exact ⟨[], .empty, good_nil⟩
  | cons first rest ih =>
      intro nonempty connected pairwise
      have splitPairwise := List.pairwise_cons.mp pairwise
      obtain ⟨firstTarget, firstDerivation, firstGood⟩ :=
        component_derives_good first (nonempty first (by simp))
          (connected first (by simp))
      obtain ⟨restTarget, restDerivation, restGood⟩ := ih
        (fun component member => nonempty component (List.mem_cons_of_mem first member))
        (fun component member => connected component (List.mem_cons_of_mem first member))
        splitPairwise.2
      have disjoint : UniqueSeparatorFourSupportsDisjoint firstTarget restTarget := by
        intro selected inFirstTarget inRestTarget
        have inFirst : selected ∈ first :=
          (support_of_listDerives firstDerivation selected).mpr inFirstTarget
        have inRest : selected ∈ rest.flatten :=
          (support_of_listDerives restDerivation selected).mpr inRestTarget
        obtain ⟨component, inComponents, inComponent⟩ := List.mem_flatten.mp inRest
        exact splitPairwise.1 component inComponents selected inFirst inComponent
      refine ⟨firstTarget ++ restTarget, ?_, good_append firstGood restGood disjoint⟩
      have joined := (firstDerivation.append rest.flatten).trans
        (restDerivation.prepend firstTarget)
      simpa only [List.flatten_cons] using joined

theorem list_derives_good (letters : List Nat) :
    ∃ target, ListDerives basis letters target ∧ Good target := by
  have decomposition := connectedComponentDecomposeList_spec letters
  obtain ⟨target, derived, good⟩ := components_derive_good _
    decomposition.nonempty decomposition.supportConnected decomposition.pairwiseDisjoint
  rw [decomposition.flatten_eq] at derived
  exact ⟨target, derived, good⟩

/-- No word-length, rank, renderer, or factor-validity premise is required. -/
theorem word_derives_good (word : Word Nat) :
    ∃ target : Word Nat, Derives basis word target ∧ Good target.toList := by
  cases word with
  | mk head tail =>
      obtain ⟨target, derived, good⟩ := list_derives_good (head :: tail)
      obtain ⟨targetHead, targetTail, rfl, wordDerived⟩ := derived.from_cons
      exact ⟨Word.mk targetHead targetTail, wordDerived, good⟩

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.GoodWords
