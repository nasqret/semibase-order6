import SemigroupBasis.CoRoots.Order6SporadicSection18RawChainBridge

/-! Maximal runs for an arbitrary FIXED letter predicate. In the C7 application
the predicate is global nonsimplicity in the original whole word; recursion
never reclassifies a letter using only a suffix. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def GoodRawSlot (nonSimple : Nat → Prop) (slot : Slot) : Prop :=
  slot.block ≠ [] ∧ (∀ x ∈ slot.block, nonSimple x) ∧ ∀ x ∈ slot.gap, ¬ nonSimple x

def RawRuns (nonSimple : Nat → Prop) (first : Slot) (rest : List Slot) : Prop :=
  GoodRawSlot nonSimple first ∧ ∀ slot ∈ rest, GoodRawSlot nonSimple slot ∧ slot.gap ≠ []

def EndsWithN (nonSimple : Nat → Prop) (letters : List Nat) : Prop :=
  ∃ before last, letters = before ++ [last] ∧ nonSimple last

theorem EndsWithN.nonempty {nonSimple : Nat → Prop} {letters : List Nat}
    (ended : EndsWithN nonSimple letters) : letters ≠ [] := by
  intro empty
  obtain ⟨before, last, shape, _⟩ := ended
  have lengths := congrArg List.length shape
  rw [empty] at lengths
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

theorem EndsWithN.tail {nonSimple : Nat → Prop} {head : Nat} {tail : List Nat}
    (ended : EndsWithN nonSimple (head :: tail)) (nonempty : tail ≠ []) : EndsWithN nonSimple tail := by
  obtain ⟨before, last, shape, good⟩ := ended
  cases before with
  | nil =>
      have boundary : head :: tail = last :: [] := shape
      exact False.elim (nonempty (List.cons.inj boundary).2)
  | cons first rest =>
      have boundary : head :: tail = first :: (rest ++ [last]) := shape
      exact ⟨rest, last, (List.cons.inj boundary).2, good⟩

theorem EndsWithN.singleton {nonSimple : Nat → Prop} {head : Nat}
    (ended : EndsWithN nonSimple [head]) : nonSimple head := by
  obtain ⟨before, last, shape, good⟩ := ended
  cases before with
  | nil =>
      have boundary : head :: [] = last :: [] := shape
      exact (List.cons.inj boundary).1.symm ▸ good
  | cons first rest =>
      have boundary : head :: [] = first :: (rest ++ [last]) := shape
      have lengths := congrArg List.length (List.cons.inj boundary).2
      simp only [List.length_nil, List.length_append, List.length_cons] at lengths
      omega

private theorem singleton_good (nonSimple : Nat → Prop) (x : Nat) (good : nonSimple x) :
    GoodRawSlot nonSimple ⟨[], [x]⟩ := by
  simp [GoodRawSlot, good]

theorem RawRuns.slotGood {nonSimple : Nat → Prop} {first : Slot} {rest : List Slot}
    (runs : RawRuns nonSimple first rest) (slot : Slot) (member : slot ∈ first :: rest) :
    GoodRawSlot nonSimple slot := by
  rcases List.mem_cons.mp member with equal | member
  · subst slot
    exact runs.1
  · exact (runs.2 slot member).1

/-- Ending with a selected letter is sufficient for a nonempty alternating
run decomposition. Only the first gap is permitted to be empty. -/
theorem exists_rawRuns (nonSimple : Nat → Prop) [DecidablePred nonSimple] (letters : List Nat) :
    EndsWithN nonSimple letters →
      ∃ first rest, rawRender (first :: rest) = letters ∧ RawRuns nonSimple first rest := by
  induction letters with
  | nil =>
      intro ended
      exact False.elim (ended.nonempty rfl)
  | cons x xs ih =>
      intro ended
      cases xs with
      | nil =>
          refine ⟨⟨[], [x]⟩, [], rfl, singleton_good nonSimple x ended.singleton, ?_⟩
          intro slot impossible
          cases impossible
      | cons y ys =>
          obtain ⟨first, rest, shape, runs⟩ := ih (ended.tail (by simp))
          have firstGood := runs.1
          have restGood := runs.2
          by_cases selected : nonSimple x
          · by_cases gapEmpty : first.gap = []
            · refine ⟨⟨[], x :: first.block⟩, rest, ?_, ?_⟩
              · simpa only [rawRender, gapEmpty, List.nil_append, List.cons_append] using
                  congrArg (List.cons x) shape
              · refine ⟨⟨by simp, ?_, ?_⟩, restGood⟩
                · intro z member
                  rcases List.mem_cons.mp member with equal | member
                  · subst z
                    exact selected
                  · exact firstGood.2.1 z member
                · intro z impossible
                  cases impossible
            · refine ⟨⟨[], [x]⟩, first :: rest, ?_, singleton_good nonSimple x selected, ?_⟩
              · simpa only [rawRender, List.nil_append, List.cons_append] using
                  congrArg (List.cons x) shape
              · intro slot member
                rcases List.mem_cons.mp member with equal | member
                · subst slot
                  exact ⟨firstGood, gapEmpty⟩
                · exact restGood slot member
          · refine ⟨⟨x :: first.gap, first.block⟩, rest, ?_, ?_⟩
            · simpa only [rawRender, List.cons_append] using congrArg (List.cons x) shape
            · refine ⟨⟨firstGood.1, firstGood.2.1, ?_⟩, restGood⟩
              intro z member
              rcases List.mem_cons.mp member with equal | member
              · subst z
                exact selected
              · exact firstGood.2.2 z member

theorem RawRuns.first_gap_empty {nonSimple : Nat → Prop} {first : Slot} {rest : List Slot}
    (runs : RawRuns nonSimple first rest)
    (starts : ∃ head tail, rawRender (first :: rest) = head :: tail ∧ nonSimple head) : first.gap = [] := by
  obtain ⟨head, tail, shape, good⟩ := starts
  cases gapEq : first.gap with
  | nil => rfl
  | cons x xs =>
      have notSelected := runs.1.2.2 x (by simp [gapEq])
      have boundary : x :: (xs ++ first.block ++ rawRender rest) = head :: tail := by
        simpa only [rawRender, gapEq, List.cons_append] using shape
      exact False.elim (notSelected ((List.cons.inj boundary).1.symm ▸ good))

theorem RawRuns.tail_nonempty {nonSimple : Nat → Prop} {first : Slot} {rest : List Slot}
    (runs : RawRuns nonSimple first rest) (firstEmpty : first.gap = [])
    (hasOther : ∃ x, x ∈ rawRender (first :: rest) ∧ ¬ nonSimple x) : rest ≠ [] := by
  intro empty
  subst rest
  obtain ⟨x, member, notSelected⟩ := hasOther
  have blockMember : x ∈ first.block := by
    simpa only [rawRender, firstEmpty, List.nil_append, List.append_nil] using member
  exact notSelected (runs.1.2.1 x blockMember)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.RawRuns.slotGood
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.exists_rawRuns
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.RawRuns.first_gap_empty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.RawRuns.tail_nonempty

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
