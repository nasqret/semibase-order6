import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaBoundary
import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaInitials

/-! Unrestricted canonical uniqueness, peeling one common last block.
The fresh-suffix boundary exposes the tail; capped counts expose a doubled
head unless a later occurrence forces that head exponent to one. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

theorem append_one_injective (left right : List Nat) (head other : Nat)
    (same : left ++ [head] = right ++ [other]) : left = right ∧ head = other := by
  have reversed := congrArg List.reverse same
  have consEqual : head :: left.reverse = other :: right.reverse := by simpa using reversed
  have parts := List.cons.inj consEqual
  have original := congrArg List.reverse parts.2
  exact ⟨by simpa using original, parts.1⟩

namespace AlphaForm

theorem canonical_unique (left right : AlphaForm) (after : List Nat)
    (leftValid : left.Valid) (rightValid : right.Valid)
    (leftTight : left.TightAfter after) (rightTight : right.TightAfter after)
    (sameHeads : left.heads = right.heads)
    (same : Observations (left.render ++ after) (right.render ++ after))
    (boundary : AfterBoundary left.heads after) : left = right := by
  induction left generalizing right after with
  | nil =>
      cases right with
      | nil => rfl
      | snoc init head extra tail => simp [heads] at sameHeads
  | snoc init head extra tail ih =>
      cases right with
      | nil => simp [heads] at sameHeads
      | snoc other otherHead otherExtra otherTail =>
          have parts := append_one_injective init.heads other.heads head otherHead sameHeads
          have headEqual := parts.2
          subst otherHead
          have initHeads := parts.1
          have lastEqual := last_eq_of_boundary (snoc init head extra tail)
            (snoc other head otherExtra otherTail) after leftValid rightValid sameHeads same boundary
          rw [lastLetter_render_snoc, lastLetter_render_snoc] at lastEqual
          have labelEqual : tail.getD head = otherTail.getD head := Option.some.inj lastEqual
          rcases leftValid with ⟨initValid, fresh, earlier⟩
          rcases rightValid with ⟨otherValid, otherFresh, otherEarlier⟩
          have tailMissing : head ∉ tail.toList := fun present => fresh (earlier head present)
          have otherTailMissing : head ∉ otherTail.toList :=
            fun present => otherFresh (otherEarlier head present)
          have tailEqual := tail_eq_of_getD head tail otherTail tailMissing otherTailMissing labelEqual
          subst otherTail
          rcases leftTight with ⟨bound, laterMissing, initTight⟩
          rcases rightTight with ⟨otherBound, otherLaterMissing, otherTight⟩
          have extraEqual : extra = otherExtra := by
            by_cases later : head ∈ after
            · have notOne : extra ≠ 1 := by
                intro one
                exact laterMissing one (by simp [later])
              have otherNotOne : otherExtra ≠ 1 := by
                intro one
                exact otherLaterMissing one (by simp [later])
              omega
            · have counts := same.capped head
              rw [count_snoc_head init head extra tail after ⟨initValid, fresh, earlier⟩ later,
                count_snoc_head other head otherExtra tail after
                  ⟨otherValid, otherFresh, otherEarlier⟩ later] at counts
              omega
          subst otherExtra
          let suffix := (headRun head extra ++ tail.toList) ++ after
          have earlierSame : Observations (init.render ++ suffix) (other.render ++ suffix) := by
            simpa only [render, suffix, List.append_assoc] using same
          have earlierBoundary : AfterBoundary init.heads suffix := by
            refine Or.inr ⟨head, (List.replicate extra head ++ tail.toList) ++ after, ?_, fresh⟩
            simp only [suffix, headRun, List.cons_append]
          have initEqual := ih other suffix initValid otherValid initTight otherTight
            initHeads earlierSame earlierBoundary
          exact congrArg (fun form => snoc form head extra tail) initEqual

end AlphaForm

theorem normalizeCanonical_eq_of_observations (left right : List Nat)
    (same : Observations left right) : normalizeCanonical left = normalizeCanonical right := by
  have sameHeads : (normalizeCanonical left).heads = (normalizeCanonical right).heads :=
    (normalizeCanonical_heads left).trans (same.ini.trans (normalizeCanonical_heads right).symm)
  have normalized :=
    ((observations_of_listDerives (derives_normalizeCanonical left)).symm.trans same).trans
      (observations_of_listDerives (derives_normalizeCanonical right))
  apply AlphaForm.canonical_unique (normalizeCanonical left) (normalizeCanonical right) []
    (normalizeCanonical_valid left) (normalizeCanonical_valid right)
    (normalizeCanonical_tight left) (normalizeCanonical_tight right) sameHeads
  · simpa only [List.append_nil] using normalized
  · exact Or.inl rfl

/-- Genuine unrestricted completeness for the exact nine-law F7 presentation. -/
theorem canonical_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have same := normalizeCanonical_eq_of_observations identity.lhs.toList identity.rhs.toList
    (valid_observations identity valid)
  have left := derives_normalizeCanonical identity.lhs.toList
  have right := derives_normalizeCanonical identity.rhs.toList
  rw [same] at left
  exact S5_107.ListDerives.toWord (left.trans right.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.append_one_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.canonical_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeCanonical_eq_of_observations
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.canonical_complete
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
