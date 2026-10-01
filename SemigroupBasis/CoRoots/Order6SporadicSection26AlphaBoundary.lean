import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaReduction
import SemigroupBasis.CoRoots.Order6SporadicSection26Observations

/-! Exact last-block boundary observations. Removing a shared suffix whose
first letter is fresh exposes the preceding final letter via the proved F7
predecessor detector. No cancellation of semigroup values is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

theorem predecessorScan_boundary (separator previous : Nat) (before after : List Nat)
    (missing : separator ∉ before) :
    predecessorScan separator previous (before ++ separator :: after) =
      before.foldl (fun _ x => x) previous := by
  induction before generalizing previous with
  | nil => simp [predecessorScan]
  | cons head tail ih =>
      have different : head ≠ separator := by
        intro same
        subst head
        exact missing (by simp)
      have tailMissing : separator ∉ tail := by
        intro present
        exact missing (by simp [present])
      simp only [List.cons_append, predecessorScan, if_neg different, List.foldl_cons]
      exact ih head tailMissing

theorem predecessorList_boundary (separator : Nat) (before after : List Nat)
    (missing : separator ∉ before) :
    predecessorList separator (before ++ separator :: after) = lastLetter before := by
  cases before with
  | nil => simp [predecessorList, lastLetter]
  | cons head tail =>
      have different : head ≠ separator := by
        intro same
        subst head
        exact missing (by simp)
      have tailMissing : separator ∉ tail := by
        intro present
        exact missing (by simp [present])
      simp only [List.cons_append, predecessorList, if_neg different, lastLetter]
      rw [predecessorScan_boundary separator head tail after tailMissing]

theorem lastLetter_append_cons (before : List Nat) (head : Nat) (tail : List Nat) :
    lastLetter (before ++ head :: tail) = lastLetter (head :: tail) := by
  cases before with
  | nil => rfl
  | cons x xs => simp only [List.cons_append, lastLetter, List.foldl_append, List.foldl_cons]

theorem fold_last_replicate (head extra : Nat) :
    (List.replicate extra head).foldl (fun _ x => x) head = head := by
  induction extra with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.foldl_cons] using ih

theorem lastLetter_headRun (head extra : Nat) : lastLetter (headRun head extra) = some head := by
  simp only [headRun, lastLetter, fold_last_replicate]

theorem tail_eq_of_getD (head : Nat) (left right : Option Nat)
    (leftMissing : head ∉ left.toList) (rightMissing : head ∉ right.toList)
    (same : left.getD head = right.getD head) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some y =>
          have equal : head = y := same
          exact False.elim (rightMissing (by simp [equal]))
  | some x =>
      cases right with
      | none =>
          have equal : x = head := same
          exact False.elim (leftMissing (by simp [equal]))
      | some y => exact congrArg some same

namespace AlphaForm

theorem lastLetter_render_snoc (init : AlphaForm) (head extra : Nat) (tail : Option Nat) :
    lastLetter (snoc init head extra tail).render = some (tail.getD head) := by
  cases tail with
  | none =>
      change lastLetter (init.render ++ (headRun head extra ++ [])) = some head
      rw [List.append_nil]
      exact (lastLetter_append_cons init.render head (List.replicate extra head)).trans
        (lastLetter_headRun head extra)
  | some x =>
      change lastLetter (init.render ++ (headRun head extra ++ [x])) = some x
      rw [← List.append_assoc]
      exact lastLetter_append_cons (init.render ++ headRun head extra) x []

theorem count_snoc_head (init : AlphaForm) (head extra : Nat) (tail : Option Nat)
    (after : List Nat) (valid : (snoc init head extra tail).Valid)
    (missing : head ∉ after) : ((snoc init head extra tail).render ++ after).count head = extra + 1 := by
  rcases valid with ⟨initValid, fresh, earlier⟩
  have initMissing : head ∉ init.render := by
    intro present
    exact fresh ((mem_render_iff init head initValid).mp present)
  have tailMissing : head ∉ tail.toList := fun present => fresh (earlier head present)
  have initZero := List.count_eq_zero_of_not_mem initMissing
  have tailZero := List.count_eq_zero_of_not_mem tailMissing
  have afterZero := List.count_eq_zero_of_not_mem missing
  simp [render, headRun, List.count_append, initZero, tailZero, afterZero]

def AfterBoundary (heads after : List Nat) : Prop :=
  after = [] ∨ ∃ separator rest, after = separator :: rest ∧ separator ∉ heads

theorem last_eq_of_boundary (left right : AlphaForm) (after : List Nat)
    (leftValid : left.Valid) (rightValid : right.Valid) (sameHeads : left.heads = right.heads)
    (same : Observations (left.render ++ after) (right.render ++ after))
    (boundary : AfterBoundary left.heads after) : lastLetter left.render = lastLetter right.render := by
  rcases boundary with empty | ⟨separator, rest, shape, missing⟩
  · simpa only [empty, List.append_nil] using same.last
  · have leftMissing : separator ∉ left.render := by
      intro present
      exact missing ((mem_render_iff left separator leftValid).mp present)
    have rightMissing : separator ∉ right.render := by
      intro present
      apply missing
      rw [sameHeads]
      exact (mem_render_iff right separator rightValid).mp present
    have observation := same.predecessor separator
    rw [shape, predecessorList_boundary separator left.render rest leftMissing,
      predecessorList_boundary separator right.render rest rightMissing] at observation
    exact observation

end AlphaForm

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.predecessorScan_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.predecessorList_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.lastLetter_append_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.fold_last_replicate
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.lastLetter_headRun
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.tail_eq_of_getD
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.lastLetter_render_snoc
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.count_snoc_head
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.last_eq_of_boundary
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
