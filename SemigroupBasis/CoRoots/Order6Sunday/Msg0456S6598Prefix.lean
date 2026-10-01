import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Erasure

/-! The extra S6598 observation is support before a globally simple nilpotent.
All list statements are unrestricted; finite prechecks are not hypotheses. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Prefix

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Erasure

theorem fold_blocked_noNil (valuation : α → Fin 6) (xs : List α) (initial : Summary)
    (none : xs.countP (fun x => isNil (valuation x)) = 0) :
    (xs.foldl (fun s x => push s (valuation x)) initial).blockedNil = initial.blockedNil := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      have tailZero : xs.countP (fun x => isNil (valuation x)) = 0 := by
        simp only [List.countP_cons] at none
        split at none <;> omega
      have nilFalse : isNil (valuation x) = false := by
        cases value : isNil (valuation x) with
        | false => rfl
        | true => simp [value] at none
      rw [List.foldl_cons, ih _ tailZero]
      simp [push, nilFalse]

theorem summary_blocked_noNil (valuation : α → Fin 6) (xs : List α)
    (none : xs.countP (fun x => isNil (valuation x)) = 0) :
    (summaryList valuation xs).blockedNil = false := by
  exact fold_blocked_noNil valuation xs emptySummary none

theorem blocked_unique_split (valuation : α → Fin 6)
    (before after : List α) (separator : α)
    (nilSeparator : isNil (valuation separator) = true)
    (unique : (before ++ separator :: after).countP (fun x => isNil (valuation x)) = 1) :
    (summaryList valuation (before ++ separator :: after)).blockedNil =
      before.any (fun x => valuation x == 5) := by
  have counts : before.countP (fun x => isNil (valuation x)) +
      (after.countP (fun x => isNil (valuation x)) + 1) = 1 := by
    simpa [List.countP_cons, nilSeparator] using unique
  have beforeZero : before.countP (fun x => isNil (valuation x)) = 0 := by omega
  have afterZero : after.countP (fun x => isNil (valuation x)) = 0 := by omega
  unfold summaryList
  rw [List.foldl_append, List.foldl_cons, fold_blocked_noNil valuation after _ afterZero]
  change ((summaryList valuation before).blockedNil ||
      ((summaryList valuation before).hasKill && isNil (valuation separator))) = _
  rw [summary_blocked_noNil valuation before beforeZero, summary_hasKill, nilSeparator]
  simp

theorem simple_of_unique_nil (valuation : Nat → Fin 6) (xs : List Nat) (separator : Nat)
    (member : separator ∈ xs) (nilSeparator : isNil (valuation separator) = true)
    (unique : xs.countP (fun x => isNil (valuation x)) = 1) : xs.count separator = 1 := by
  have positive := List.count_pos_iff.mpr member
  have bound : xs.count separator ≤ xs.countP (fun x => isNil (valuation x)) := by
    rw [← List.count_filter (l := xs) (p := fun x => isNil (valuation x)) nilSeparator,
      List.countP_eq_length_filter]
    exact List.count_le_length
  omega

theorem blocked_eq_prefix_any (valuation : Nat → Fin 6) (word : Word Nat) (separator : Nat)
    (simple : S5_254.GloballySimple word separator)
    (nilSeparator : isNil (valuation separator) = true)
    (unique : word.toList.countP (fun x => isNil (valuation x)) = 1) :
    (summaryList valuation word.toList).blockedNil =
      (S5_254.simplePrefixBefore separator word.toList).any (fun x => valuation x == 5) := by
  have member : separator ∈ word.toList := List.count_pos_iff.mp (by rw [simple]; decide)
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  rw [S5_254.simplePrefixBefore_eq_of_split simple before after shape]
  rw [shape] at unique ⊢
  exact blocked_unique_split valuation before after separator nilSeparator unique

theorem any_eq_of_sameSupport (left right : List α) (predicate : α → Bool)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : left.any predicate = right.any predicate := by
  cases hl : left.any predicate <;> cases hr : right.any predicate
  · rfl
  · obtain ⟨x, hx, px⟩ := List.any_eq_true.mp hr
    have yes : left.any predicate = true := List.any_eq_true.mpr ⟨x, (same x).mpr hx, px⟩
    simp [hl] at yes
  · obtain ⟨x, hx, px⟩ := List.any_eq_true.mp hl
    have yes : right.any predicate = true := List.any_eq_true.mpr ⟨x, (same x).mp hx, px⟩
    simp [hr] at yes
  · rfl

/-- A two-marker valuation reads membership in the prefix support. -/
def prefixProbe (separator tested : Nat) (x : Nat) : Fin 6 :=
  if x = separator then 1 else if x = tested then 5 else 3

theorem erase_prefixProbe (separator tested : Nat) :
    (fun x => eraseKill (prefixProbe separator tested x)) = S5_254.m18SimpleValuation separator := by
  funext x
  by_cases first : x = separator <;> by_cases second : x = tested <;>
    simp_all [prefixProbe, eraseKill, S5_254.m18SimpleValuation]
  all_goals first | rfl | (intro h; first | rfl |
    exact False.elim ((by decide : ¬ (5 : Fin 6).val < 5) h))

theorem prefixProbe_isNil (separator tested x : Nat) :
    isNil (prefixProbe separator tested x) = (x == separator) := by
  by_cases first : x = separator <;> by_cases second : x = tested <;>
    simp_all [prefixProbe, isNil]

theorem prefixProbe_isKill (separator tested x : Nat) (different : tested ≠ separator) :
    (prefixProbe separator tested x == 5) = (x == tested) := by
  by_cases first : x = separator <;> by_cases second : x = tested <;>
    simp_all [prefixProbe]

theorem prefixProbe_eval (word : Word Nat) (separator tested : Nat)
    (simple : S5_254.GloballySimple word separator) (different : tested ≠ separator) :
    table.semigroup.eval (prefixProbe separator tested) word =
      if tested ∈ S5_254.simplePrefixBefore separator word.toList then (0 : Fin 6) else (1 : Fin 6) := by
  have erased : S5_254.table.semigroup.eval
      (fun x => eraseKill (prefixProbe separator tested x)) word = (1 : Fin 5) := by
    rw [erase_prefixProbe, S5_254.m18SimpleEval, simple]
    rfl
  have unique : word.toList.countP (fun x => isNil (prefixProbe separator tested x)) = 1 := by
    have predicate : (fun x => isNil (prefixProbe separator tested x)) = (fun x => x == separator) :=
      funext (prefixProbe_isNil separator tested)
    rw [predicate]
    exact simple
  have nilSeparator : isNil (prefixProbe separator tested separator) = true := by
    simp [prefixProbe_isNil]
  rw [eval_eq_restore, erased, blocked_eq_prefix_any _ _ separator simple nilSeparator unique]
  have killPredicate : (fun x => prefixProbe separator tested x == 5) = (fun x => x == tested) :=
    funext (fun x => prefixProbe_isKill separator tested x different)
  rw [killPredicate]
  by_cases present : tested ∈ S5_254.simplePrefixBefore separator word.toList
  · have yes : (S5_254.simplePrefixBefore separator word.toList).any (fun x => x == tested) = true :=
      List.any_eq_true.mpr ⟨tested, present, by simp⟩
    simp [restore, yes, present]
  · have no : (S5_254.simplePrefixBefore separator word.toList).any (fun x => x == tested) = false := by
      cases h : (S5_254.simplePrefixBefore separator word.toList).any (fun x => x == tested) with
      | false => rfl
      | true =>
          obtain ⟨x, member, equal⟩ := List.any_eq_true.mp h
          have same : x = tested := by simpa using equal
          subst x
          exact False.elim (present member)
    simp [restore, no, present, embedValue]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Prefix
